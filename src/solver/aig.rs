use std::sync::atomic::{AtomicI64, Ordering};

/// AIG (And-Inverter Graph) node representing a boolean function
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AigNode {
    id: i64,
    negated: bool,
}

impl AigNode {
    pub const TRUE_ID: i64 = 1;
    
    pub fn new(id: i64, negated: bool) -> Self {
        Self { id, negated }
    }
    
    pub fn is_true(&self) -> bool {
        self.id == Self::TRUE_ID && !self.negated
    }
    
    pub fn is_false(&self) -> bool {
        self.id == Self::TRUE_ID && self.negated
    }
    
    pub fn is_const(&self) -> bool {
        !self.is_and() && !self.is_true() && !self.is_false()
    }
    
    pub fn is_and(&self) -> bool {
        self.id > Self::TRUE_ID
    }
    
    pub fn is_negated(&self) -> bool {
        self.negated
    }
    
    pub fn get_id(&self) -> i64 {
        if self.negated { -self.id } else { self.id }
    }
    
    pub fn get_raw_id(&self) -> i64 {
        self.id
    }
}

/// AIG node data stored in the manager
#[derive(Debug)]
pub struct AigNodeData {
    id: i64,
    refs: u32,
    parents: u32,
    left: Option<AigNode>,
    right: Option<AigNode>,
}

impl AigNodeData {
    pub fn new(id: i64) -> Self {
        Self {
            id,
            refs: 0,
            parents: 0,
            left: None,
            right: None,
        }
    }
    
    pub fn new_and(id: i64, left: AigNode, right: AigNode) -> Self {
        Self {
            id,
            refs: 0,
            parents: 0,
            left: Some(left),
            right: Some(right),
        }
    }
    
    pub fn inc_refs(&mut self) {
        self.refs += 1;
    }
    
    pub fn dec_refs(&mut self) -> bool {
        if self.refs > 0 {
            self.refs -= 1;
        }
        self.refs == 0
    }
    
    pub fn inc_parents(&mut self) {
        self.parents += 1;
    }
    
    pub fn dec_parents(&mut self) {
        if self.parents > 0 {
            self.parents -= 1;
        }
    }
}

/// Statistics for AIG operations
#[derive(Debug, Default)]
pub struct AigStatistics {
    pub num_ands: u64,
    pub num_consts: u64,
    pub num_shared: u64,
}

/// Unique table for hash consing of AIG nodes
pub struct AigUniqueTable {
    buckets: Vec<Vec<usize>>,
    num_elements: usize,
}

impl AigUniqueTable {
    pub fn new() -> Self {
        Self {
            buckets: vec![Vec::new(); 1024],
            num_elements: 0,
        }
    }
    
    fn hash(&self, left: &AigNode, right: &AigNode) -> usize {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        left.get_id().hash(&mut hasher);
        right.get_id().hash(&mut hasher);
        hasher.finish() as usize % self.buckets.len()
    }
    
    pub fn find_or_insert(&mut self, left: &AigNode, right: &AigNode, node_data: &mut Vec<AigNodeData>) -> Option<usize> {
        let bucket_idx = self.hash(left, right);
        
        for &node_idx in &self.buckets[bucket_idx] {
            if let Some(node_data) = node_data.get(node_idx) {
                if let (Some(ref l), Some(ref r)) = (&node_data.left, &node_data.right) {
                    if l == left && r == right {
                        return Some(node_idx);
                    }
                }
            }
        }
        
        None
    }
    
    pub fn insert(&mut self, left: &AigNode, right: &AigNode, node_idx: usize) {
        let bucket_idx = self.hash(left, right);
        self.buckets[bucket_idx].push(node_idx);
        self.num_elements += 1;
    }
    
    fn resize(&mut self) {
        // Simple resize implementation - in practice would be more sophisticated
        let new_size = self.buckets.len() * 2;
        self.buckets = vec![Vec::new(); new_size];
        self.num_elements = 0;
        // Would need to rehash all elements in a real implementation
    }
}

/// Manager for AIG nodes with hash consing and reference counting
pub struct AigManager {
    node_data: Vec<AigNodeData>,
    unique_table: AigUniqueTable,
    id_counter: AtomicI64,
    true_node: AigNode,
    false_node: AigNode,
    statistics: AigStatistics,
}

impl AigManager {
    pub fn new() -> Self {
        let mut node_data = Vec::new();
        
        // Create true node (id = 1)
        node_data.push(AigNodeData::new(AigNode::TRUE_ID));
        
        let true_node = AigNode::new(AigNode::TRUE_ID, false);
        let false_node = AigNode::new(AigNode::TRUE_ID, true);
        
        Self {
            node_data,
            unique_table: AigUniqueTable::new(),
            id_counter: AtomicI64::new(AigNode::TRUE_ID + 1),
            true_node,
            false_node,
            statistics: AigStatistics::default(),
        }
    }
    
    pub fn mk_true(&self) -> AigNode {
        self.true_node.clone()
    }
    
    pub fn mk_false(&self) -> AigNode {
        self.false_node.clone()
    }
    
    pub fn mk_const(&mut self) -> AigNode {
        self.statistics.num_consts += 1;
        let id = self.id_counter.fetch_add(1, Ordering::SeqCst);
        self.node_data.push(AigNodeData::new(id));
        AigNode::new(id, false)
    }
    
    pub fn mk_not(&self, a: &AigNode) -> AigNode {
        AigNode::new(a.get_raw_id(), !a.is_negated())
    }
    
    pub fn mk_and(&mut self, left: &AigNode, right: &AigNode) -> AigNode {
        // Check for trivial cases
        if left.is_false() || right.is_false() {
            return self.mk_false();
        }
        if left.is_true() {
            return right.clone();
        }
        if right.is_true() {
            return left.clone();
        }
        
        // Check unique table for existing AND gate
        if let Some(node_idx) = self.unique_table.find_or_insert(left, right, &mut self.node_data) {
            self.statistics.num_shared += 1;
            return AigNode::new(self.node_data[node_idx].id, false);
        }
        
        // Create new AND gate
        self.statistics.num_ands += 1;
        let id = self.id_counter.fetch_add(1, Ordering::SeqCst);
        let node_idx = self.node_data.len();
        
        self.node_data.push(AigNodeData::new_and(id, left.clone(), right.clone()));
        self.unique_table.insert(left, right, node_idx);
        
        AigNode::new(id, false)
    }
    
    pub fn mk_or(&mut self, left: &AigNode, right: &AigNode) -> AigNode {
        // De Morgan's law: a OR b = NOT(NOT a AND NOT b)
        let not_left = self.mk_not(left);
        let not_right = self.mk_not(right);
        let and_result = self.mk_and(&not_left, &not_right);
        self.mk_not(&and_result)
    }
    
    pub fn mk_iff(&mut self, left: &AigNode, right: &AigNode) -> AigNode {
        // a IFF b = (a AND b) OR (NOT a AND NOT b)
        let and1 = self.mk_and(left, right);
        let not_left = self.mk_not(left);
        let not_right = self.mk_not(right);
        let and2 = self.mk_and(&not_left, &not_right);
        self.mk_or(&and1, &and2)
    }
    
    pub fn mk_ite(&mut self, cond: &AigNode, then_node: &AigNode, else_node: &AigNode) -> AigNode {
        // ITE(c, a, b) = (c AND a) OR (NOT c AND b)
        let and1 = self.mk_and(cond, then_node);
        let not_cond = self.mk_not(cond);
        let and2 = self.mk_and(&not_cond, else_node);
        self.mk_or(&and1, &and2)
    }
    
    pub fn get_node_data(&self, node: &AigNode) -> Option<&AigNodeData> {
        let id = node.get_raw_id();
        self.node_data.iter().find(|data| data.id == id)
    }
    
    pub fn get_children(&self, node: &AigNode) -> Option<(AigNode, AigNode)> {
        if let Some(data) = self.get_node_data(node) {
            if let (Some(ref left), Some(ref right)) = (&data.left, &data.right) {
                return Some((left.clone(), right.clone()));
            }
        }
        None
    }
    
    pub fn statistics(&self) -> &AigStatistics {
        &self.statistics
    }
}

impl Default for AigManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_aig_basic_operations() {
        let mut mgr = AigManager::new();
        
        // Test constants
        let true_node = mgr.mk_true();
        let false_node = mgr.mk_false();
        let const_node = mgr.mk_const();
        
        assert!(true_node.is_true());
        assert!(false_node.is_false());
        assert!(const_node.is_const());
        
        // Test NOT
        let not_true = mgr.mk_not(&true_node);
        assert!(not_true.is_false());
        
        // Test AND
        let and_result = mgr.mk_and(&true_node, &const_node);
        assert!(and_result.is_and());
        
        // Test OR
        let or_result = mgr.mk_or(&false_node, &const_node);
        assert!(or_result.is_and()); // OR is implemented as NOT(AND(NOT, NOT))
        
        // Test IFF
        let iff_result = mgr.mk_iff(&true_node, &const_node);
        assert!(iff_result.is_and());
        
        // Test ITE
        let ite_result = mgr.mk_ite(&true_node, &const_node, &false_node);
        assert!(ite_result.is_and());
    }
    
    #[test]
    fn test_aig_hash_consing() {
        let mut mgr = AigManager::new();
        let a = mgr.mk_const();
        let b = mgr.mk_const();
        
        // Create same AND gate twice
        let and1 = mgr.mk_and(&a, &b);
        let and2 = mgr.mk_and(&a, &b);
        
        // Should be the same node due to hash consing
        assert_eq!(and1.get_raw_id(), and2.get_raw_id());
        assert_eq!(mgr.statistics().num_shared, 1);
    }
}
