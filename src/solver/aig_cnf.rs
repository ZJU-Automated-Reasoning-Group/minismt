use std::collections::{HashMap, HashSet, VecDeque};
use super::aig::AigNode;
use super::cnf::{BoolLit, Cnf};

/// Interface for SAT solver operations
pub trait SatInterface {
    fn add_literal(&mut self, lit: i32);
    fn add_clause(&mut self, literals: Vec<i32>);
    fn get_value(&self, var: i32) -> bool;
}

/// CNF encoder for AIG nodes
pub struct AigCnfEncoder<'a> {
    sat_solver: &'a mut dyn SatInterface,
    encoded: HashSet<i64>,
    var_map: HashMap<i64, i32>, // Maps AIG node ID to SAT variable
    next_var: i32,
    statistics: CnfStatistics,
}

#[derive(Debug, Default)]
pub struct CnfStatistics {
    pub num_vars: u64,
    pub num_clauses: u64,
    pub num_literals: u64,
}

impl<'a> AigCnfEncoder<'a> {
    pub fn new(sat_solver: &'a mut dyn SatInterface) -> Self {
        Self {
            sat_solver,
            encoded: HashSet::new(),
            var_map: HashMap::new(),
            next_var: 1,
            statistics: CnfStatistics::default(),
        }
    }
    
    /// Encode an AIG node to CNF
    pub fn encode(&mut self, node: &AigNode, top_level: bool) {
        if top_level {
            self.encode_top_level(node);
        } else {
            self.encode_recursive(node);
        }
    }
    
    /// Get the SAT variable for an AIG node
    pub fn get_var(&mut self, node: &AigNode) -> i32 {
        let id = node.get_raw_id();
        if let Some(&var) = self.var_map.get(&id) {
            return var;
        }
        
        let var = self.next_var;
        self.next_var += 1;
        self.var_map.insert(id, var);
        self.statistics.num_vars += 1;
        var
    }
    
    /// Get the literal for an AIG node
    pub fn get_literal(&mut self, node: &AigNode) -> i32 {
        let var = self.get_var(node);
        if node.is_negated() {
            -var
        } else {
            var
        }
    }
    
    /// Encode a top-level node (asserted as true)
    fn encode_top_level(&mut self, node: &AigNode) {
        // Collect all nodes that need to be encoded
        let mut to_encode = Vec::new();
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();
        
        queue.push_back(node.clone());
        
        while let Some(current) = queue.pop_front() {
            if !visited.insert(current.get_id()) {
                continue;
            }
            
            if current.is_and() && !current.is_negated() {
                // Add children to queue
                if let Some((left, right)) = self.get_children(&current) {
                    queue.push_back(left);
                    queue.push_back(right);
                }
            } else {
                to_encode.push(current);
            }
        }
        
        // Encode all collected nodes
        for node in &to_encode {
            self.encode_recursive(node);
        }
        
        // Assert the top-level node as true
        let lit = self.get_literal(node);
        self.sat_solver.add_clause(vec![lit]);
        self.statistics.num_clauses += 1;
        self.statistics.num_literals += 1;
    }
    
    /// Recursively encode an AIG node
    fn encode_recursive(&mut self, node: &AigNode) {
        let id = node.get_id();
        if self.encoded.contains(&id) {
            return;
        }
        
        self.encoded.insert(id);
        
        if node.is_true() || node.is_false() {
            // Constants don't need encoding
            return;
        }
        
        if node.is_const() {
            // Variables don't need encoding
            return;
        }
        
        if node.is_and() && !node.is_negated() {
            self.encode_and(node);
        } else {
            // Handle negated nodes
            let pos_node = AigNode::new(node.get_raw_id(), false);
            self.encode_recursive(&pos_node);
        }
    }
    
    /// Encode an AND gate
    fn encode_and(&mut self, node: &AigNode) {
        if let Some((left, right)) = self.get_children(node) {
            // Encode children first
            self.encode_recursive(&left);
            self.encode_recursive(&right);
            
            let out_lit = self.get_literal(node);
            let left_lit = self.get_literal(&left);
            let right_lit = self.get_literal(&right);
            
            // AND gate encoding: out <-> (left AND right)
            // This gives us:
            // 1. out -> left: -out OR left
            // 2. out -> right: -out OR right  
            // 3. left AND right -> out: -left OR -right OR out
            
            // Clause 1: -out OR left
            self.sat_solver.add_clause(vec![-out_lit, left_lit]);
            self.statistics.num_clauses += 1;
            self.statistics.num_literals += 2;
            
            // Clause 2: -out OR right
            self.sat_solver.add_clause(vec![-out_lit, right_lit]);
            self.statistics.num_clauses += 1;
            self.statistics.num_literals += 2;
            
            // Clause 3: -left OR -right OR out
            self.sat_solver.add_clause(vec![-left_lit, -right_lit, out_lit]);
            self.statistics.num_clauses += 1;
            self.statistics.num_literals += 3;
        }
    }
    
    /// Get children of an AIG node (helper method)
    fn get_children(&self, _node: &AigNode) -> Option<(AigNode, AigNode)> {
        // This would need access to the AigManager to get node data
        // For now, we'll assume this is handled externally
        None
    }
    
    /// Get the value of an AIG node from the SAT solver
    pub fn get_value(&self, node: &AigNode) -> Option<bool> {
        if node.is_true() {
            return Some(true);
        }
        if node.is_false() {
            return Some(false);
        }
        
        let id = node.get_raw_id();
        if let Some(&var) = self.var_map.get(&id) {
            let value = self.sat_solver.get_value(var);
            Some(if node.is_negated() { !value } else { value })
        } else {
            None
        }
    }
    
    pub fn statistics(&self) -> &CnfStatistics {
        &self.statistics
    }
}

/// CNF implementation that implements SatInterface
impl SatInterface for Cnf {
    fn add_literal(&mut self, lit: i32) {
        // Convert i32 literal to BoolLit and add to current clause
        let var = lit.abs() as usize;
        let polarity = lit > 0;
        let bool_lit = BoolLit(var, polarity);
        // Note: Cnf doesn't have add_literal_to_current_clause, so we'll add a single-literal clause
        self.add_clause(vec![bool_lit]);
    }
    
    fn add_clause(&mut self, literals: Vec<i32>) {
        let mut clause = Vec::new();
        for lit in literals {
            let var = lit.abs() as usize;
            let polarity = lit > 0;
            clause.push(BoolLit(var, polarity));
        }
        self.add_clause(clause);
    }
    
    fn get_value(&self, _var: i32) -> bool {
        // This would need to be implemented based on the SAT solver's model
        // For now, return false as placeholder
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::cnf::Cnf;
    use super::super::aig::AigManager;
    
    #[test]
    fn test_aig_cnf_encoding() {
        let mut cnf = Cnf::new();
        let mut encoder = AigCnfEncoder::new(&mut cnf);
        
        // Create a simple AIG: a AND b
        let mut mgr = AigManager::new();
        let a = mgr.mk_const();
        let b = mgr.mk_const();
        let and_gate = mgr.mk_and(&a, &b);
        
        // Encode the AND gate
        encoder.encode(&and_gate, false);
        
        // Should have created variables and clauses
        assert!(encoder.statistics().num_vars > 0);
        assert!(encoder.statistics().num_clauses > 0);
    }
}
