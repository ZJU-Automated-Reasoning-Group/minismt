use std::collections::HashMap;
use anyhow::{bail, Result};
use super::bv::SortBv;
use super::cnf::BoolLit;
// use super::aig_bitblaster::AigNode;

/// A node in the symbol table representing a symbol binding
#[derive(Debug, Clone)]
pub struct SymbolNode {
    /// The name of the symbol
    pub name: String,
    /// The assertion level (for push/pop support)
    pub assertion_level: u32,
    /// The sort of the symbol (for variables)
    pub sort: Option<SortBv>,
    /// The term representation (for function definitions)
    pub term: Option<super::bv::BvTerm>,
    /// The boolean literal representation (for boolean symbols)
    pub bool_lit: Option<BoolLit>,
    /// The AIG node representation (for internal use)
    // pub aig_node: Option<AigNode>,
    /// Whether this symbol is bound
    pub is_bound: bool,
    /// The next node in the shadow chain (for symbol shadowing)
    pub next: Option<Box<SymbolNode>>,
}

impl SymbolNode {
    pub fn new(name: String, assertion_level: u32) -> Self {
        Self {
            name,
            assertion_level,
            sort: None,
            term: None,
            bool_lit: None,
            // aig_node: None,
            is_bound: false,
            next: None,
        }
    }
    
    pub fn with_sort(name: String, sort: SortBv, assertion_level: u32) -> Self {
        Self {
            name,
            assertion_level,
            sort: Some(sort),
            term: None,
            bool_lit: None,
            // aig_node: None,
            is_bound: false,
            next: None,
        }
    }
    
    pub fn with_term(name: String, term: super::bv::BvTerm, assertion_level: u32) -> Self {
        Self {
            name,
            assertion_level,
            sort: None,
            term: Some(term),
            bool_lit: None,
            // aig_node: None,
            is_bound: true,
            next: None,
        }
    }
    
    pub fn with_bool_lit(name: String, bool_lit: BoolLit, assertion_level: u32) -> Self {
        Self {
            name,
            assertion_level,
            sort: None,
            term: None,
            bool_lit: Some(bool_lit),
            // aig_node: None,
            is_bound: true,
            next: None,
        }
    }
}

/// Symbol table for managing variable and function bindings with proper scoping
pub struct SymbolTable {
    /// The main symbol table mapping names to nodes
    table: HashMap<String, Box<SymbolNode>>,
    /// Pending symbols (for let bindings that need to be inserted together)
    pending_symbols: Vec<Box<SymbolNode>>,
    /// Current assertion level
    current_level: u32,
}

impl SymbolTable {
    pub fn new() -> Self {
        Self {
            table: HashMap::new(),
            pending_symbols: Vec::new(),
            current_level: 0,
        }
    }
    
    /// Find a symbol in the table
    pub fn find(&self, name: &str) -> Option<&SymbolNode> {
        self.table.get(name).map(|node| node.as_ref())
    }
    
    /// Insert a new symbol, potentially shadowing an existing one
    pub fn insert(&mut self, mut node: Box<SymbolNode>) -> Result<()> {
        let name = node.name.clone();
        
        // If symbol already exists, shadow it
        if let Some(existing) = self.table.remove(&name) {
            node.next = Some(existing);
        }
        
        self.table.insert(name, node);
        Ok(())
    }
    
    /// Insert a symbol as pending (for let bindings)
    pub fn insert_pending(&mut self, node: Box<SymbolNode>) {
        self.pending_symbols.push(node);
    }
    
    /// Insert all pending symbols
    pub fn insert_pending_symbols(&mut self) -> Result<()> {
        let pending = std::mem::take(&mut self.pending_symbols);
        for node in pending {
            self.insert(node)?;
        }
        Ok(())
    }
    
    /// Remove a symbol from the table
    pub fn remove(&mut self, name: &str) -> Option<Box<SymbolNode>> {
        if let Some(mut node) = self.table.remove(name) {
            // If there's a shadowed symbol, restore it
            if let Some(shadowed) = node.next.take() {
                let name_str = name.to_string();
                self.table.insert(name_str, shadowed);
            }
            Some(node)
        } else {
            None
        }
    }
    
    /// Push a new assertion level
    pub fn push(&mut self) {
        self.current_level += 1;
    }
    
    /// Pop an assertion level, removing all symbols at that level
    pub fn pop(&mut self) -> Result<()> {
        if self.current_level == 0 {
            bail!("Cannot pop from level 0");
        }
        
        // Remove all symbols at the current level
        let symbols_to_remove: Vec<String> = self.table
            .iter()
            .filter(|(_, node)| node.assertion_level >= self.current_level)
            .map(|(name, _)| name.clone())
            .collect();
            
        for name in symbols_to_remove {
            let _ = self.table.remove(&name);
        }
        
        self.current_level -= 1;
        Ok(())
    }
    
    /// Get the current assertion level
    pub fn current_level(&self) -> u32 {
        self.current_level
    }
    
    /// Clear all symbols
    pub fn clear(&mut self) {
        self.table.clear();
        self.pending_symbols.clear();
        self.current_level = 0;
    }
    
    /// Get all symbols at the current level
    pub fn get_symbols_at_level(&self, level: u32) -> Vec<&SymbolNode> {
        self.table
            .values()
            .filter(|node| node.assertion_level == level)
            .map(|node| node.as_ref())
            .collect()
    }
    
    /// Check if a symbol exists
    pub fn contains(&self, name: &str) -> bool {
        self.table.contains_key(name)
    }
    
    /// Get the number of symbols
    pub fn len(&self) -> usize {
        self.table.len()
    }
    
    /// Check if the table is empty
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }
}

impl Default for SymbolTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_symbol_table_basic() {
        let mut table = SymbolTable::new();
        
        let node = Box::new(SymbolNode::with_sort(
            "x".to_string(),
            SortBv { width: 32 },
            0
        ));
        
        table.insert(node).unwrap();
        assert!(table.contains("x"));
        assert_eq!(table.len(), 1);
    }
    
    #[test]
    fn test_symbol_shadowing() {
        let mut table = SymbolTable::new();
        
        let node1 = Box::new(SymbolNode::with_sort(
            "x".to_string(),
            SortBv { width: 32 },
            0
        ));
        let node2 = Box::new(SymbolNode::with_sort(
            "x".to_string(),
            SortBv { width: 64 },
            1
        ));
        
        table.insert(node1).unwrap();
        table.insert(node2).unwrap();
        
        let found = table.find("x").unwrap();
        assert_eq!(found.sort.as_ref().unwrap().width, 64);
    }
    
    #[test]
    fn test_push_pop() {
        let mut table = SymbolTable::new();
        
        let node1 = Box::new(SymbolNode::with_sort(
            "x".to_string(),
            SortBv { width: 32 },
            0
        ));
        let node2 = Box::new(SymbolNode::with_sort(
            "y".to_string(),
            SortBv { width: 64 },
            1
        ));
        
        table.insert(node1).unwrap();
        table.push();
        table.insert(node2).unwrap();
        
        assert_eq!(table.len(), 2);
        
        table.pop().unwrap();
        assert_eq!(table.len(), 1);
        assert!(table.contains("x"));
        assert!(!table.contains("y"));
    }
}
