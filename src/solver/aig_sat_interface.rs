use super::cnf::{BoolLit, Cnf};
use super::aig::AigNode;

/// SAT solver interface for AIG to CNF conversion
pub struct AigSatInterface<'a> {
    cnf: &'a mut Cnf,
    var_map: std::collections::HashMap<i64, usize>, // Maps AIG node ID to CNF variable
    next_var: usize,
}

impl<'a> AigSatInterface<'a> {
    pub fn new(cnf: &'a mut Cnf) -> Self {
        let next_var = cnf.num_vars + 1;
        Self {
            cnf,
            var_map: std::collections::HashMap::new(),
            next_var,
        }
    }
    
    /// Get or create a CNF variable for an AIG node
    fn get_var(&mut self, node: &AigNode) -> usize {
        let id = node.get_raw_id();
        if let Some(&var) = self.var_map.get(&id) {
            return var;
        }
        
        let var = self.next_var;
        self.next_var += 1;
        self.var_map.insert(id, var);
        self.cnf.num_vars = self.cnf.num_vars.max(var + 1);
        var
    }
    
    /// Convert AIG node to CNF literal
    fn node_to_literal(&mut self, node: &AigNode) -> BoolLit {
        let var = self.get_var(node);
        BoolLit(var, !node.is_negated())
    }
}

impl<'a> super::aig_cnf::SatInterface for AigSatInterface<'a> {
    fn add_literal(&mut self, lit: i32) {
        let var = lit.abs() as usize;
        let polarity = lit > 0;
        let bool_lit = BoolLit(var, polarity);
        self.cnf.add_clause(vec![bool_lit]);
    }
    
    fn add_clause(&mut self, literals: Vec<i32>) {
        let mut clause = Vec::new();
        for lit in literals {
            let var = lit.abs() as usize;
            let polarity = lit > 0;
            clause.push(BoolLit(var, polarity));
        }
        self.cnf.add_clause(clause);
    }
    
    fn get_value(&self, _var: i32) -> bool {
        // This would need to be implemented based on the SAT solver's model
        // For now, return false as placeholder
        false
    }
}

/// Adapter that converts between AigNode and BoolLit for backward compatibility
pub struct AigBitBlasterAdapter {
    aig_blaster: super::aig_bitblaster::AigBitBlaster,
    cnf: Cnf,
    sat_interface: Option<AigSatInterface<'static>>, // Will be properly initialized
}

impl AigBitBlasterAdapter {
    pub fn new() -> Self {
        Self {
            aig_blaster: super::aig_bitblaster::AigBitBlaster::new(),
            cnf: Cnf::new(),
            sat_interface: None,
        }
    }
    
    pub fn new_with_config(config: super::config::SolverConfig) -> Self {
        Self {
            aig_blaster: super::aig_bitblaster::AigBitBlaster::new_with_config(config),
            cnf: Cnf::new(),
            sat_interface: None,
        }
    }
    
    /// Convert AIG node to BoolLit for backward compatibility
    fn aig_to_bool_lit(&mut self, _node: &AigNode) -> BoolLit {
        // Create a temporary SAT interface to convert the node
        let mut temp_interface = AigSatInterface::new(&mut self.cnf);
        temp_interface.node_to_literal(_node)
    }
    
    /// Convert BoolLit to AIG node (for constants)
    fn bool_lit_to_aig(&mut self, lit: BoolLit) -> AigNode {
        if lit.1 {
            self.aig_blaster.const_lit(true)
        } else {
            self.aig_blaster.const_lit(false)
        }
    }
    
    pub fn new_bool(&mut self) -> BoolLit {
        let aig_node = self.aig_blaster.new_bool();
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn mk_not(&mut self, a: BoolLit) -> BoolLit {
        let aig_a = self.bool_lit_to_aig(a);
        let result = self.aig_blaster.mk_not(&aig_a);
        self.aig_to_bool_lit(&result)
    }
    
    pub fn mk_and(&mut self, lits: &[BoolLit]) -> BoolLit {
        if lits.is_empty() {
            return self.aig_blaster.const_lit(true).into();
        }
        if lits.len() == 1 {
            return lits[0];
        }
        
        let aig_lits: Vec<AigNode> = lits.iter().map(|lit| self.bool_lit_to_aig(*lit)).collect();
        let mut result = aig_lits[0].clone();
        for lit in &aig_lits[1..] {
            result = self.aig_blaster.mk_and(&result, lit);
        }
        self.aig_to_bool_lit(&result)
    }
    
    pub fn mk_or(&mut self, lits: &[BoolLit]) -> BoolLit {
        if lits.is_empty() {
            return self.aig_blaster.const_lit(false).into();
        }
        if lits.len() == 1 {
            return lits[0];
        }
        
        let aig_lits: Vec<AigNode> = lits.iter().map(|lit| self.bool_lit_to_aig(*lit)).collect();
        let mut result = aig_lits[0].clone();
        for lit in &aig_lits[1..] {
            result = self.aig_blaster.mk_or(&result, lit);
        }
        self.aig_to_bool_lit(&result)
    }
    
    pub fn encode_xor_var(&mut self, a: BoolLit, b: BoolLit) -> BoolLit {
        let aig_a = self.bool_lit_to_aig(a);
        let aig_b = self.bool_lit_to_aig(b);
        let result = self.aig_blaster.mk_xor(&aig_a, &aig_b);
        self.aig_to_bool_lit(&result)
    }
    
    pub fn get_bool_sym<S: Into<String>>(&mut self, name: S) -> BoolLit {
        let aig_node = self.aig_blaster.get_bool_sym(name);
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn lookup_bool_sym(&self, name: &str) -> Option<BoolLit> {
        self.aig_blaster.lookup_bool_sym(name).map(|_node| {
            // This is a bit tricky since we need to convert without mutable access
            // For now, return a placeholder
            BoolLit(0, true)
        })
    }
    
    pub fn const_lit(&mut self, value: bool) -> BoolLit {
        let aig_node = self.aig_blaster.const_lit(value);
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn assert_true(&mut self, lit: BoolLit) {
        self.cnf.add_clause(vec![lit]);
    }
    
    pub fn mk_implies(&mut self, a: BoolLit, b: BoolLit) -> BoolLit {
        // a -> b is (¬a ∨ b)
        let not_a = self.mk_not(a);
        self.mk_or(&[not_a, b])
    }
    
    pub fn emit_bit(&mut self, t: &super::bv::BvTerm, i: u32) -> BoolLit {
        let aig_node = self.aig_blaster.emit_bit(t, i);
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn bool_eq(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.bool_eq(a, b);
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn emit_ult_bool(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.emit_ult_bool(a, b);
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn emit_ule_bool(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.emit_ule_bool(a, b);
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn emit_slt_bool(&mut self, a: &super::bv::BvTerm, b: &super::bv::BvTerm) -> BoolLit {
        let aig_node = self.aig_blaster.emit_slt_bool(a, b);
        self.aig_to_bool_lit(&aig_node)
    }
    
    pub fn ite_bit(&mut self, c: BoolLit, t: BoolLit, e: BoolLit) -> BoolLit {
        let aig_c = self.bool_lit_to_aig(c);
        let aig_t = self.bool_lit_to_aig(t);
        let aig_e = self.bool_lit_to_aig(e);
        let result = self.aig_blaster.ite_bit(&aig_c, &aig_t, &aig_e);
        self.aig_to_bool_lit(&result)
    }
    
    pub fn emit_bits(&mut self, t: &super::bv::BvTerm) -> Vec<BoolLit> {
        let aig_bits = self.aig_blaster.emit_bits(t);
        aig_bits.into_iter().map(|node| self.aig_to_bool_lit(&node)).collect()
    }
    
    // Access to underlying CNF and AIG structures
    pub fn cnf(&self) -> &Cnf {
        &self.cnf
    }
    
    pub fn cnf_mut(&mut self) -> &mut Cnf {
        &mut self.cnf
    }
    
    pub fn bool_syms(&self) -> &std::collections::HashMap<String, AigNode> {
        &self.aig_blaster.bool_syms
    }
    
    pub fn var_bits(&self) -> &std::collections::HashMap<(String, u32), AigNode> {
        &self.aig_blaster.var_bits
    }
}

impl Default for AigBitBlasterAdapter {
    fn default() -> Self {
        Self::new()
    }
}

// Conversion from AigNode to BoolLit (simplified)
impl From<AigNode> for BoolLit {
    fn from(_node: AigNode) -> Self {
        // This is a placeholder - in practice, we'd need proper variable mapping
        BoolLit(0, true)
    }
}
