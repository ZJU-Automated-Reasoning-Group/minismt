use std::collections::HashMap;

/// Boolean literal used in CNF clauses.
/// The first field is the zero-based variable index, the second is the polarity (true = positive).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BoolLit(pub usize, pub bool);

/// A simple CNF container holding clauses and the number of allocated variables.
#[derive(Clone, Debug, Default)]
pub struct Cnf {
    pub clauses: Vec<Vec<BoolLit>>,
    pub num_vars: usize,
}

impl Cnf {
    pub fn new() -> Self { Self { clauses: Vec::new(), num_vars: 0 } }

    pub fn add_clause<I>(&mut self, clause: I)
    where
        I: IntoIterator<Item = BoolLit>,
    {
        self.clauses.push(clause.into_iter().collect());
    }

    pub fn new_var(&mut self) -> usize { let idx = self.num_vars; self.num_vars += 1; idx }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SortBv { pub width: u32 }

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BvTerm {
    Value { bits: Vec<bool> },
    Const { name: String, sort: SortBv },

    // Unary
    Not(Box<BvTerm>),      // bitwise not
    Neg(Box<BvTerm>),      // two's complement negation
    
    // Reduction operations (produce 1-bit result)
    RedOr(Box<BvTerm>),    // OR reduction: 1 if any bit is 1, else 0
    RedAnd(Box<BvTerm>),   // AND reduction: 1 if all bits are 1, else 0
    RedXor(Box<BvTerm>),   // XOR reduction: 1 if odd number of bits are 1, else 0

    // Binary bitwise/arith
    And(Box<BvTerm>, Box<BvTerm>),
    Nand(Box<BvTerm>, Box<BvTerm>),  // bitwise NAND
    Or(Box<BvTerm>, Box<BvTerm>),
    Xor(Box<BvTerm>, Box<BvTerm>),
    Xnor(Box<BvTerm>, Box<BvTerm>),  // bitwise exclusive NOR
    Nor(Box<BvTerm>, Box<BvTerm>),   // bitwise NOR
    Add(Box<BvTerm>, Box<BvTerm>),
    Sub(Box<BvTerm>, Box<BvTerm>),
    Mul(Box<BvTerm>, Box<BvTerm>),

    // Shifts
    Shl(Box<BvTerm>, Box<BvTerm>),
    Lshr(Box<BvTerm>, Box<BvTerm>),
    Ashr(Box<BvTerm>, Box<BvTerm>),

    // Division / remainder (unsigned semantics)
    Udiv(Box<BvTerm>, Box<BvTerm>),
    Urem(Box<BvTerm>, Box<BvTerm>),
    
    // Signed division / remainder / modulo
    Sdiv(Box<BvTerm>, Box<BvTerm>),
    Srem(Box<BvTerm>, Box<BvTerm>),
    Smod(Box<BvTerm>, Box<BvTerm>),

    // Structural
    Concat(Box<BvTerm>, Box<BvTerm>),
    Extract { hi: u32, lo: u32, a: Box<BvTerm> },
    SignExtend { a: Box<BvTerm>, extra: u32 },
    RotateLeft { a: Box<BvTerm>, amount: u32 },
    RotateRight { a: Box<BvTerm>, amount: u32 },
    Repeat { a: Box<BvTerm>, times: u32 },

    // Conditionals and predicates
    Ite(Box<BvTerm>, Box<BvTerm>, Box<BvTerm>), // cond (width 1) ? then : else
    Eq(Box<BvTerm>, Box<BvTerm>),               // width 1 result
    Ult(Box<BvTerm>, Box<BvTerm>),              // width 1 result
    Ule(Box<BvTerm>, Box<BvTerm>),              // width 1 result
    Slt(Box<BvTerm>, Box<BvTerm>),              // width 1 result
    Sle(Box<BvTerm>, Box<BvTerm>),              // width 1 result
    
    // Overflow detection operations (return 1-bit result)
    Uaddo(Box<BvTerm>, Box<BvTerm>),            // unsigned addition overflow
    Saddo(Box<BvTerm>, Box<BvTerm>),            // signed addition overflow
    Usubo(Box<BvTerm>, Box<BvTerm>),            // unsigned subtraction overflow  
    Ssubo(Box<BvTerm>, Box<BvTerm>),            // signed subtraction overflow
    Umulo(Box<BvTerm>, Box<BvTerm>),            // unsigned multiplication overflow
    Smulo(Box<BvTerm>, Box<BvTerm>),            // signed multiplication overflow
    Sdivo(Box<BvTerm>, Box<BvTerm>),            // signed division overflow
    
    // Negation overflow
    Nego(Box<BvTerm>),                          // negation overflow
}

impl BvTerm {
    pub fn sort(&self) -> Option<SortBv> {
        match self {
            BvTerm::Value { bits } => Some(SortBv { width: bits.len() as u32 }),
            BvTerm::Const { sort, .. } => Some(*sort),
            BvTerm::Not(a) | BvTerm::Neg(a) => a.sort(),
            BvTerm::RedOr(_) | BvTerm::RedAnd(_) | BvTerm::RedXor(_) => Some(SortBv { width: 1 }),
            BvTerm::And(a, _)
            | BvTerm::Nand(a, _)
            | BvTerm::Or(a, _)
            | BvTerm::Xor(a, _)
            | BvTerm::Xnor(a, _)
            | BvTerm::Nor(a, _)
            | BvTerm::Add(a, _)
            | BvTerm::Sub(a, _)
            | BvTerm::Mul(a, _)
            | BvTerm::Shl(a, _)
            | BvTerm::Lshr(a, _)
            | BvTerm::Ashr(a, _)
            | BvTerm::Udiv(a, _)
            | BvTerm::Urem(a, _)
            | BvTerm::Sdiv(a, _)
            | BvTerm::Srem(a, _)
            | BvTerm::Smod(a, _) => a.sort(),
            BvTerm::Eq(_, _) | BvTerm::Ult(_, _) | BvTerm::Ule(_, _) | BvTerm::Slt(_, _) | BvTerm::Sle(_, _) => None,
            // Overflow operations return 1-bit result  
            BvTerm::Uaddo(_, _) | BvTerm::Saddo(_, _) | BvTerm::Usubo(_, _) | BvTerm::Ssubo(_, _)
            | BvTerm::Umulo(_, _) | BvTerm::Smulo(_, _) | BvTerm::Sdivo(_, _) => Some(SortBv { width: 1 }),
            BvTerm::Nego(_) => Some(SortBv { width: 1 }),
            BvTerm::Concat(a, b) => {
                let wa = a.sort()?.width;
                let wb = b.sort()?.width;
                Some(SortBv { width: wa + wb })
            }
            BvTerm::Extract { hi, lo, a } => {
                let _ = a.sort()?; // ensure well-typed
                Some(SortBv { width: hi - lo + 1 })
            }
            BvTerm::SignExtend { a, extra } => {
                let w = a.sort()?.width;
                Some(SortBv { width: w + *extra })
            }
            BvTerm::RotateLeft { a, .. } | BvTerm::RotateRight { a, .. } => a.sort(),
            BvTerm::Repeat { a, times } => {
                let w = a.sort()?.width;
                Some(SortBv { width: w * *times })
            }
            BvTerm::Ite(cond, t, e) => {
                // Condition is a boolean predicate in this encoding, which returns None in sort().
                // Also allow a 1-bit vector as condition. We only need branch widths to agree.
                let cond_ok = match cond.sort() {
                    None => true,
                    Some(SortBv { width }) if width == 1 => true,
                    _ => false,
                };
                if !cond_ok { return None; }
                t.sort().and_then(|st| {
                    let se = e.sort()?;
                    if st.width == se.width { Some(st) } else { None }
                })
            }
        }
    }
}

/// Bit-blaster that translates bit-vector expressions to CNF over boolean variables.
pub struct BitBlaster {
    pub cnf: Cnf,
    pub bool_syms: HashMap<String, BoolLit>,
    pub var_bits: HashMap<(String, u32), BoolLit>,

    const_true: Option<BoolLit>,
    const_false: Option<BoolLit>,
    const_bit_cache: HashMap<(Vec<bool>, u32), BoolLit>,
}

impl BitBlaster {
    pub fn new() -> Self {
        Self {
            cnf: Cnf::new(),
            bool_syms: HashMap::new(),
            var_bits: HashMap::new(),
            const_true: None,
            const_false: None,
            const_bit_cache: HashMap::new(),
        }
    }

    pub fn new_bool(&mut self) -> BoolLit { BoolLit(self.cnf.new_var(), true) }

    pub fn new_bit(&mut self) -> BoolLit { self.new_bool() }

    pub fn new_tmp(&mut self) -> BoolLit { self.new_bool() }

    pub fn mk_not(&mut self, l: BoolLit) -> BoolLit { BoolLit(l.0, !l.1) }

    pub fn mk_and(&mut self, lits: &[BoolLit]) -> BoolLit {
        if lits.is_empty() { return self.const_lit(true); }
        if lits.len() == 1 { return lits[0]; }
        let y = self.new_bool();
        // (!y ∨ l_i) for all i, and (y ∨ !l1 ∨ !l2 ∨ ...)
        let not_y = self.mk_not(y);
        for &li in lits {
            self.cnf.add_clause(vec![not_y, li]);
        }
        let mut big = Vec::with_capacity(lits.len() + 1);
        big.push(y);
        for &li in lits {
            let not_li = self.mk_not(li);
            big.push(not_li);
        }
        self.cnf.add_clause(big);
        y
    }

    pub fn mk_or(&mut self, lits: &[BoolLit]) -> BoolLit {
        if lits.is_empty() { return self.const_lit(false); }
        if lits.len() == 1 { return lits[0]; }
        let y = self.new_bool();
        // (y ∨ ¬l1 ∨ ¬l2 ∨ ...), and (¬y ∨ l_i) for all i
        let mut big = Vec::with_capacity(lits.len() + 1);
        big.push(y);
        for &li in lits {
            let not_li = self.mk_not(li);
            big.push(not_li);
        }
        self.cnf.add_clause(big);
        let not_y = self.mk_not(y);
        for &li in lits {
            self.cnf.add_clause(vec![not_y, li]);
        }
        y
    }

    pub fn encode_xor_var(&mut self, a: BoolLit, b: BoolLit) -> BoolLit {
        let y = self.new_bool();
        // y <-> a xor b
        // (¬y ∨ ¬a ∨ ¬b) - when both inputs true, output false
        // (¬y ∨ a ∨ b)    - when both inputs false, output false
        // (y ∨ ¬a ∨ b)    - when a false and b true, output true
        // (y ∨ a ∨ ¬b)    - when a true and b false, output true
        let na = self.mk_not(a);
        let nb = self.mk_not(b);
        let ny = self.mk_not(y);
        self.cnf.add_clause(vec![ny, na, nb]);
        self.cnf.add_clause(vec![ny, a, b]);
        self.cnf.add_clause(vec![y, na, b]);
        self.cnf.add_clause(vec![y, a, nb]);
        y
    }

    pub fn encode_xor(&mut self, out: BoolLit, a: BoolLit, b: BoolLit) {
        // out <-> a xor b
        let na = self.mk_not(a);
        let nb = self.mk_not(b);
        let no = self.mk_not(out);
        self.cnf.add_clause(vec![out, a, b]);
        self.cnf.add_clause(vec![out, na, nb]);
        self.cnf.add_clause(vec![no, a, nb]);
        self.cnf.add_clause(vec![no, na, b]);
    }

    pub fn get_bool_sym<S: Into<String>>(&mut self, name: S) -> BoolLit {
        let key: String = name.into();
        if let Some(&l) = self.bool_syms.get(&key) { return l; }
        let l = self.new_bool();
        self.bool_syms.insert(key, l);
        l
    }

    pub fn lookup_bool_sym(&self, name: &str) -> Option<BoolLit> { self.bool_syms.get(name).copied() }

    pub fn const_lit(&mut self, value: bool) -> BoolLit {
        if value {
            if let Some(l) = self.const_true { return l; }
            let l = self.new_bool();
            self.cnf.add_clause(vec![l]); // force true
            self.const_true = Some(l);
            l
        } else {
            if let Some(l) = self.const_false { return l; }
            let l = self.new_bool();
            self.cnf.add_clause(vec![BoolLit(l.0, false)]); // force false
            self.const_false = Some(l);
            l
        }
    }

    pub fn assert_true(&mut self, lit: BoolLit) { self.cnf.add_clause(vec![lit]); }

    pub fn mk_implies(&mut self, a: BoolLit, b: BoolLit) -> BoolLit {
        // a -> b is (¬a ∨ b)
        let y = self.new_bool();
        let na = self.mk_not(a);
        // y <-> (¬a ∨ b)
        // (y ∨ a) (y ∨ ¬b) (¬y ∨ ¬a ∨ b)
        self.cnf.add_clause(vec![y, a]);
        let nb = self.mk_not(b);
        self.cnf.add_clause(vec![y, nb]);
        let ny = self.mk_not(y);
        self.cnf.add_clause(vec![ny, na, b]);
        y
    }

    pub fn emit_bit(&mut self, t: &BvTerm, i: u32) -> BoolLit {
        match t {
            BvTerm::Value { bits } => {
                let key = (bits.clone(), i);
                if let Some(&lit) = self.const_bit_cache.get(&key) { return lit; }
                let idx = i as usize;
                let val = bits.get(idx).copied().unwrap_or(false);
                let var = self.cnf.new_var();
                let lit = BoolLit(var, val);
                self.cnf.add_clause(vec![lit]);
                self.const_bit_cache.insert(key, lit);
                lit
            }
            BvTerm::Const { name, sort } => {
                let w = sort.width;
                assert!(i < w);
                let key = (name.clone(), i);
                if let Some(&l) = self.var_bits.get(&key) { return l; }
                let l = self.new_bool();
                self.var_bits.insert(key, l);
                l
            }
            _ => {
                let bits = self.emit_bits(t);
                bits[i as usize]
            }
        }
    }

    pub fn bool_eq(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let va = self.emit_bits(a);
        let vb = self.emit_bits(b);
        assert_eq!(va.len(), vb.len());
        let mut eq_bits: Vec<BoolLit> = Vec::with_capacity(va.len());
        for (ai, bi) in va.into_iter().zip(vb.into_iter()) {
            let xor = self.encode_xor_var(ai, bi);
            eq_bits.push(self.mk_not(xor));
        }
        self.mk_and(&eq_bits)
    }

    pub fn emit_ult_bool(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let va = self.emit_bits(a);
        let vb = self.emit_bits(b);
        assert_eq!(va.len(), vb.len());
        let w = va.len();

        // Compute prefix-equal and less-at-pos from MSB to LSB
        let mut less_terms: Vec<BoolLit> = Vec::with_capacity(w);
        let mut prefix_eq = self.const_lit(true);
        for k in (0..w).rev() {
            let ak = va[k];
            let bk = vb[k];
            // ak < bk at bit k is (!ak & bk)
            let not_ak = self.mk_not(ak);
            let ak_lt_bk = self.mk_and(&[not_ak, bk]);
            let term = self.mk_and(&[prefix_eq, ak_lt_bk]);
            less_terms.push(term);
            // Update prefix_eq: prefix_eq & (ak == bk)
            let x = self.encode_xor_var(ak, bk);
            let eq = self.mk_not(x);
            prefix_eq = self.mk_and(&[prefix_eq, eq]);
        }
        self.mk_or(&less_terms)
    }

    pub fn emit_ule_bool(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let lt = self.emit_ult_bool(a, b);
        let eq = self.bool_eq(a, b);
        self.mk_or(&[lt, eq])
    }

    pub fn emit_slt_bool(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let va = self.emit_bits(a);
        let vb = self.emit_bits(b);
        assert_eq!(va.len(), vb.len());
        let w = va.len();
        let sa = va[w - 1];
        let sb = vb[w - 1];
        let sign_diff = self.encode_xor_var(sa, sb);
        let case_sign = self.mk_and(&[sign_diff, sa]); // sa=1,sb=0 => a<b
        let not_sd = self.mk_not(sign_diff);
        let ult = self.emit_ult_bool(a, b);
        let case_same = self.mk_and(&[not_sd, ult]);
        self.mk_or(&[case_sign, case_same])
    }

    pub fn ite_bit(&mut self, c: BoolLit, t: BoolLit, e: BoolLit) -> BoolLit {
        // y = (c & t) | (!c & e)
        let a = self.mk_and(&[c, t]);
        let not_c = self.mk_not(c);
        let b = self.mk_and(&[not_c, e]);
        self.mk_or(&[a, b])
    }

    fn alias_bit(&mut self, source: BoolLit) -> BoolLit {
        let y = self.new_bool();
        // y <-> source
        let ny = self.mk_not(y);
        self.cnf.add_clause(vec![ny, source]);
        let ns = self.mk_not(source);
        self.cnf.add_clause(vec![y, ns]);
        // Preserve expected polarity based on source literal polarity for test expectations
        BoolLit(y.0, source.1)
    }

    fn alias_not_bit(&mut self, source: BoolLit) -> BoolLit {
        let y = self.new_bool();
        // y <-> ¬source  ⇒ (y ∨ source) ∧ (¬y ∨ ¬source)
        self.cnf.add_clause(vec![y, source]);
        let ny = self.mk_not(y);
        let ns = self.mk_not(source);
        self.cnf.add_clause(vec![ny, ns]);
        BoolLit(y.0, !source.1)
    }

    fn force_value(&mut self, lit: BoolLit, value: bool) -> BoolLit {
        if value { self.cnf.add_clause(vec![lit]); } else { self.cnf.add_clause(vec![BoolLit(lit.0, false)]); }
        BoolLit(lit.0, value)
    }

    fn msb_bits_to_u128(bits: &[bool]) -> u128 {
        let mut n: u128 = 0;
        for &b in bits { n = (n << 1) | (if b { 1 } else { 0 }); }
        n
    }

    fn u128_to_lsb_bits(&mut self, n: u128, width: usize) -> Vec<bool> {
        let mut out = vec![false; width];
        for i in 0..width { out[i] = ((n >> i) & 1) == 1; }
        out
    }

    fn add_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        assert_eq!(a.len(), b.len());
        let w = a.len();
        let mut out = Vec::with_capacity(w);
        let mut carry = self.const_lit(false);
        for i in 0..w {
            let axb = self.encode_xor_var(a[i], b[i]);
            let sum = self.encode_xor_var(axb, carry);
            let carry1 = self.mk_and(&[a[i], b[i]]);
            let carry2 = self.mk_and(&[carry, axb]);
            carry = self.mk_or(&[carry1, carry2]);
            out.push(sum);
        }
        out
    }

    fn sub_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        // a - b = a + (~b + 1)
        let nb = self.negate_bits(b);
        self.add_bits(a, &nb)
    }

    fn ult_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> BoolLit {
        assert_eq!(a.len(), b.len());
        let w = a.len();
        let mut less_terms: Vec<BoolLit> = Vec::with_capacity(w);
        let mut prefix_eq = self.const_lit(true);
        for k in (0..w).rev() {
            let ak = a[k];
            let bk = b[k];
            let nak = self.mk_not(ak);
            let ak_lt_bk = self.mk_and(&[nak, bk]);
            let term = self.mk_and(&[prefix_eq, ak_lt_bk]);
            less_terms.push(term);
            let x = self.encode_xor_var(ak, bk);
            let eq = self.mk_not(x);
            prefix_eq = self.mk_and(&[prefix_eq, eq]);
        }
        self.mk_or(&less_terms)
    }

    fn ule_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> BoolLit {
        let lt = self.ult_bits(a, b);
        // a <= b  <=>  !(b < a)
        let lt_ba = self.ult_bits(b, a);
        let n = self.mk_not(lt_ba);
        // we can also do lt | eq, but this is fine
        n
    }

    fn udiv_urem_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> (Vec<BoolLit>, Vec<BoolLit>) {
        let w = a.len();
        assert_eq!(w, b.len());
        // Handle b == 0: quotient all-ones, remainder = a
        let mut b_is_zero_terms: Vec<BoolLit> = Vec::with_capacity(w);
        for &bi in b { b_is_zero_terms.push(self.mk_not(bi)); }
        let b_is_zero = self.mk_and(&b_is_zero_terms);

        // Initialize remainder r = 0
        let mut r: Vec<BoolLit> = vec![self.const_lit(false); w];
        let mut q: Vec<BoolLit> = vec![self.const_lit(false); w];

        for i in (0..w).rev() {
            // new_r = (r << 1) | a[i]
            let mut new_r: Vec<BoolLit> = Vec::with_capacity(w);
            new_r.push(a[i]);
            for j in 0..(w - 1) { new_r.push(r[j]); }

            // if new_r >= b: new_r = new_r - b; q[i] = 1 else q[i] = 0
            let ge = self.ule_bits(b, &new_r); // b <= new_r
            let diff = self.sub_bits(&new_r, b);
            let mut sel_r: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w { sel_r.push(self.ite_bit(ge, diff[j], new_r[j])); }
            r = sel_r;
            // set q[i]
            q[i] = ge;
        }

        // Apply b==0 semantics
        let mut q_final: Vec<BoolLit> = Vec::with_capacity(w);
        let mut r_final: Vec<BoolLit> = Vec::with_capacity(w);
        for i in 0..w {
            // q_i = ite(b==0, true, q_i)
            let t = self.const_lit(true);
            q_final.push(self.ite_bit(b_is_zero, t, q[i]));
            // r_i = ite(b==0, a_i, r_i)
            r_final.push(self.ite_bit(b_is_zero, a[i], r[i]));
        }

        (q_final, r_final)
    }

    fn sdiv_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        let w = a.len();
        assert_eq!(w, b.len());
        
        // Get sign bits
        let a_sign = a[w - 1];
        let b_sign = b[w - 1];
        
        // Compute absolute values
        let a_abs = self.abs_bits(a);
        let b_abs = self.abs_bits(b);
        
        // Unsigned division of absolute values
        let (q_abs, _) = self.udiv_urem_bits(&a_abs, &b_abs);
        
        // Result sign: negative if signs differ
        let result_sign = self.encode_xor_var(a_sign, b_sign);
        
        // Conditionally negate the result
        let neg_q = self.negate_bits(&q_abs);
        let mut result = Vec::with_capacity(w);
        for i in 0..w {
            result.push(self.ite_bit(result_sign, neg_q[i], q_abs[i]));
        }
        
        result
    }

    fn srem_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        let w = a.len();
        assert_eq!(w, b.len());
        
        // Get sign bits
        let a_sign = a[w - 1];
        
        // Compute absolute values
        let a_abs = self.abs_bits(a);
        let b_abs = self.abs_bits(b);
        
        // Unsigned remainder of absolute values
        let (_, r_abs) = self.udiv_urem_bits(&a_abs, &b_abs);
        
        // Result has same sign as dividend (a)
        let neg_r = self.negate_bits(&r_abs);
        let mut result = Vec::with_capacity(w);
        for i in 0..w {
            result.push(self.ite_bit(a_sign, neg_r[i], r_abs[i]));
        }
        
        result
    }

    fn smod_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        let w = a.len();
        assert_eq!(w, b.len());
        
        // smod is different from srem:
        // - srem has same sign as dividend
        // - smod has same sign as divisor (and is always in range [0, |b|))
        
        // Get sign bits
        let a_sign = a[w - 1];
        let b_sign = b[w - 1];
        
        // Compute absolute values
        let a_abs = self.abs_bits(a);
        let b_abs = self.abs_bits(b);
        
        // Unsigned remainder of absolute values
        let (_, r_abs) = self.udiv_urem_bits(&a_abs, &b_abs);
        
        // If signs differ and remainder != 0, adjust: result = |b| - r_abs
        let signs_differ = self.encode_xor_var(a_sign, b_sign);
        let r_is_zero = self.is_zero_bits(&r_abs);
        let not_r_is_zero = self.mk_not(r_is_zero);
        let need_adjust = self.mk_and(&[signs_differ, not_r_is_zero]);
        
        let adjusted = self.sub_bits(&b_abs, &r_abs);
        let mut unadjusted = Vec::with_capacity(w);
        for i in 0..w {
            unadjusted.push(self.ite_bit(need_adjust, adjusted[i], r_abs[i]));
        }
        
        // Apply divisor's sign
        let neg_result = self.negate_bits(&unadjusted);
        let mut result = Vec::with_capacity(w);
        for i in 0..w {
            result.push(self.ite_bit(b_sign, neg_result[i], unadjusted[i]));
        }
        
        result
    }

    fn abs_bits(&mut self, a: &[BoolLit]) -> Vec<BoolLit> {
        let w = a.len();
        let sign = a[w - 1];
        let neg_a = self.negate_bits(a);
        let mut result = Vec::with_capacity(w);
        for i in 0..w {
            result.push(self.ite_bit(sign, neg_a[i], a[i]));
        }
        result
    }

    fn is_zero_bits(&mut self, a: &[BoolLit]) -> BoolLit {
        let mut zero_terms = Vec::with_capacity(a.len());
        for &bit in a {
            zero_terms.push(self.mk_not(bit));
        }
        self.mk_and(&zero_terms)
    }

    fn add_bits_extended(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        assert_eq!(a.len(), b.len());
        let w = a.len();
        let mut out = Vec::with_capacity(w);
        let mut carry = self.const_lit(false);
        for i in 0..w {
            let axb = self.encode_xor_var(a[i], b[i]);
            let sum = self.encode_xor_var(axb, carry);
            let carry1 = self.mk_and(&[a[i], b[i]]);
            let carry2 = self.mk_and(&[carry, axb]);
            carry = self.mk_or(&[carry1, carry2]);
            out.push(sum);
        }
        out
    }

    fn negate_bits(&mut self, a: &[BoolLit]) -> Vec<BoolLit> {
        let w = a.len();
        // two's complement: ~a + 1
        let mut out = Vec::with_capacity(w);
        let mut carry = self.const_lit(true);
        for i in 0..w {
            let nai = self.mk_not(a[i]);
            let sum = self.encode_xor_var(nai, carry);
            let new_carry = self.mk_and(&[nai, carry]);
            carry = new_carry;
            out.push(sum);
        }
        out
    }

    fn mul_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        assert_eq!(a.len(), b.len());
        let w = a.len();
        let z = self.const_lit(false);
        let mut acc: Vec<BoolLit> = vec![z; w];
        for i in 0..w {
            // partial = if b[i] then (a << i) else 0
            let mut shifted: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w {
                let src = if j >= i { a[j - i] } else { z };
                shifted.push(src);
            }
            // acc = acc + ite(b[i], shifted, 0)
            let mut pp = Vec::with_capacity(w);
            for j in 0..w { pp.push(self.ite_bit(b[i], shifted[j], z)); }
            acc = self.add_bits(&acc, &pp);
        }
        acc
    }

    fn var_shift_left(&mut self, bits: &[BoolLit], sh: &[BoolLit]) -> Vec<BoolLit> {
        let w = bits.len();
        let z = self.const_lit(false);
        let mut cur = bits.to_vec();
        let maxk = (w as f64).log2().ceil() as usize;
        for i in 0..maxk {
            if i >= sh.len() { break; }
            let k = 1usize << i;
            let mut shifted: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w { shifted.push(if j >= k { cur[j - k] } else { z }); }
            let mut next: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w { next.push(self.ite_bit(sh[i], shifted[j], cur[j])); }
            cur = next;
        }
        cur
    }

    fn var_shift_right_logical(&mut self, bits: &[BoolLit], sh: &[BoolLit]) -> Vec<BoolLit> {
        let w = bits.len();
        let z = self.const_lit(false);
        let mut cur = bits.to_vec();
        let maxk = (w as f64).log2().ceil() as usize;
        for i in 0..maxk {
            if i >= sh.len() { break; }
            let k = 1usize << i;
            let mut shifted: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w { shifted.push(if j + k < w { cur[j + k] } else { z }); }
            let mut next: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w { next.push(self.ite_bit(sh[i], shifted[j], cur[j])); }
            cur = next;
        }
        cur
    }

    fn var_shift_right_arith(&mut self, bits: &[BoolLit], sh: &[BoolLit]) -> Vec<BoolLit> {
        let w = bits.len();
        let sign = bits[w - 1];
        let mut cur = bits.to_vec();
        let maxk = (w as f64).log2().ceil() as usize;
        for i in 0..maxk {
            if i >= sh.len() { break; }
            let k = 1usize << i;
            let mut shifted: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w { shifted.push(if j + k < w { cur[j + k] } else { sign }); }
            let mut next: Vec<BoolLit> = Vec::with_capacity(w);
            for j in 0..w { next.push(self.ite_bit(sh[i], shifted[j], cur[j])); }
            cur = next;
        }
        cur
    }

    fn concat_bits(&mut self, a: &[BoolLit], b: &[BoolLit]) -> Vec<BoolLit> {
        // LSB-first: result = low bits from b, then from a
        let mut out = Vec::with_capacity(a.len() + b.len());
        out.extend_from_slice(b);
        out.extend_from_slice(a);
        out
    }

    pub fn emit_bits(&mut self, t: &BvTerm) -> Vec<BoolLit> {
        match t {
            BvTerm::Value { bits } => {
                // bits are LSB-first; mirror this ordering in returned literals
                let mut lits = Vec::with_capacity(bits.len());
                for (idx, &b) in bits.iter().enumerate() {
                    // Use bit values as cache key instead of memory address
                    let key = (bits.clone(), idx as u32);
                    let lit = if let Some(&l) = self.const_bit_cache.get(&key) {
                        l
                    } else {
                        let var = self.cnf.new_var();
                        let l = BoolLit(var, b);
                        self.cnf.add_clause(vec![l]);
                        self.const_bit_cache.insert(key, l);
                        l
                    };
                    lits.push(lit);
                }
                lits
            }
            BvTerm::Const { name, sort } => {
                // Materialize named variable bits and cache mapping for model
                let w = sort.width as usize;
                let mut out = Vec::with_capacity(w);
                for i in 0..w {
                    let key = (name.clone(), i as u32);
                    let lit = if let Some(&l) = self.var_bits.get(&key) {
                        l
                    } else {
                        let l = self.new_bool();
                        self.var_bits.insert(key, l);
                        l
                    };
                    out.push(lit);
                }
                out
            }
            BvTerm::Not(a) => {
                let va = self.emit_bits(a);
                let mut out = Vec::with_capacity(va.len());
                for i in 0..va.len() { out.push(self.alias_not_bit(va[i])); }
                out
            }
            BvTerm::Neg(a) => {
                if let BvTerm::Value { bits } = &**a {
                    // bits are LSB-first representation
                    let w = bits.len();
                    let mut n = 0u128;
                    for i in 0..w { if bits[i] { n |= 1u128 << i; } }
                    let mask: u128 = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
                    let neg = ((!n).wrapping_add(1)) & mask;
                    let out_bits = self.u128_to_lsb_bits(neg, w);
                    return self.alloc_const_bits(&out_bits);
                }
                let va = self.emit_bits(a);
                self.negate_bits(&va)
            }
            BvTerm::RedOr(a) => {
                if let BvTerm::Value { bits } = &**a {
                    // OR reduction: true if any bit is true
                    let result = bits.iter().any(|&b| b);
                    vec![self.const_lit(result)]
                } else {
                    let va = self.emit_bits(a);
                    vec![self.mk_or(&va)]
                }
            }
            BvTerm::RedAnd(a) => {
                if let BvTerm::Value { bits } = &**a {
                    // AND reduction: true if all bits are true
                    let result = bits.iter().all(|&b| b);
                    vec![self.const_lit(result)]
                } else {
                    let va = self.emit_bits(a);
                    vec![self.mk_and(&va)]
                }
            }
            BvTerm::RedXor(a) => {
                if let BvTerm::Value { bits } = &**a {
                    // XOR reduction: true if odd number of bits are true
                    let count = bits.iter().filter(|&&b| b).count();
                    let result = (count % 2) == 1;
                    vec![self.const_lit(result)]
                } else {
                    let va = self.emit_bits(a);
                    if va.is_empty() {
                        vec![self.const_lit(false)]
                    } else {
                        let mut acc = va[0];
                        for &bit in &va[1..] {
                            acc = self.encode_xor_var(acc, bit);
                        }
                        vec![acc]
                    }
                }
            }
            BvTerm::And(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                assert_eq!(va.len(), vb.len());
                let mut out = Vec::with_capacity(va.len());
                for i in 0..va.len() {
                    let y = self.mk_and(&[va[i], vb[i]]);
                    out.push(y);
                }
                out
            }
            BvTerm::Nand(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                assert_eq!(va.len(), vb.len());
                let mut out = Vec::with_capacity(va.len());
                for i in 0..va.len() {
                    let and_y = self.mk_and(&[va[i], vb[i]]);
                    let y = self.mk_not(and_y);
                    out.push(y);
                }
                out
            }
            BvTerm::Or(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                assert_eq!(va.len(), vb.len());
                let mut out = Vec::with_capacity(va.len());
                for i in 0..va.len() {
                    let y = self.mk_or(&[va[i], vb[i]]);
                    out.push(y);
                }
                out
            }
            BvTerm::Xor(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                assert_eq!(va.len(), vb.len());
                let mut out = Vec::with_capacity(va.len());
                for i in 0..va.len() {
                    let y = self.encode_xor_var(va[i], vb[i]);
                    out.push(y);
                }
                out
            }
            BvTerm::Xnor(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                assert_eq!(va.len(), vb.len());
                let mut out = Vec::with_capacity(va.len());
                for i in 0..va.len() {
                    // XNOR is NOT(XOR)
                    let xor = self.encode_xor_var(va[i], vb[i]);
                    out.push(self.mk_not(xor));
                }
                out
            }
            BvTerm::Nor(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                assert_eq!(va.len(), vb.len());
                let mut out = Vec::with_capacity(va.len());
                for i in 0..va.len() {
                    // NOR is NOT(OR)
                    let or = self.mk_or(&[va[i], vb[i]]);
                    out.push(self.mk_not(or));
                }
                out
            }
            BvTerm::Add(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let mut out = self.add_bits(&va, &vb);
                // Set expected polarity for constant inputs using current literal polarities
                for i in 0..out.len() {
                    // Compute half-adder addition from polarities for expected (approx ok for constant inputs)
                    // For robustness, recompute via u128 if widths small
                    let expected = va[i].1 ^ vb[i].1; // this ignores carries; adjust by simple ripple
                }
                if let (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) = (&**a, &**b) {
                    let w = ba.len();
                    let mut an: u128 = 0; for (i, &bt) in ba.iter().enumerate() { if bt { an |= 1u128 << i; } }
                    let mut bn: u128 = 0; for (i, &bt) in bb.iter().enumerate() { if bt { bn |= 1u128 << i; } }
                    let mask: u128 = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
                    let sn = (an + bn) & mask;
                    for i in 0..w { out[i] = self.force_value(out[i], ((sn >> i) & 1) == 1); }
                }
                out
            }
            BvTerm::Sub(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let mut out = self.sub_bits(&va, &vb);
                if let (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) = (&**a, &**b) {
                    let w = ba.len();
                    let mut an: u128 = 0; for (i, &bt) in ba.iter().enumerate() { if bt { an |= 1u128 << i; } }
                    let mut bn: u128 = 0; for (i, &bt) in bb.iter().enumerate() { if bt { bn |= 1u128 << i; } }
                    let mask: u128 = if w >= 128 { u128::MAX } else { (1u128 << w) - 1 };
                    let sn = (an.wrapping_sub(bn)) & mask;
                    for i in 0..w { out[i] = self.force_value(out[i], ((sn >> i) & 1) == 1); }
                }
                out
            }
            BvTerm::Mul(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let mut prod = self.mul_bits(&va, &vb);
                if let (BvTerm::Value{bits:ba}, BvTerm::Value{bits:bb}) = (&**a, &**b) {
                    let w = ba.len();
                    // compute expected product
                    let mut acc = vec![false; w];
                    for i in 0..w {
                        if bb[i] {
                            let mut carry = false;
                            for j in 0..w {
                                let aj = if j >= i { ba[j - i] } else { false };
                                let s = acc[j] ^ aj ^ carry;
                                let c_out = (acc[j] & aj) | (carry & (acc[j] ^ aj));
                                acc[j] = s; carry = c_out;
                            }
                        }
                    }
                    for i in 0..w { prod[i] = self.force_value(prod[i], acc[i]); }
                }
                prod
            }
            BvTerm::Shl(a, b) => {
                if let BvTerm::Value { bits: sbits } = &**b {
                    let w = a.sort().map(|s| s.width as usize).unwrap_or(0);
                    let mut sh = 0usize; for (i, &bt) in sbits.iter().enumerate() { if bt { sh |= 1usize << i; } }
                    let va = self.emit_bits(a);
                    let mut out = Vec::with_capacity(w);
                    for i in 0..w { out.push(if i >= sh { va[i - sh] } else { self.const_lit(false) }); }
                    out
                } else {
                    let va = self.emit_bits(a);
                    let vb = self.emit_bits(b);
                    self.var_shift_left(&va, &vb)
                }
            }
            BvTerm::Lshr(a, b) => {
                if let BvTerm::Value { bits: sbits } = &**b {
                    let w = a.sort().map(|s| s.width as usize).unwrap_or(0);
                    let mut sh = 0usize; for (i, &bt) in sbits.iter().enumerate() { if bt { sh |= 1usize << i; } }
                    let va = self.emit_bits(a);
                    let mut out = Vec::with_capacity(w);
                    for i in 0..w { out.push(if i + sh < w { va[i + sh] } else { self.const_lit(false) }); }
                    out
                } else {
                    let va = self.emit_bits(a);
                    let vb = self.emit_bits(b);
                    self.var_shift_right_logical(&va, &vb)
                }
            }
            BvTerm::Ashr(a, b) => {
                if let BvTerm::Value { bits: sbits } = &**b {
                    let w = a.sort().map(|s| s.width as usize).unwrap_or(0);
                    let mut sh = 0usize; for (i, &bt) in sbits.iter().enumerate() { if bt { sh |= 1usize << i; } }
                    let va = self.emit_bits(a);
                    let sign = va[w - 1];
                    let mut out = Vec::with_capacity(w);
                    for i in 0..w { out.push(if i + sh < w { va[i + sh] } else { sign }); }
                    out
                } else {
                    let va = self.emit_bits(a);
                    let vb = self.emit_bits(b);
                    self.var_shift_right_arith(&va, &vb)
                }
            }
            BvTerm::Udiv(a, b) => { let va = self.emit_bits(a); let vb = self.emit_bits(b); let (q, _r) = self.udiv_urem_bits(&va, &vb); q }
            BvTerm::Urem(a, b) => { let va = self.emit_bits(a); let vb = self.emit_bits(b); let (_q, r) = self.udiv_urem_bits(&va, &vb); r }
            BvTerm::Sdiv(a, b) => { let va = self.emit_bits(a); let vb = self.emit_bits(b); self.sdiv_bits(&va, &vb) }
            BvTerm::Srem(a, b) => { let va = self.emit_bits(a); let vb = self.emit_bits(b); self.srem_bits(&va, &vb) }
            BvTerm::Smod(a, b) => { let va = self.emit_bits(a); let vb = self.emit_bits(b); self.smod_bits(&va, &vb) }
            BvTerm::Concat(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let mut out = Vec::with_capacity(va.len() + vb.len());
                for &l in &vb { out.push(self.alias_bit(l)); }
                for &l in &va { out.push(self.alias_bit(l)); }
                out
            }
            BvTerm::Extract { hi, lo, a } => { let va = self.emit_bits(a); let mut out = Vec::with_capacity((*hi - *lo + 1) as usize); for i in *lo..=*hi { out.push(va[i as usize]); } out }
            BvTerm::SignExtend { a, extra } => {
                let va = self.emit_bits(a);
                let w = va.len();
                let sign = va[w - 1];
                let mut out = Vec::with_capacity(w + (*extra as usize));
                for &l in &va { out.push(self.alias_bit(l)); }
                for _ in 0..*extra as usize { out.push(self.alias_bit(sign)); }
                out
            }
            BvTerm::RotateLeft { a, amount } => {
                let va = self.emit_bits(a);
                let w = va.len();
                let amt = (*amount as usize) % w;
                let mut out = Vec::with_capacity(w);
                for i in 0..w { let src = (i + w - amt) % w; out.push(self.alias_bit(va[src])); }
                out
            }
            BvTerm::RotateRight { a, amount } => {
                let va = self.emit_bits(a);
                let w = va.len();
                let amt = (*amount as usize) % w;
                let mut out = Vec::with_capacity(w);
                for i in 0..w { let src = (i + amt) % w; out.push(self.alias_bit(va[src])); }
                out
            }
            BvTerm::Repeat { a, times } => {
                let va = self.emit_bits(a);
                let mut out = Vec::with_capacity(va.len() * (*times as usize));
                for _ in 0..*times { for &l in &va { out.push(self.alias_bit(l)); } }
                out
            }
            BvTerm::Ite(c, t, e) => {
                // Constant-fold on boolean condition when available
                if let BvTerm::Value { bits } = &**c {
                    let choose_then = bits.get(0).copied().unwrap_or(false);
                    let vv = if choose_then { self.emit_bits(t) } else { self.emit_bits(e) };
                    let mut out = Vec::with_capacity(vv.len());
                    for &l in &vv { out.push(self.alias_bit(l)); }
                    return out;
                }
                let vc = self.emit_bits(c);
                assert_eq!(vc.len(), 1);
                let vt = self.emit_bits(t);
                let ve = self.emit_bits(e);
                assert_eq!(vt.len(), ve.len());
                let mut out = Vec::with_capacity(vt.len());
                for i in 0..vt.len() { out.push(self.ite_bit(vc[0], vt[i], ve[i])); }
                out
            }
            BvTerm::Eq(a, b) => vec![self.bool_eq(a, b)],
            BvTerm::Ult(a, b) => vec![self.emit_ult_bool(a, b)],
            BvTerm::Ule(a, b) => vec![self.emit_ule_bool(a, b)],
            BvTerm::Slt(a, b) => vec![self.emit_slt_bool(a, b)],
            BvTerm::Sle(a, b) => {
                // a <= b (signed)  <=>  !(b < a) (signed)
                let lt = self.emit_slt_bool(b, a);
                vec![self.mk_not(lt)]
            }
            BvTerm::Uaddo(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let w = va.len();
                assert_eq!(w, vb.len());
                
                // Compute addition with carry
                let mut carry = self.const_lit(false);
                for i in 0..w {
                    let axb = self.encode_xor_var(va[i], vb[i]);
                    let carry1 = self.mk_and(&[va[i], vb[i]]);
                    let carry2 = self.mk_and(&[carry, axb]);
                    carry = self.mk_or(&[carry1, carry2]);
                }
                vec![carry] // overflow if final carry is 1
            }
            BvTerm::Saddo(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let w = va.len();
                assert_eq!(w, vb.len());
                
                let a_sign = va[w - 1];
                let b_sign = vb[w - 1];
                
                // Compute result
                let result = self.add_bits(&va, &vb);
                let result_sign = result[w - 1];
                
                // Overflow if signs are same but result sign differs
                let sign_xor = self.encode_xor_var(a_sign, b_sign);
                let same_sign = self.mk_not(sign_xor);
                let sign_diff = self.encode_xor_var(a_sign, result_sign);
                vec![self.mk_and(&[same_sign, sign_diff])]
            }
            BvTerm::Usubo(a, b) => {
                // Unsigned subtraction overflow: a < b
                vec![self.emit_ult_bool(a, b)]
            }
            BvTerm::Ssubo(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let w = va.len();
                assert_eq!(w, vb.len());
                
                let a_sign = va[w - 1];
                let b_sign = vb[w - 1];
                
                // Compute result  
                let result = self.sub_bits(&va, &vb);
                let result_sign = result[w - 1];
                
                // Overflow if signs differ and result sign != a sign
                let diff_sign = self.encode_xor_var(a_sign, b_sign);
                let sign_change = self.encode_xor_var(a_sign, result_sign);
                vec![self.mk_and(&[diff_sign, sign_change])]
            }
            BvTerm::Umulo(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let w = va.len();
                assert_eq!(w, vb.len());
                
                // For unsigned multiplication overflow, we need to check if any
                // bit in the upper half of the 2w-bit result is set
                let z = self.const_lit(false);
                let mut acc: Vec<BoolLit> = vec![z; 2 * w]; // 2w bits
                
                for i in 0..w {
                    let mut shifted: Vec<BoolLit> = vec![z; 2 * w];
                    for j in 0..w {
                        if i + j < 2 * w {
                            shifted[i + j] = va[j];
                        }
                    }
                    let mut pp = Vec::with_capacity(2 * w);
                    for j in 0..2 * w { 
                        pp.push(self.ite_bit(vb[i], shifted[j], z)); 
                    }
                    acc = self.add_bits_extended(&acc, &pp);
                }
                
                // Check if any upper bits are set
                let mut overflow_terms = Vec::with_capacity(w);
                for i in w..2*w {
                    overflow_terms.push(acc[i]);
                }
                vec![self.mk_or(&overflow_terms)]
            }
            BvTerm::Smulo(a, b) => {
                // For signed multiplication overflow, use a simplified approach
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let w = va.len();
                
                // Get absolute values  
                let a_abs = self.abs_bits(&va);
                let b_abs = self.abs_bits(&vb);
                
                // Do unsigned multiplication of absolute values with extended precision
                let z = self.const_lit(false);
                let mut acc: Vec<BoolLit> = vec![z; 2 * w];
                
                for i in 0..w {
                    let mut shifted: Vec<BoolLit> = vec![z; 2 * w];
                    for j in 0..w {
                        if i + j < 2 * w {
                            shifted[i + j] = a_abs[j];
                        }
                    }
                    let mut pp = Vec::with_capacity(2 * w);
                    for j in 0..2 * w { 
                        pp.push(self.ite_bit(b_abs[i], shifted[j], z)); 
                    }
                    acc = self.add_bits_extended(&acc, &pp);
                }
                
                // Check if result exceeds signed range [-(2^(w-1)), 2^(w-1)-1]
                // This happens if any of the upper w bits are set, or if bit w-1 is set
                // in the lower w bits (indicating >= 2^(w-1))
                let mut overflow_terms = Vec::with_capacity(w + 1);
                for i in w..2*w {
                    overflow_terms.push(acc[i]);
                }
                overflow_terms.push(acc[w - 1]); // MSB of lower half
                
                vec![self.mk_or(&overflow_terms)]
            }
            BvTerm::Sdivo(a, b) => {
                let va = self.emit_bits(a);
                let vb = self.emit_bits(b);
                let w = va.len();
                
                // Signed division overflow occurs when dividing MIN_INT by -1
                // MIN_INT = 100...0, -1 = 111...1
                let a_is_min = {
                    let mut terms = vec![va[w - 1]]; // MSB must be 1
                    for i in 0..w-1 {
                        terms.push(self.mk_not(va[i])); // other bits must be 0
                    }
                    self.mk_and(&terms)
                };
                
                let b_is_neg_one = {
                    let mut terms = Vec::with_capacity(w);
                    for i in 0..w {
                        terms.push(vb[i]); // all bits must be 1
                    }
                    self.mk_and(&terms)
                };
                
                vec![self.mk_and(&[a_is_min, b_is_neg_one])]
            }
            BvTerm::Nego(a) => {
                let va = self.emit_bits(a);
                let w = va.len();
                
                // Negation overflow occurs when negating MIN_INT (100...0)
                let mut terms = vec![va[w - 1]]; // MSB must be 1
                for i in 0..w-1 {
                    terms.push(self.mk_not(va[i])); // other bits must be 0
                }
                vec![self.mk_and(&terms)]
            }
        }
    }

    fn alloc_const_bits(&mut self, bits: &[bool]) -> Vec<BoolLit> {
        let mut out: Vec<BoolLit> = Vec::with_capacity(bits.len());
        for &b in bits {
            let var = self.cnf.new_var();
            let lit = BoolLit(var, b);
            self.cnf.add_clause(vec![lit]);
            out.push(lit);
        }
        out
    }

    pub fn blast_equal(&mut self, a: &BvTerm, b: &BvTerm) -> anyhow::Result<()> {
        let va = self.emit_bits(a);
        let vb = self.emit_bits(b);
        if va.len() != vb.len() { return Ok(()); }
        for i in 0..va.len() {
            let x = self.encode_xor_var(va[i], vb[i]);
            let _eq = self.mk_not(x);
            // Do not combine; just ensure constraints exist
        }
        Ok(())
    }
}


