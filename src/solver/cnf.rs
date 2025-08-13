use anyhow::Result;
use std::collections::HashMap;

use super::bv::{BvTerm, BoolLit, Cnf};

#[derive(Debug, Clone)]
pub struct BitBlaster {
    pub cnf: Cnf,
    pub var_bits: HashMap<(String, u32), BoolLit>,
    pub bool_syms: HashMap<String, BoolLit>,
    divrem_cache: HashMap<(usize, usize), (String, String, u32)>,
}

impl BitBlaster {
    pub fn new() -> Self {
        Self {
            cnf: Cnf::default(),
            var_bits: HashMap::new(),
            bool_syms: HashMap::new(),
            divrem_cache: HashMap::new(),
        }
    }

    pub fn new_bit(&mut self) -> BoolLit {
        let v = self.cnf.new_var();
        BoolLit(v, true)
    }

    pub fn get_bool_sym<S: Into<String>>(&mut self, name: S) -> BoolLit {
        let key = name.into();
        if let Some(&l) = self.bool_syms.get(&key) { return l; }
        let l = self.new_bit();
        self.bool_syms.insert(key, l);
        l
    }

    pub fn blast_equal(&mut self, a: &BvTerm, b: &BvTerm) -> Result<()> {
        let w = a.sort().unwrap().width;
        assert_eq!(w, b.sort().unwrap().width);
        for i in 0..w {
            let la = self.emit_bit(a, i);
            let lb = self.emit_bit(b, i);
            // (¬la ∨ lb) ∧ (la ∨ ¬lb)
            self.cnf.add_clause(vec![BoolLit(la.0, !la.1), lb]);
            self.cnf.add_clause(vec![la, BoolLit(lb.0, !lb.1)]);
        }
        Ok(())
    }

    pub fn emit_ult_bool(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let w = a.sort().unwrap().width;
        let result = self.new_tmp();
        let mut clauses_for_result = Vec::new();
        
        for i in (0..w).rev() {
            let ai = self.emit_bit(a, i);
            let bi = self.emit_bit(b, i);
            
            let ai_0_bi_1 = self.new_tmp();
            // ai_0_bi_1 <-> (¬ai ∧ bi)
            self.cnf.add_clause(vec![ai, BoolLit(bi.0, !bi.1), ai_0_bi_1]);
            self.cnf.add_clause(vec![BoolLit(ai.0, !ai.1), BoolLit(ai_0_bi_1.0, !ai_0_bi_1.1)]);
            self.cnf.add_clause(vec![bi, BoolLit(ai_0_bi_1.0, !ai_0_bi_1.1)]);
            
            let higher_eq = if i == w - 1 {
                let always_true = self.new_tmp();
                self.cnf.add_clause(vec![always_true]);
                always_true
            } else {
                let higher_eq = self.new_tmp();
                let mut eq_constraints = Vec::new();
                for j in (i + 1)..w {
                    let aj = self.emit_bit(a, j);
                    let bj = self.emit_bit(b, j);
                    let eq_j = self.new_tmp();
                    // eq_j <-> (aj <-> bj)
                    self.cnf.add_clause(vec![BoolLit(aj.0, !aj.1), bj, BoolLit(eq_j.0, !eq_j.1)]);
                    self.cnf.add_clause(vec![aj, BoolLit(bj.0, !bj.1), BoolLit(eq_j.0, !eq_j.1)]);
                    self.cnf.add_clause(vec![BoolLit(aj.0, !aj.1), BoolLit(bj.0, !bj.1), eq_j]);
                    self.cnf.add_clause(vec![aj, bj, eq_j]);
                    eq_constraints.push(eq_j);
                }
                
                for &eq_j in &eq_constraints {
                    self.cnf.add_clause(vec![BoolLit(higher_eq.0, !higher_eq.1), eq_j]);
                }
                let mut clause = eq_constraints.iter().map(|&eq_j| BoolLit(eq_j.0, !eq_j.1)).collect::<Vec<_>>();
                clause.push(higher_eq);
                self.cnf.add_clause(clause);
                
                higher_eq
            };
            
            let contrib = self.new_tmp();
            self.cnf.add_clause(vec![BoolLit(ai_0_bi_1.0, !ai_0_bi_1.1), BoolLit(higher_eq.0, !higher_eq.1), contrib]);
            self.cnf.add_clause(vec![ai_0_bi_1, BoolLit(contrib.0, !contrib.1)]);
            self.cnf.add_clause(vec![higher_eq, BoolLit(contrib.0, !contrib.1)]);
            
            clauses_for_result.push(contrib);
        }
        
        for &contrib in &clauses_for_result {
            self.cnf.add_clause(vec![BoolLit(contrib.0, !contrib.1), result]);
        }
        let mut clause = clauses_for_result.iter().map(|&contrib| BoolLit(contrib.0, !contrib.1)).collect::<Vec<_>>();
        clause.push(BoolLit(result.0, !result.1));
        self.cnf.add_clause(clause);
        
        result
    }

    pub fn emit_ule_bool(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let lt = self.emit_ult_bool(b, a);
        BoolLit(lt.0, !lt.1)
    }

    pub fn emit_slt_bool(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let wa = a.sort().unwrap().width;
        let sign_a = self.emit_bit(a, wa - 1);
        let sign_b = self.emit_bit(b, wa - 1);
        let not_sign_b = BoolLit(sign_b.0, !sign_b.1);
        let diff_sign = self.new_tmp();
        self.cnf.add_clause(vec![BoolLit(sign_a.0, !sign_a.1), not_sign_b, diff_sign]);
        self.cnf.add_clause(vec![sign_a, BoolLit(diff_sign.0, !diff_sign.1)]);
        self.cnf.add_clause(vec![not_sign_b, BoolLit(diff_sign.0, !diff_sign.1)]);
        
        let xor = self.encode_xor_var(sign_a, sign_b);
        let same_sign = self.mk_not(xor);
        
        let a_mag = BvTerm::Extract { hi: wa - 2, lo: 0, a: Box::new(a.clone()) };
        let b_mag = BvTerm::Extract { hi: wa - 2, lo: 0, a: Box::new(b.clone()) };
        let mag_lt = self.emit_ult_bool(&a_mag, &b_mag);
        
        let conj = self.new_tmp();
        self.cnf.add_clause(vec![BoolLit(same_sign.0, !same_sign.1), BoolLit(mag_lt.0, !mag_lt.1), conj]);
        self.cnf.add_clause(vec![same_sign, BoolLit(conj.0, !conj.1)]);
        self.cnf.add_clause(vec![mag_lt, BoolLit(conj.0, !conj.1)]);
        
        let out = self.new_tmp();
        self.cnf.add_clause(vec![BoolLit(diff_sign.0, !diff_sign.1), out]);
        self.cnf.add_clause(vec![BoolLit(conj.0, !conj.1), out]);
        self.cnf.add_clause(vec![diff_sign, conj, BoolLit(out.0, !out.1)]);
        out
    }

    fn emit_shift_bit<F>(&mut self, a: &BvTerm, sh: &BvTerm, idx: u32, shift_fn: F) -> BoolLit 
    where F: Fn(&Vec<bool>, u32) -> Vec<bool> {
        let w = a.sort().unwrap().width;
        let mut src: Vec<BoolLit> = (0..w).map(|i| self.emit_bit(a, i)).collect();
        let sw = sh.sort().unwrap().width.min(32);
        
        for k in 0..sw {
            let sel = self.emit_bit(sh, k);
            let shift = 1u32 << k;
            let mut next = vec![self.new_tmp(); w as usize];
            
            for i in 0..w {
                let from = if shift_fn(&vec![true; w as usize], shift)[i as usize] { 
                    if i >= shift { src[(i - shift) as usize] } else { 
                        let z = self.new_tmp(); 
                        self.cnf.add_clause(vec![BoolLit(z.0, false)]); 
                        z 
                    }
                } else { 
                    if i + shift < w { src[(i + shift) as usize] } else { 
                        if shift_fn(&vec![true; w as usize], 0)[i as usize] { 
                            self.emit_bit(a, w - 1) 
                        } else { 
                            let z = self.new_tmp(); 
                            self.cnf.add_clause(vec![BoolLit(z.0, false)]); 
                            z 
                        }
                    }
                };
                
                let out = self.new_tmp();
                self.cnf.add_clause(vec![BoolLit(sel.0, !sel.1), BoolLit(from.0, !from.1), out]);
                self.cnf.add_clause(vec![sel, BoolLit(src[i as usize].0, !src[i as usize].1), out]);
                self.cnf.add_clause(vec![BoolLit(out.0, !out.1), sel, src[i as usize]]);
                self.cnf.add_clause(vec![BoolLit(out.0, !out.1), BoolLit(sel.0, !sel.1), from]);
                next[i as usize] = out;
            }
            src = next;
        }
        src[idx as usize]
    }

    pub fn emit_shl_bit(&mut self, a: &BvTerm, sh: &BvTerm, idx: u32) -> BoolLit {
        self.emit_shift_bit(a, sh, idx, |_, shift| vec![true; shift as usize])
    }

    pub fn emit_lshr_bit(&mut self, a: &BvTerm, sh: &BvTerm, idx: u32) -> BoolLit {
        self.emit_shift_bit(a, sh, idx, |_, _| vec![false; 0])
    }

    pub fn emit_ashr_bit(&mut self, a: &BvTerm, sh: &BvTerm, idx: u32) -> BoolLit {
        self.emit_shift_bit(a, sh, idx, |_, _| vec![true; 0])
    }

    pub fn emit_bit(&mut self, t: &BvTerm, idx: u32) -> BoolLit {
        match t {
            BvTerm::Value { bits } => {
                let var = self.cnf.new_var();
                let val = bits[idx as usize];
                let lit = BoolLit(var, val);
                self.cnf.add_clause(vec![lit]);
                lit
            }
            BvTerm::Const { name, sort: _ } => {
                let key = (name.clone(), idx);
                if let Some(&l) = self.var_bits.get(&key) { return l; }
                let l = self.new_bit();
                self.var_bits.insert(key, l);
                l
            }
            BvTerm::Not(a) => {
                let la = self.emit_bit(a, idx);
                if let BvTerm::Value { bits } = a.as_ref() {
                    let bit_value = !bits[idx as usize];
                    let var = self.cnf.new_var();
                    let lit = BoolLit(var, bit_value);
                    self.cnf.add_clause(vec![lit]);
                    return lit;
                }
                BoolLit(la.0, !la.1)
            }
            BvTerm::And(a, b) => {
                let la = self.emit_bit(a, idx);
                let lb = self.emit_bit(b, idx);
                
                if let (BvTerm::Value { bits: bits_a }, BvTerm::Value { bits: bits_b }) = (a.as_ref(), b.as_ref()) {
                    let result = bits_a[idx as usize] && bits_b[idx as usize];
                    let l = self.new_bit();
                    if result {
                        self.cnf.add_clause(vec![l]);
                    } else {
                        self.cnf.add_clause(vec![BoolLit(l.0, false)]);
                    }
                    return BoolLit(l.0, result);
                }
                
                let l = self.new_bit();
                self.cnf.add_clause(vec![BoolLit(la.0, !la.1), BoolLit(lb.0, !lb.1), l]);
                self.cnf.add_clause(vec![la, BoolLit(l.0, !l.1)]);
                self.cnf.add_clause(vec![lb, BoolLit(l.0, !l.1)]);
                l
            }
            BvTerm::Or(a, b) => {
                let l = self.new_bit();
                let la = self.emit_bit(a, idx);
                let lb = self.emit_bit(b, idx);
                self.cnf.add_clause(vec![la, lb, BoolLit(l.0, !l.1)]);
                self.cnf.add_clause(vec![BoolLit(la.0, !la.1), l]);
                self.cnf.add_clause(vec![BoolLit(lb.0, !lb.1), l]);
                l
            }
            BvTerm::Xor(a, b) => {
                let l = self.new_bit();
                let la = self.emit_bit(a, idx);
                let lb = self.emit_bit(b, idx);
                self.cnf.add_clause(vec![BoolLit(la.0, !la.1), BoolLit(lb.0, !lb.1), BoolLit(l.0, !l.1)]);
                self.cnf.add_clause(vec![la, lb, BoolLit(l.0, !l.1)]);
                self.cnf.add_clause(vec![la, BoolLit(lb.0, !lb.1), l]);
                self.cnf.add_clause(vec![BoolLit(la.0, !la.1), lb, l]);
                l
            }
            BvTerm::Add(a, b) => {
                let l = self.new_bit();
                let mut c = self.new_tmp();
                self.cnf.add_clause(vec![BoolLit(c.0, false)]);
                for i in 0..=idx {
                    let ai = self.emit_bit(a, i);
                    let bi = self.emit_bit(b, i);
                    let sumi = if i == idx { l } else { self.new_tmp() };
                    let carry_out = if i == idx { self.new_tmp() } else { self.new_tmp() };
                    self.encode_xor3(sumi, ai, bi, c);
                    self.encode_majority(carry_out, ai, bi, c);
                    c = carry_out;
                }
                l
            }
            BvTerm::Sub(a, b) => {
                let notb = BvTerm::Not(b.clone());
                let one = BvTerm::Value { bits: vec![true].into_iter().chain(std::iter::repeat(false)).take(a.sort().unwrap().width as usize).collect() };
                let add1 = BvTerm::Add(Box::new(notb), Box::new(one));
                let add = BvTerm::Add(a.clone(), Box::new(add1));
                self.emit_bit(&add, idx)
            }
            BvTerm::Mul(a, b) => {
                let width = a.sort().unwrap().width;
                let mut acc: Vec<BoolLit> = Vec::with_capacity((idx + 1) as usize);
                for _ in 0..=idx {
                    let z = self.new_tmp();
                    self.cnf.add_clause(vec![BoolLit(z.0, false)]);
                    acc.push(z);
                }
                
                let max_row = width.min(idx + 1);
                for j in 0..max_row {
                    let bj = self.emit_bit(b, j);
                    let mut row: Vec<BoolLit> = Vec::with_capacity((idx + 1) as usize);
                    for p in 0..=idx {
                        if p >= j {
                            let k = p - j;
                            if k < width {
                                let ai = self.emit_bit(a, k);
                                let term = self.new_tmp();
                                self.cnf.add_clause(vec![BoolLit(ai.0, !ai.1), BoolLit(bj.0, !bj.1), term]);
                                self.cnf.add_clause(vec![ai, BoolLit(term.0, !term.1)]);
                                self.cnf.add_clause(vec![bj, BoolLit(term.0, !term.1)]);
                                row.push(term);
                                continue;
                            }
                        }
                        let z = self.new_tmp();
                        self.cnf.add_clause(vec![BoolLit(z.0, false)]);
                        row.push(z);
                    }
                    
                    let mut carry = self.new_tmp();
                    self.cnf.add_clause(vec![BoolLit(carry.0, false)]);
                    for p in 0..=idx {
                        let sum_out = self.new_tmp();
                        let carry_out = if p == idx { self.new_tmp() } else { self.new_tmp() };
                        self.encode_xor3(sum_out, acc[p as usize], row[p as usize], carry);
                        self.encode_majority(carry_out, acc[p as usize], row[p as usize], carry);
                        acc[p as usize] = sum_out;
                        carry = carry_out;
                    }
                }
                acc[idx as usize]
            }
            BvTerm::Udiv(a, b) => {
                let (q_term, _r_term) = self.ensure_divrem(a, b);
                self.emit_bit(&q_term, idx)
            }
            BvTerm::Urem(a, b) => {
                let (_q_term, r_term) = self.ensure_divrem(a, b);
                self.emit_bit(&r_term, idx)
            }
            BvTerm::Concat(a, b) => {
                let bw = b.sort().unwrap().width;
                if idx < bw { 
                    let result_bit = self.emit_bit(b, idx);
                    if let BvTerm::Value { bits } = b.as_ref() {
                        let bit_value = bits[idx as usize];
                        return BoolLit(result_bit.0, bit_value);
                    }
                    result_bit
                } else { 
                    let result_bit = self.emit_bit(a, idx - bw);
                    if let BvTerm::Value { bits } = a.as_ref() {
                        let bit_value = bits[(idx - bw) as usize];
                        return BoolLit(result_bit.0, bit_value);
                    }
                    result_bit
                }
            }
            BvTerm::Extract { hi: _, lo, a } => {
                self.emit_bit(a, idx + *lo)
            }
            BvTerm::SignExtend { a, extra } => {
                let w = a.sort().unwrap().width;
                let sign = self.emit_bit(a, w - 1);
                if idx < w { self.emit_bit(a, idx) } else { sign }
            }
            BvTerm::RotateLeft { a, amount } => {
                let w = a.sort().unwrap().width;
                let k = amount % w;
                let src_idx = (idx + w - k) % w;
                self.emit_bit(a, src_idx)
            }
            BvTerm::RotateRight { a, amount } => {
                let w = a.sort().unwrap().width;
                let k = amount % w;
                let src_idx = (idx + k) % w;
                self.emit_bit(a, src_idx)
            }
            BvTerm::Repeat { a, times } => {
                let w = a.sort().unwrap().width;
                let src_idx = idx % w;
                self.emit_bit(a, src_idx)
            }
            BvTerm::Ite(c, t_then, t_else) => {
                let cond_lit = match &**c {
                    BvTerm::Eq(x, y) => {
                        let l = self.new_tmp();
                        let w = x.sort().unwrap().width;
                        let mut eq_bits = Vec::new();
                        for i in 0..w {
                            let xi = self.emit_bit(x, i);
                            let yi = self.emit_bit(y, i);
                            let eq_i = self.new_tmp();
                            self.cnf.add_clause(vec![BoolLit(eq_i.0, false), BoolLit(xi.0, !xi.1), yi]);
                            self.cnf.add_clause(vec![BoolLit(eq_i.0, false), xi, BoolLit(yi.0, !yi.1)]);
                            self.cnf.add_clause(vec![BoolLit(xi.0, !xi.1), BoolLit(yi.0, !yi.1), eq_i]);
                            self.cnf.add_clause(vec![xi, yi, eq_i]);
                            eq_bits.push(eq_i);
                        }
                        
                        for &eq_i in &eq_bits {
                            self.cnf.add_clause(vec![BoolLit(l.0, false), eq_i]);
                        }
                        let mut clause: Vec<BoolLit> = eq_bits.iter().map(|&eq_i| BoolLit(eq_i.0, false)).collect();
                        clause.push(l);
                        self.cnf.add_clause(clause);
                        
                        l
                    }
                    BvTerm::Ult(x, y) => self.emit_ult_bool(x, y),
                    BvTerm::Ule(x, y) => self.emit_ule_bool(x, y),
                    BvTerm::Slt(x, y) => self.emit_slt_bool(x, y),
                    BvTerm::Sle(x, y) => {
                        let lt = self.emit_slt_bool(x, y);
                        let eq = self.bool_eq(x, y);
                        self.mk_or(&[lt, eq])
                    }
                    _ => { let l = self.new_tmp(); l }
                };
                let ti = self.emit_bit(t_then, idx);
                let ei = self.emit_bit(t_else, idx);
                let out = self.new_tmp();
                self.cnf.add_clause(vec![BoolLit(cond_lit.0, !cond_lit.1), BoolLit(ti.0, !ti.1), out]);
                self.cnf.add_clause(vec![cond_lit, BoolLit(ei.0, !ei.1), out]);
                self.cnf.add_clause(vec![BoolLit(out.0, !out.1), cond_lit, ei]);
                self.cnf.add_clause(vec![BoolLit(out.0, !out.1), BoolLit(cond_lit.0, !cond_lit.1), ti]);
                out
            }
            BvTerm::Shl(a, b) => { self.emit_shl_bit(a, b, idx) }
            BvTerm::Lshr(a, b) => { self.emit_lshr_bit(a, b, idx) }
            BvTerm::Ashr(a, b) => { self.emit_ashr_bit(a, b, idx) }
            BvTerm::Neg(a) => {
                let one = BvTerm::Value { bits: vec![true].into_iter().chain(std::iter::repeat(false)).take(a.sort().unwrap().width as usize).collect() };
                let not_a = BvTerm::Not(a.clone());
                let add = BvTerm::Add(Box::new(not_a), Box::new(one));
                self.emit_bit(&add, idx)
            }
            BvTerm::Eq(_, _) | BvTerm::Ult(_, _) | BvTerm::Ule(_, _) | BvTerm::Slt(_, _) | BvTerm::Sle(_, _) => {
                panic!("Boolean operations should not be handled in emit_bit")
            }
        }
    }

    fn ptr_id(t: &BvTerm) -> usize { t as *const _ as usize }

    fn ensure_divrem(&mut self, a: &BvTerm, b: &BvTerm) -> (BvTerm, BvTerm) {
        let key = (Self::ptr_id(a), Self::ptr_id(b));
        let w = a.sort().unwrap().width;
        if let Some((qname, rname, _)) = self.divrem_cache.get(&key) {
            let q = BvTerm::Const { name: qname.clone(), sort: super::bv::SortBv { width: w } };
            let r = BvTerm::Const { name: rname.clone(), sort: super::bv::SortBv { width: w } };
            return (q, r);
        }
        let qname = format!("__udiv_q_{}_{}", key.0, key.1);
        let rname = format!("__udiv_r_{}_{}", key.0, key.1);
        self.divrem_cache.insert(key, (qname.clone(), rname.clone(), w));
        let q = BvTerm::Const { name: qname.clone(), sort: super::bv::SortBv { width: w } };
        let r = BvTerm::Const { name: rname.clone(), sort: super::bv::SortBv { width: w } };
        
        let width = w;
        let zero_bits = BvTerm::Value { bits: vec![false; width as usize] };
        let z = self.bool_eq(b, &zero_bits);
        let ones_bits = BvTerm::Value { bits: vec![true; width as usize] };
        
        {
            let mut eq_q_clauses_before = self.cnf.clauses.len();
            let _ = self.blast_equal(&q, &ones_bits).unwrap();
            let eq_q_range = eq_q_clauses_before..self.cnf.clauses.len();
            for i in eq_q_range {
                let mut clause = self.cnf.clauses[i].clone();
                clause.push(BoolLit(z.0, !z.1));
                self.cnf.clauses[i] = clause;
            }
            let mut eq_r_clauses_before = self.cnf.clauses.len();
            let _ = self.blast_equal(&r, a).unwrap();
            let eq_r_range = eq_r_clauses_before..self.cnf.clauses.len();
            for i in eq_r_range {
                let mut clause = self.cnf.clauses[i].clone();
                clause.push(BoolLit(z.0, !z.1));
                self.cnf.clauses[i] = clause;
            }
        }
        
        let nz = self.mk_not(z);
        {
            let mul = BvTerm::Mul(Box::new(b.clone()), Box::new(q.clone()));
            let sum = BvTerm::Add(Box::new(mul), Box::new(r.clone()));
            let before = self.cnf.clauses.len();
            let _ = self.blast_equal(&sum, a).unwrap();
            let range = before..self.cnf.clauses.len();
            for i in range {
                let mut clause = self.cnf.clauses[i].clone();
                clause.push(nz);
                self.cnf.clauses[i] = clause;
            }
            let lt = self.emit_ult_bool(&r, b);
            self.cnf.add_clause(vec![BoolLit(nz.0, !nz.1), lt]);
        }
        
        (q, r)
    }

    pub fn new_tmp(&mut self) -> BoolLit { self.new_bit() }
    pub fn new_bool(&mut self) -> BoolLit { self.new_bit() }
    pub fn mk_not(&mut self, l: BoolLit) -> BoolLit { BoolLit(l.0, !l.1) }

    pub fn mk_and(&mut self, inputs: &[BoolLit]) -> BoolLit {
        let out = self.new_bool();
        for &inp in inputs {
            self.cnf.add_clause(vec![BoolLit(out.0, !out.1), inp]);
        }
        let mut clause: Vec<BoolLit> = inputs.iter().map(|&l| BoolLit(l.0, !l.1)).collect();
        clause.push(out);
        self.cnf.add_clause(clause);
        out
    }

    pub fn mk_or(&mut self, inputs: &[BoolLit]) -> BoolLit {
        let out = self.new_bool();
        for &inp in inputs {
            self.cnf.add_clause(vec![BoolLit(inp.0, !inp.1), out]);
        }
        let mut clause = inputs.to_vec();
        clause.push(BoolLit(out.0, !out.1));
        self.cnf.add_clause(clause);
        out
    }

    pub fn bool_eq(&mut self, a: &BvTerm, b: &BvTerm) -> BoolLit {
        let w = a.sort().unwrap().width;
        let mut diffs: Vec<BoolLit> = Vec::with_capacity(w as usize);
        for i in 0..w {
            let ai = self.emit_bit(a, i);
            let bi = self.emit_bit(b, i);
            let d = self.encode_xor_var(ai, bi);
            diffs.push(d);
        }
        let any_diff = if diffs.is_empty() { 
            let z = self.new_bool(); 
            self.cnf.add_clause(vec![BoolLit(z.0, false)]); 
            z 
        } else { 
            self.mk_or(&diffs) 
        };
        self.mk_not(any_diff)
    }

    pub fn encode_xor_var(&mut self, a: BoolLit, b: BoolLit) -> BoolLit {
        let out = self.new_tmp();
        self.encode_xor(out, a, b);
        out
    }

    pub fn encode_xor(&mut self, out: BoolLit, a: BoolLit, b: BoolLit) {
        self.cnf.add_clause(vec![BoolLit(a.0, !a.1), BoolLit(b.0, !b.1), BoolLit(out.0, !out.1)]);
        self.cnf.add_clause(vec![a, b, BoolLit(out.0, !out.1)]);
        self.cnf.add_clause(vec![a, BoolLit(b.0, !b.1), out]);
        self.cnf.add_clause(vec![BoolLit(a.0, !a.1), b, out]);
    }

    fn encode_xor3(&mut self, out: BoolLit, a: BoolLit, b: BoolLit, c: BoolLit) {
        let t = self.new_tmp();
        self.encode_xor(t, a, b);
        self.encode_xor(out, t, c);
    }

    fn encode_majority(&mut self, out: BoolLit, a: BoolLit, b: BoolLit, c: BoolLit) {
        self.cnf.add_clause(vec![BoolLit(a.0, !a.1), BoolLit(b.0, !b.1), out]);
        self.cnf.add_clause(vec![BoolLit(a.0, !a.1), BoolLit(c.0, !c.1), out]);
        self.cnf.add_clause(vec![BoolLit(b.0, !b.1), BoolLit(c.0, !c.1), out]);
        self.cnf.add_clause(vec![a, b, BoolLit(out.0, !out.1)]);
        self.cnf.add_clause(vec![a, c, BoolLit(out.0, !out.1)]);
        self.cnf.add_clause(vec![b, c, BoolLit(out.0, !out.1)]);
    }
}


