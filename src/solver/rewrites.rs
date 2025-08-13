use super::bv::{BvTerm};

/// Very small collection of local simplifications to keep CNF small.
pub fn simplify_bv(t: BvTerm) -> BvTerm {
    match t {
        BvTerm::Not(a) => {
            let a_s = simplify_bv(*a);
            match a_s {
                BvTerm::Value { mut bits } => { for b in &mut bits { *b = !*b; } BvTerm::Value { bits } }
                // ~~x -> x
                BvTerm::Not(inner) => simplify_bv(*inner),
                BvTerm::Concat(h, l) => {
                    // ~(concat h l) -> concat (~h) (~l)
                    let nh = simplify_bv(BvTerm::Not(h));
                    let nl = simplify_bv(BvTerm::Not(l));
                    BvTerm::Concat(Box::new(nh), Box::new(nl))
                }
                other => BvTerm::Not(Box::new(other)),
            }
        }
        BvTerm::Xor(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            match (a_s, b_s) {
                (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                    let mut out = Vec::with_capacity(ba.len());
                    for i in 0..ba.len() { out.push(ba[i] ^ bb[i]); }
                    BvTerm::Value { bits: out }
                }
                // x ^ 0 -> x ; 0 ^ x -> x
                (BvTerm::Value { ref bits }, y) if bits.iter().all(|&b| !b) => y,
                (y, BvTerm::Value { ref bits }) if bits.iter().all(|&b| !b) => y,
                // x ^ all1 -> ~x ; all1 ^ x -> ~x
                (BvTerm::Value { ref bits }, y) if bits.iter().all(|&b| b) => simplify_bv(BvTerm::Not(Box::new(y))),
                (y, BvTerm::Value { ref bits }) if bits.iter().all(|&b| b) => simplify_bv(BvTerm::Not(Box::new(y))),
                // x ^ x -> 0
                (a1, b1) if a1 == b1 => { let w = a1.sort().map(|s| s.width as usize).unwrap_or(1); BvTerm::Value { bits: vec![false; w] } }
                (a, b) => BvTerm::Xor(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::And(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            match (a_s, b_s) {
                (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                    let mut out = Vec::with_capacity(ba.len());
                    for i in 0..ba.len() { out.push(ba[i] & bb[i]); }
                    BvTerm::Value { bits: out }
                }
                // x & 0 -> 0 ; 0 & x -> 0
                (BvTerm::Value { ref bits }, _) if bits.iter().all(|&b| !b) => BvTerm::Value { bits: vec![false; bits.len()] },
                (_, BvTerm::Value { ref bits }) if bits.iter().all(|&b| !b) => BvTerm::Value { bits: vec![false; bits.len()] },
                // x & all1 -> x ; all1 & x -> x
                (BvTerm::Value { ref bits }, x) if bits.iter().all(|&b| b) => x,
                (x, BvTerm::Value { ref bits }) if bits.iter().all(|&b| b) => x,
                // x & x -> x
                (a1, b1) if a1 == b1 => a1,
                (BvTerm::Concat(ah, al), BvTerm::Concat(bh, bl)) => {
                    // (concat ah al) & (concat bh bl) -> concat (ah & bh) (al & bl)
                    let high = simplify_bv(BvTerm::And(ah, bh));
                    let low = simplify_bv(BvTerm::And(al, bl));
                    BvTerm::Concat(Box::new(high), Box::new(low))
                }
                (a, b) => BvTerm::And(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Or(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            match (a_s, b_s) {
                (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                    let mut out = Vec::with_capacity(ba.len());
                    for i in 0..ba.len() { out.push(ba[i] | bb[i]); }
                    BvTerm::Value { bits: out }
                }
                // x | 0 -> x ; 0 | x -> x
                (BvTerm::Value { ref bits }, x) if bits.iter().all(|&b| !b) => x,
                (x, BvTerm::Value { ref bits }) if bits.iter().all(|&b| !b) => x,
                // x | all1 -> all1 ; all1 | x -> all1
                (BvTerm::Value { ref bits }, _x) if bits.iter().all(|&b| b) => BvTerm::Value { bits: vec![true; bits.len()] },
                (_x, BvTerm::Value { ref bits }) if bits.iter().all(|&b| b) => BvTerm::Value { bits: vec![true; bits.len()] },
                // x | x -> x
                (a1, b1) if a1 == b1 => a1,
                (BvTerm::Concat(ah, al), BvTerm::Concat(bh, bl)) => {
                    // (concat ah al) | (concat bh bl) -> concat (ah | bh) (al | bl)
                    let high = simplify_bv(BvTerm::Or(ah, bh));
                    let low = simplify_bv(BvTerm::Or(al, bl));
                    BvTerm::Concat(Box::new(high), Box::new(low))
                }
                (a, b) => BvTerm::Or(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Add(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            match (a_s, b_s) {
                (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                    // constant add in small bit-vector domain
                    let w = ba.len();
                    let mut out = Vec::with_capacity(w);
                    let mut carry = false;
                    for i in 0..w {
                        let s = ba[i] ^ bb[i] ^ carry;
                        let carry_out = (ba[i] & bb[i]) | (carry & (ba[i] ^ bb[i]));
                        out.push(s);
                        carry = carry_out;
                    }
                    BvTerm::Value { bits: out }
                }
                // x + 0 -> x ; 0 + x -> x
                (BvTerm::Value { ref bits }, x) if bits.iter().all(|&b| !b) => x,
                (x, BvTerm::Value { ref bits }) if bits.iter().all(|&b| !b) => x,
                // x + (-x) -> 0 ; (-x) + x -> 0
                (a1, BvTerm::Neg(b1)) | (BvTerm::Neg(b1), a1) if a1 == *b1 => { let w = a1.sort().map(|s| s.width as usize).unwrap_or(1); BvTerm::Value { bits: vec![false; w] } }
                (a, b) => BvTerm::Add(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Concat(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            match (a_s, b_s) {
                (BvTerm::Value { bits: ah }, BvTerm::Value { bits: bl }) => {
                    // LSB-first: result low bits come from bl, then ah
                    let mut out = Vec::with_capacity(ah.len() + bl.len());
                    out.extend_from_slice(&bl);
                    out.extend_from_slice(&ah);
                    BvTerm::Value { bits: out }
                }
                // concat (concat a b) c -> concat a (concat b c)
                (BvTerm::Concat(ah, al), c) => {
                    simplify_bv(BvTerm::Concat(ah, Box::new(BvTerm::Concat(al, Box::new(c)))))
                }
                // concat a (concat b c) -> concat (concat a b) c
                (a, BvTerm::Concat(bh, bl)) => {
                    simplify_bv(BvTerm::Concat(Box::new(BvTerm::Concat(Box::new(a), bh)), bl))
                }
                (a, b) => BvTerm::Concat(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Sub(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            match (a_s, b_s) {
                (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                    let w = ba.len();
                    let mut out = Vec::with_capacity(w);
                    let mut borrow = false;
                    for i in 0..w {
                        let ai = ba[i];
                        let bi = bb[i];
                        let s = ai ^ bi ^ borrow;
                        let borrow_out = (!ai & (bi | borrow)) | (bi & borrow);
                        out.push(s);
                        borrow = borrow_out;
                    }
                    BvTerm::Value { bits: out }
                }
                // x - 0 -> x
                (x, BvTerm::Value { ref bits }) if bits.iter().all(|&b| !b) => x,
                // x - x -> 0
                (a1, b1) if a1 == b1 => { let w = a1.sort().map(|s| s.width as usize).unwrap_or(1); BvTerm::Value { bits: vec![false; w] } }
                (a1, b1) => BvTerm::Sub(Box::new(a1), Box::new(b1)),
            }
        }
        BvTerm::Mul(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            match (a_s, b_s) {
                (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                    let w = ba.len();
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
                    BvTerm::Value { bits: acc }
                }
                // x * 0 -> 0 ; 0 * x -> 0
                (BvTerm::Value { ref bits }, _) if bits.iter().all(|&b| !b) => BvTerm::Value { bits: vec![false; bits.len()] },
                (_, BvTerm::Value { ref bits }) if bits.iter().all(|&b| !b) => BvTerm::Value { bits: vec![false; bits.len()] },
                // x * 1 -> x ; 1 * x -> x
                (BvTerm::Value { ref bits }, x) if bits.iter().enumerate().all(|(i, &bt)| if i == 0 { bt } else { !bt }) => x,
                (x, BvTerm::Value { ref bits }) if bits.iter().enumerate().all(|(i, &bt)| if i == 0 { bt } else { !bt }) => x,
                (a1, b1) => BvTerm::Mul(Box::new(a1), Box::new(b1)),
            }
        }
        BvTerm::Shl(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            if let BvTerm::Value { ref bits } = b_s { if bits.iter().all(|&bt| !bt) { return a_s; } }
            BvTerm::Shl(Box::new(a_s), Box::new(b_s))
        }
        BvTerm::Lshr(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            if let BvTerm::Value { ref bits } = b_s { if bits.iter().all(|&bt| !bt) { return a_s; } }
            BvTerm::Lshr(Box::new(a_s), Box::new(b_s))
        }
        BvTerm::Ashr(a, b) => {
            let a_s = simplify_bv(*a);
            let b_s = simplify_bv(*b);
            if let BvTerm::Value { ref bits } = b_s { if bits.iter().all(|&bt| !bt) { return a_s; } }
            BvTerm::Ashr(Box::new(a_s), Box::new(b_s))
        }
        other => other,
    }
}


