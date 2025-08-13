use super::bv::{BvTerm};

/// Very small collection of local simplifications to keep CNF small.
pub fn simplify_bv(t: BvTerm) -> BvTerm {
    match t {
        BvTerm::Not(a) => match *a {
            BvTerm::Value { mut bits } => { for b in &mut bits { *b = !*b; } BvTerm::Value { bits } }
            other => BvTerm::Not(Box::new(other)),
        },
        BvTerm::Xor(a, b) => match (*a, *b) {
            (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                let mut out = Vec::with_capacity(ba.len());
                for i in 0..ba.len() { out.push(ba[i] ^ bb[i]); }
                BvTerm::Value { bits: out }
            }
            (a, b) => BvTerm::Xor(Box::new(a), Box::new(b)),
        },
        BvTerm::And(a, b) => match (*a, *b) {
            (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                let mut out = Vec::with_capacity(ba.len());
                for i in 0..ba.len() { out.push(ba[i] & bb[i]); }
                BvTerm::Value { bits: out }
            }
            (a, b) => BvTerm::And(Box::new(a), Box::new(b)),
        },
        BvTerm::Or(a, b) => match (*a, *b) {
            (BvTerm::Value { bits: ba }, BvTerm::Value { bits: bb }) => {
                let mut out = Vec::with_capacity(ba.len());
                for i in 0..ba.len() { out.push(ba[i] | bb[i]); }
                BvTerm::Value { bits: out }
            }
            (a, b) => BvTerm::Or(Box::new(a), Box::new(b)),
        },
        BvTerm::Add(a, b) => match (*a, *b) {
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
            (a, b) => BvTerm::Add(Box::new(a), Box::new(b)),
        },
        other => other,
    }
}


