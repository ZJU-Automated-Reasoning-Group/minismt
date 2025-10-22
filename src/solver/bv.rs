use std::collections::HashMap;

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
    Comp(Box<BvTerm>, Box<BvTerm>),  // bvcomp: returns 1-bit vector (1 if equal else 0)
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
            BvTerm::Comp(_, _) => Some(SortBv { width: 1 }),
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

/// Evaluates a BvTerm given a model (variable assignments).
/// Returns the bit vector result as a Vec<bool>, or an error if evaluation fails.
pub fn eval_term(term: &BvTerm, model: &HashMap<String, Vec<bool>>) -> anyhow::Result<Vec<bool>> {
    use anyhow::bail;
    
    match term {
        BvTerm::Value { bits } => Ok(bits.clone()),
        BvTerm::Const { name, sort } => {
            if let Some(bits) = model.get(name) {
                if bits.len() == sort.width as usize {
                    Ok(bits.clone())
                } else {
                    bail!("Model value for {} has wrong width: expected {}, got {}", name, sort.width, bits.len())
                }
            } else {
                // If not in model, default to all zeros
                Ok(vec![false; sort.width as usize])
            }
        }
        BvTerm::Not(a) => {
            let av = eval_term(a, model)?;
            Ok(av.iter().map(|&b| !b).collect())
        }
        BvTerm::Neg(a) => {
            let av = eval_term(a, model)?;
            Ok(bv_neg(&av))
        }
        BvTerm::RedOr(a) => {
            let av = eval_term(a, model)?;
            Ok(vec![av.iter().any(|&b| b)])
        }
        BvTerm::RedAnd(a) => {
            let av = eval_term(a, model)?;
            Ok(vec![av.iter().all(|&b| b)])
        }
        BvTerm::RedXor(a) => {
            let av = eval_term(a, model)?;
            let count = av.iter().filter(|&&b| b).count();
            Ok(vec![(count % 2) == 1])
        }
        BvTerm::And(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            if av.len() != bv.len() {
                bail!("And operands have different widths");
            }
            Ok(av.iter().zip(bv.iter()).map(|(&x, &y)| x && y).collect())
        }
        BvTerm::Nand(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            if av.len() != bv.len() {
                bail!("Nand operands have different widths");
            }
            Ok(av.iter().zip(bv.iter()).map(|(&x, &y)| !(x && y)).collect())
        }
        BvTerm::Or(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            if av.len() != bv.len() {
                bail!("Or operands have different widths");
            }
            Ok(av.iter().zip(bv.iter()).map(|(&x, &y)| x || y).collect())
        }
        BvTerm::Xor(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            if av.len() != bv.len() {
                bail!("Xor operands have different widths");
            }
            Ok(av.iter().zip(bv.iter()).map(|(&x, &y)| x != y).collect())
        }
        BvTerm::Xnor(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            if av.len() != bv.len() {
                bail!("Xnor operands have different widths");
            }
            Ok(av.iter().zip(bv.iter()).map(|(&x, &y)| x == y).collect())
        }
        BvTerm::Nor(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            if av.len() != bv.len() {
                bail!("Nor operands have different widths");
            }
            Ok(av.iter().zip(bv.iter()).map(|(&x, &y)| !(x || y)).collect())
        }
        BvTerm::Comp(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![av == bv])
        }
        BvTerm::Add(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_add(&av, &bv))
        }
        BvTerm::Sub(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_sub(&av, &bv))
        }
        BvTerm::Mul(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_mul(&av, &bv))
        }
        BvTerm::Shl(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_shl(&av, &bv))
        }
        BvTerm::Lshr(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_lshr(&av, &bv))
        }
        BvTerm::Ashr(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_ashr(&av, &bv))
        }
        BvTerm::Udiv(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_udiv(&av, &bv))
        }
        BvTerm::Urem(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_urem(&av, &bv))
        }
        BvTerm::Sdiv(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_sdiv(&av, &bv))
        }
        BvTerm::Srem(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_srem(&av, &bv))
        }
        BvTerm::Smod(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(bv_smod(&av, &bv))
        }
        BvTerm::Concat(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            let mut result = bv.clone();
            result.extend(av);
            Ok(result)
        }
        BvTerm::Extract { hi, lo, a } => {
            let av = eval_term(a, model)?;
            let lo = *lo as usize;
            let hi = *hi as usize;
            if hi >= av.len() || lo > hi {
                bail!("Extract out of bounds");
            }
            Ok(av[lo..=hi].to_vec())
        }
        BvTerm::SignExtend { a, extra } => {
            let av = eval_term(a, model)?;
            let sign_bit = av.last().copied().unwrap_or(false);
            let mut result = av.clone();
            result.extend(vec![sign_bit; *extra as usize]);
            Ok(result)
        }
        BvTerm::RotateLeft { a, amount } => {
            let av = eval_term(a, model)?;
            let n = av.len();
            if n == 0 { return Ok(av); }
            let rot = (*amount as usize) % n;
            let mut result = Vec::with_capacity(n);
            result.extend(&av[rot..]);
            result.extend(&av[..rot]);
            Ok(result)
        }
        BvTerm::RotateRight { a, amount } => {
            let av = eval_term(a, model)?;
            let n = av.len();
            if n == 0 { return Ok(av); }
            let rot = (*amount as usize) % n;
            let mut result = Vec::with_capacity(n);
            result.extend(&av[n-rot..]);
            result.extend(&av[..n-rot]);
            Ok(result)
        }
        BvTerm::Repeat { a, times } => {
            let av = eval_term(a, model)?;
            let mut result = Vec::new();
            for _ in 0..*times {
                result.extend(av.iter());
            }
            Ok(result)
        }
        BvTerm::Ite(cond, then_val, else_val) => {
            let cv = eval_term(cond, model)?;
            let cond_true = cv.len() > 0 && cv[0];
            if cond_true {
                eval_term(then_val, model)
            } else {
                eval_term(else_val, model)
            }
        }
        BvTerm::Eq(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![av == bv])
        }
        BvTerm::Ult(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_ult(&av, &bv)])
        }
        BvTerm::Ule(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_ule(&av, &bv)])
        }
        BvTerm::Slt(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_slt(&av, &bv)])
        }
        BvTerm::Sle(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_sle(&av, &bv)])
        }
        BvTerm::Uaddo(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_uaddo(&av, &bv)])
        }
        BvTerm::Saddo(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_saddo(&av, &bv)])
        }
        BvTerm::Usubo(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_usubo(&av, &bv)])
        }
        BvTerm::Ssubo(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_ssubo(&av, &bv)])
        }
        BvTerm::Umulo(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_umulo(&av, &bv)])
        }
        BvTerm::Smulo(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_smulo(&av, &bv)])
        }
        BvTerm::Sdivo(a, b) => {
            let av = eval_term(a, model)?;
            let bv = eval_term(b, model)?;
            Ok(vec![bv_sdivo(&av, &bv)])
        }
        BvTerm::Nego(a) => {
            let av = eval_term(a, model)?;
            Ok(vec![bv_nego(&av)])
        }
    }
}

// Helper functions for bit-vector operations
fn bv_neg(a: &[bool]) -> Vec<bool> {
    let result = a.iter().map(|&b| !b).collect::<Vec<_>>();
    let one = vec![true];
    bv_add(&result, &one)
}

fn bv_add(a: &[bool], b: &[bool]) -> Vec<bool> {
    let n = a.len().max(b.len());
    let mut result = Vec::with_capacity(n);
    let mut carry = false;
    for i in 0..n {
        let ai = a.get(i).copied().unwrap_or(false);
        let bi = b.get(i).copied().unwrap_or(false);
        let sum = ai ^ bi ^ carry;
        carry = (ai && bi) || (ai && carry) || (bi && carry);
        result.push(sum);
    }
    result.truncate(n);
    result
}

fn bv_sub(a: &[bool], b: &[bool]) -> Vec<bool> {
    bv_add(a, &bv_neg(b))
}

fn bv_mul(a: &[bool], b: &[bool]) -> Vec<bool> {
    let n = a.len();
    let mut result = vec![false; n];
    for i in 0..n {
        if b.get(i).copied().unwrap_or(false) {
            let shifted = bv_shl(a, &to_bits(i as u128, n));
            result = bv_add(&result, &shifted);
        }
    }
    result.truncate(n);
    result
}

fn bv_shl(a: &[bool], b: &[bool]) -> Vec<bool> {
    let shift = from_bits(b);
    let n = a.len();
    if shift >= n as u128 {
        return vec![false; n];
    }
    let shift = shift as usize;
    let mut result = vec![false; n];
    for i in shift..n {
        result[i] = a[i - shift];
    }
    result
}

fn bv_lshr(a: &[bool], b: &[bool]) -> Vec<bool> {
    let shift = from_bits(b);
    let n = a.len();
    if shift >= n as u128 {
        return vec![false; n];
    }
    let shift = shift as usize;
    let mut result = vec![false; n];
    for i in 0..(n - shift) {
        result[i] = a[i + shift];
    }
    result
}

fn bv_ashr(a: &[bool], b: &[bool]) -> Vec<bool> {
    let shift = from_bits(b);
    let n = a.len();
    let sign_bit = a.last().copied().unwrap_or(false);
    if shift >= n as u128 {
        return vec![sign_bit; n];
    }
    let shift = shift as usize;
    let mut result = vec![false; n];
    for i in 0..(n - shift) {
        result[i] = a[i + shift];
    }
    for i in (n - shift)..n {
        result[i] = sign_bit;
    }
    result
}

fn bv_udiv(a: &[bool], b: &[bool]) -> Vec<bool> {
    let n = a.len();
    let av = from_bits(a);
    let bv = from_bits(b);
    if bv == 0 {
        return vec![true; n]; // division by zero: all 1s
    }
    to_bits(av / bv, n)
}

fn bv_urem(a: &[bool], b: &[bool]) -> Vec<bool> {
    let n = a.len();
    let av = from_bits(a);
    let bv = from_bits(b);
    if bv == 0 {
        return a.to_vec(); // remainder by zero: return a
    }
    to_bits(av % bv, n)
}

fn bv_sdiv(a: &[bool], b: &[bool]) -> Vec<bool> {
    let n = a.len();
    let av = signed_from_bits(a);
    let bv = signed_from_bits(b);
    if bv == 0 {
        return if av >= 0 { vec![true; n] } else { vec![false; n-1].into_iter().chain(vec![true]).collect() };
    }
    signed_to_bits(av / bv, n)
}

fn bv_srem(a: &[bool], b: &[bool]) -> Vec<bool> {
    let n = a.len();
    let av = signed_from_bits(a);
    let bv = signed_from_bits(b);
    if bv == 0 {
        return a.to_vec();
    }
    signed_to_bits(av % bv, n)
}

fn bv_smod(a: &[bool], b: &[bool]) -> Vec<bool> {
    let n = a.len();
    let av = signed_from_bits(a);
    let bv = signed_from_bits(b);
    if bv == 0 {
        return a.to_vec();
    }
    let rem = av % bv;
    let result = if (rem < 0 && bv > 0) || (rem > 0 && bv < 0) {
        rem + bv
    } else {
        rem
    };
    signed_to_bits(result, n)
}

fn bv_ult(a: &[bool], b: &[bool]) -> bool {
    from_bits(a) < from_bits(b)
}

fn bv_ule(a: &[bool], b: &[bool]) -> bool {
    from_bits(a) <= from_bits(b)
}

fn bv_slt(a: &[bool], b: &[bool]) -> bool {
    signed_from_bits(a) < signed_from_bits(b)
}

fn bv_sle(a: &[bool], b: &[bool]) -> bool {
    signed_from_bits(a) <= signed_from_bits(b)
}

fn bv_uaddo(a: &[bool], b: &[bool]) -> bool {
    let n = a.len();
    let av = from_bits(a);
    let bv = from_bits(b);
    let sum = av + bv;
    sum >= (1 << n)
}

fn bv_saddo(a: &[bool], b: &[bool]) -> bool {
    let n = a.len();
    let av = signed_from_bits(a);
    let bv = signed_from_bits(b);
    let max_val = (1i128 << (n - 1)) - 1;
    let min_val = -(1i128 << (n - 1));
    let sum = av + bv;
    sum > max_val || sum < min_val
}

fn bv_usubo(a: &[bool], b: &[bool]) -> bool {
    from_bits(a) < from_bits(b)
}

fn bv_ssubo(a: &[bool], b: &[bool]) -> bool {
    let n = a.len();
    let av = signed_from_bits(a);
    let bv = signed_from_bits(b);
    let max_val = (1i128 << (n - 1)) - 1;
    let min_val = -(1i128 << (n - 1));
    let diff = av - bv;
    diff > max_val || diff < min_val
}

fn bv_umulo(a: &[bool], b: &[bool]) -> bool {
    let n = a.len();
    let av = from_bits(a);
    let bv = from_bits(b);
    let prod = av * bv;
    prod >= (1 << n)
}

fn bv_smulo(a: &[bool], b: &[bool]) -> bool {
    let n = a.len();
    let av = signed_from_bits(a);
    let bv = signed_from_bits(b);
    let max_val = (1i128 << (n - 1)) - 1;
    let min_val = -(1i128 << (n - 1));
    let prod = av * bv;
    prod > max_val || prod < min_val
}

fn bv_sdivo(a: &[bool], b: &[bool]) -> bool {
    let n = a.len();
    let av = signed_from_bits(a);
    let bv = signed_from_bits(b);
    let min_val = -(1i128 << (n - 1));
    av == min_val && bv == -1
}

fn bv_nego(a: &[bool]) -> bool {
    let n = a.len();
    let av = signed_from_bits(a);
    let min_val = -(1i128 << (n - 1));
    av == min_val
}

fn from_bits(bits: &[bool]) -> u128 {
    let mut result = 0u128;
    for (i, &bit) in bits.iter().enumerate() {
        if bit {
            result |= 1 << i;
        }
    }
    result
}

fn signed_from_bits(bits: &[bool]) -> i128 {
    if bits.is_empty() { return 0; }
    let n = bits.len();
    let unsigned = from_bits(bits);
    let sign_bit = bits[n - 1];
    if sign_bit {
        // Negative: compute two's complement
        (unsigned as i128) - (1i128 << n)
    } else {
        unsigned as i128
    }
}

fn to_bits(val: u128, width: usize) -> Vec<bool> {
    let mut result = Vec::with_capacity(width);
    for i in 0..width {
        result.push(((val >> i) & 1) == 1);
    }
    result
}

fn signed_to_bits(val: i128, width: usize) -> Vec<bool> {
    let mask = if width >= 128 { !0u128 } else { (1u128 << width) - 1 };
    to_bits((val as u128) & mask, width)
}
