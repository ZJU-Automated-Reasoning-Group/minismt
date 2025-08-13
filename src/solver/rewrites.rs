use super::bv::BvTerm;

pub fn simplify_bv(term: BvTerm) -> BvTerm {
    match term {
        BvTerm::Not(a) => match simplify_bv(*a) {
            BvTerm::Value { mut bits } => { for b in &mut bits { *b = !*b; } BvTerm::Value { bits } }
            x => BvTerm::Not(Box::new(x)),
        },
        BvTerm::And(a, b) => {
            let a = simplify_bv(*a);
            let b = simplify_bv(*b);
            match (&a, &b) {
                (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => BvTerm::Value { bits: bitand(va, vb) },
                (BvTerm::Value { bits }, x) | (x, BvTerm::Value { bits }) => {
                    if is_all_ones(bits) { x.clone() } else if is_all_zero(bits) { BvTerm::Value { bits: bits.clone() } } else { BvTerm::And(Box::new(a), Box::new(b)) }
                }
                _ => BvTerm::And(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Or(a, b) => {
            let a = simplify_bv(*a);
            let b = simplify_bv(*b);
            match (&a, &b) {
                (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => BvTerm::Value { bits: bitor(va, vb) },
                (BvTerm::Value { bits }, x) | (x, BvTerm::Value { bits }) => {
                    if is_all_zero(bits) { x.clone() } else if is_all_ones(bits) { BvTerm::Value { bits: bits.clone() } } else { BvTerm::Or(Box::new(a), Box::new(b)) }
                }
                _ => BvTerm::Or(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Xor(a, b) => {
            let a = simplify_bv(*a);
            let b = simplify_bv(*b);
            match (&a, &b) {
                (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => BvTerm::Value { bits: bitxor(va, vb) },
                (BvTerm::Value { bits }, x) | (x, BvTerm::Value { bits }) => {
                    if is_all_zero(bits) { x.clone() } else { BvTerm::Xor(Box::new(a), Box::new(b)) }
                }
                _ => BvTerm::Xor(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Add(a, b) => fold_add_like(BvTerm::Add, *a, *b),
        BvTerm::Sub(a, b) => fold_add_like(BvTerm::Sub, *a, *b),
        BvTerm::Mul(a, b) => fold_mul(*a, *b),
        BvTerm::Concat(a, b) => {
            let a = simplify_bv(*a);
            let b = simplify_bv(*b);
            match (&a, &b) {
                (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => {
                    let mut bits = vb.clone();
                    bits.extend_from_slice(va);
                    BvTerm::Value { bits }
                }
                _ => BvTerm::Concat(Box::new(a), Box::new(b)),
            }
        }
        BvTerm::Extract { hi, lo, a } => {
            let a = simplify_bv(*a);
            match a {
                BvTerm::Value { bits } => {
                    let mut out = Vec::new();
                    for i in lo..=hi { out.push(bits[i as usize]); }
                    BvTerm::Value { bits: out }
                }
                x => BvTerm::Extract { hi, lo, a: Box::new(x) },
            }
        }
        BvTerm::Shl(a, b) => fold_shift(true, *a, *b),
        BvTerm::Lshr(a, b) => fold_shift(false, *a, *b),
        BvTerm::Ashr(a, b) => fold_ashr(*a, *b),
        BvTerm::Udiv(a, b) => fold_udiv(*a, *b),
        BvTerm::Urem(a, b) => fold_urem(*a, *b),
        BvTerm::RotateLeft { a, amount } => {
            let a = simplify_bv(*a);
            match a {
                BvTerm::Value { bits } => BvTerm::Value { bits: rotl_bits(&bits, amount) },
                x => BvTerm::RotateLeft { a: Box::new(x), amount },
            }
        }
        BvTerm::RotateRight { a, amount } => {
            let a = simplify_bv(*a);
            match a {
                BvTerm::Value { bits } => BvTerm::Value { bits: rotr_bits(&bits, amount) },
                x => BvTerm::RotateRight { a: Box::new(x), amount },
            }
        }
        BvTerm::Repeat { a, times } => {
            let a = simplify_bv(*a);
            match a {
                BvTerm::Value { bits } => BvTerm::Value { bits: repeat_bits(&bits, times) },
                x => BvTerm::Repeat { a: Box::new(x), times },
            }
        }
        x => x,
    }
}

fn fold_add_like<F>(ctor: F, a: BvTerm, b: BvTerm) -> BvTerm
where F: Fn(Box<BvTerm>, Box<BvTerm>) -> BvTerm {
    let a = simplify_bv(a);
    let b = simplify_bv(b);
    match (&a, &b) {
        (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => BvTerm::Value { bits: add_bits(va, vb) },
        _ => ctor(Box::new(a), Box::new(b)),
    }
}

fn fold_mul(a: BvTerm, b: BvTerm) -> BvTerm {
    let a = simplify_bv(a);
    let b = simplify_bv(b);
    match (&a, &b) {
        (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => BvTerm::Value { bits: mul_bits(va, vb) },
        _ => BvTerm::Mul(Box::new(a), Box::new(b)),
    }
}

fn fold_shift(is_left: bool, a: BvTerm, b: BvTerm) -> BvTerm {
    let a = simplify_bv(a);
    let b = simplify_bv(b);
    match (&a, &b) {
        (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => {
            let shift = bits_to_u32(vb);
            if is_left { BvTerm::Value { bits: shl_bits(va, shift) } } else { BvTerm::Value { bits: lshr_bits(va, shift) } }
        }
        _ => if is_left { BvTerm::Shl(Box::new(a), Box::new(b)) } else { BvTerm::Lshr(Box::new(a), Box::new(b)) },
    }
}

fn bitand(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> { a.iter().zip(b).map(|(x,y)| *x && *y).collect() }
fn bitor(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> { a.iter().zip(b).map(|(x,y)| *x || *y).collect() }
fn bitxor(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> { a.iter().zip(b).map(|(x,y)| *x ^ *y).collect() }
fn is_all_zero(v: &Vec<bool>) -> bool { v.iter().all(|&x| !x) }
fn is_all_ones(v: &Vec<bool>) -> bool { v.iter().all(|&x| x) }

fn add_bits(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> {
    let n = a.len().max(b.len());
    let mut out = vec![false; n];
    let mut carry = false;
    for i in 0..n {
        let ai = *a.get(i).unwrap_or(&false);
        let bi = *b.get(i).unwrap_or(&false);
        let s = ai ^ bi ^ carry;
        carry = (ai & bi) | (ai & carry) | (bi & carry);
        out[i] = s;
    }
    out
}

fn mul_bits(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> {
    let n = a.len();
    let mut out = vec![false; n];
    for j in 0..n { if b.get(j).copied().unwrap_or(false) {
        out = add_bits(&out, &shift_left(a, j as u32));
    } }
    out
}

fn shift_left(a: &Vec<bool>, k: u32) -> Vec<bool> {
    let n = a.len();
    let mut out = vec![false; n];
    for i in (k as usize)..n { out[i] = a[i - k as usize]; }
    out
}
fn shl_bits(a: &Vec<bool>, k: u32) -> Vec<bool> { shift_left(a, k) }
fn lshr_bits(a: &Vec<bool>, k: u32) -> Vec<bool> {
    let n = a.len();
    let mut out = vec![false; n];
    for i in 0..n { let j = i + k as usize; out[i] = if j < n { a[j] } else { false }; }
    out
}

fn ashr_bits(a: &Vec<bool>, k: u32) -> Vec<bool> {
    let n = a.len();
    let mut out = vec![false; n];
    let sign = *a.get(n.saturating_sub(1)).unwrap_or(&false);
    for i in 0..n {
        let j = i + k as usize;
        out[i] = if j < n { a[j] } else { sign };
    }
    out
}

fn rotl_bits(a: &Vec<bool>, k: u32) -> Vec<bool> {
    let n = a.len();
    if n == 0 { return vec![]; }
    let r = (k as usize) % n;
    let mut out = vec![false; n];
    for i in 0..n { out[(i + r) % n] = a[i]; }
    out
}

fn rotr_bits(a: &Vec<bool>, k: u32) -> Vec<bool> {
    let n = a.len();
    if n == 0 { return vec![]; }
    let r = (k as usize) % n;
    let mut out = vec![false; n];
    for i in 0..n { out[i] = a[(i + r) % n]; }
    out
}

fn repeat_bits(a: &Vec<bool>, times: u32) -> Vec<bool> {
    let n = a.len();
    if n == 0 || times == 0 { return vec![]; }
    let mut out = Vec::with_capacity(n * times as usize);
    for _ in 0..times { out.extend_from_slice(a); }
    out
}

fn bits_to_u32(bits: &Vec<bool>) -> u32 {
    let mut x = 0u32;
    let upto = bits.len().min(32);
    for i in 0..upto { if bits[i] { x |= 1u32 << i; } }
    x
}

fn fold_udiv(a: BvTerm, b: BvTerm) -> BvTerm {
    let a = simplify_bv(a);
    let b = simplify_bv(b);
    match (&a, &b) {
        (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => {
            // Handle division by zero: udiv(x, 0) = 2^n - 1 (all ones)
            if is_all_zero(vb) {
                BvTerm::Value { bits: vec![true; va.len()] }
            } else {
                BvTerm::Value { bits: udiv_bits(va, vb) }
            }
        }
        // Division by zero: udiv(a, 0) = ones (SMT-LIB standard)
        (_, BvTerm::Value { bits }) if is_all_zero(bits) => {
            let width = a.sort().unwrap().width as usize;
            BvTerm::Value { bits: vec![true; width] }
        }
        // Division by one: udiv(a, 1) = a
        (_, BvTerm::Value { bits }) if is_one(bits) => a,
        // Division by all ones: udiv(a, 2^n-1) = (a == 2^n-1) ? 1 : 0
        (_, BvTerm::Value { bits }) if is_all_ones(bits) => {
            // For now, don't simplify this case to avoid complexity
            BvTerm::Udiv(Box::new(a), Box::new(b))
        }
        // Zero divided by anything non-zero: udiv(0, b) = 0
        (BvTerm::Value { bits }, _) if is_all_zero(bits) => {
            // Create conditional: b == 0 ? ones : 0
            let width = a.sort().unwrap().width as usize;
            let zero = BvTerm::Value { bits: vec![false; width] };
            let ones = BvTerm::Value { bits: vec![true; width] };
            let b_zero = BvTerm::Value { bits: vec![false; width] };
            BvTerm::Ite(
                Box::new(BvTerm::Eq(Box::new(b), Box::new(b_zero))),
                Box::new(ones),
                Box::new(zero)
            )
        }
        // Check for power-of-two division (can be optimized to right shift)
        (_, BvTerm::Value { bits }) if is_power_of_two(bits) => {
            let shift_amount = trailing_zeros(bits);
            let shift_bits = u32_to_bits(shift_amount, bits.len());
            BvTerm::Lshr(Box::new(a), Box::new(BvTerm::Value { bits: shift_bits }))
        }
        _ => BvTerm::Udiv(Box::new(a), Box::new(b)),
    }
}

fn fold_urem(a: BvTerm, b: BvTerm) -> BvTerm {
    let a = simplify_bv(a);
    let b = simplify_bv(b);
    match (&a, &b) {
        (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => {
            // Handle remainder by zero: urem(x, 0) = x
            if is_all_zero(vb) {
                a.clone()
            } else {
                BvTerm::Value { bits: urem_bits(va, vb) }
            }
        }
        // Remainder by zero: urem(a, 0) = a (SMT-LIB standard)
        (_, BvTerm::Value { bits }) if is_all_zero(bits) => a,
        // Remainder by one: urem(a, 1) = 0
        (_, BvTerm::Value { bits }) if is_one(bits) => {
            let width = a.sort().unwrap().width as usize;
            BvTerm::Value { bits: vec![false; width] }
        }
        // Zero remainder by anything: urem(0, b) = 0
        (BvTerm::Value { bits }, _) if is_all_zero(bits) => a,
        // Remainder by power of two: urem(a, 2^k) = a & (2^k - 1)
        (_, BvTerm::Value { bits }) if is_power_of_two(bits) => {
            let mut mask = bits.clone();
            // Create mask: 2^k - 1 (all bits below k-th bit set to 1)
            let k = trailing_zeros(bits) as usize;
            for i in 0..mask.len() {
                mask[i] = i < k;
            }
            BvTerm::And(Box::new(a), Box::new(BvTerm::Value { bits: mask }))
        }
        _ => BvTerm::Urem(Box::new(a), Box::new(b)),
    }
}

fn fold_ashr(a: BvTerm, b: BvTerm) -> BvTerm {
    let a = simplify_bv(a);
    let b = simplify_bv(b);
    match (&a, &b) {
        (BvTerm::Value { bits: va }, BvTerm::Value { bits: vb }) => {
            let shift = bits_to_u32(vb);
            BvTerm::Value { bits: ashr_bits(va, shift) }
        }
        _ => BvTerm::Ashr(Box::new(a), Box::new(b)),
    }
}

fn udiv_bits(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> {
    let n = a.len();
    let a_val = bits_to_u64(a);
    let b_val = bits_to_u64(b);
    if b_val == 0 {
        return vec![true; n]; // Division by zero returns all ones
    }
    let result = a_val / b_val;
    u64_to_bits(result, n)
}

fn urem_bits(a: &Vec<bool>, b: &Vec<bool>) -> Vec<bool> {
    let n = a.len();
    let a_val = bits_to_u64(a);
    let b_val = bits_to_u64(b);
    if b_val == 0 {
        return a.clone(); // Remainder by zero returns dividend
    }
    let result = a_val % b_val;
    u64_to_bits(result, n)
}

fn bits_to_u64(bits: &Vec<bool>) -> u64 {
    let mut x = 0u64;
    let upto = bits.len().min(64);
    for i in 0..upto { if bits[i] { x |= 1u64 << i; } }
    x
}

fn u64_to_bits(mut val: u64, width: usize) -> Vec<bool> {
    let mut bits = Vec::with_capacity(width);
    for _ in 0..width {
        bits.push((val & 1) == 1);
        val >>= 1;
    }
    bits
}

fn u32_to_bits(mut val: u32, width: usize) -> Vec<bool> {
    let mut bits = Vec::with_capacity(width);
    for _ in 0..width {
        bits.push((val & 1) == 1);
        val >>= 1;
    }
    bits
}

fn is_one(bits: &Vec<bool>) -> bool {
    if bits.is_empty() { return false; }
    bits[0] && bits[1..].iter().all(|&x| !x)
}

fn is_power_of_two(bits: &Vec<bool>) -> bool {
    let count = bits.iter().filter(|&&x| x).count();
    count == 1
}

fn trailing_zeros(bits: &Vec<bool>) -> u32 {
    for (i, &bit) in bits.iter().enumerate() {
        if bit { return i as u32; }
    }
    bits.len() as u32
}


