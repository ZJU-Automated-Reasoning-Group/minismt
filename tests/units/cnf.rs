use minismt::solver::cnf::BitBlaster;
use minismt::solver::bv::{BvTerm, SortBv};

#[test]
fn test_bitblaster_new() {
    let bb = BitBlaster::new();
    assert_eq!(bb.cnf.num_vars, 0);
    assert_eq!(bb.cnf.clauses.len(), 0);
    assert_eq!(bb.var_bits.len(), 0);
    assert_eq!(bb.bool_syms.len(), 0);
}

#[test]
fn test_new_bit() {
    let mut bb = BitBlaster::new();
    let bit1 = bb.new_bit();
    let bit2 = bb.new_bit();
    
    assert_eq!(bb.cnf.num_vars, 2);
    assert_eq!(bit1.0, 0);
    assert_eq!(bit2.0, 1);
    assert!(bit1.1); // polarity should be true
    assert!(bit2.1);
}

#[test]
fn test_get_bool_sym() {
    let mut bb = BitBlaster::new();
    
    // First call should create new symbol
    let sym1 = bb.get_bool_sym("x");
    assert_eq!(bb.cnf.num_vars, 1);
    assert_eq!(sym1.0, 0);
    
    // Second call should return same symbol
    let sym2 = bb.get_bool_sym("x");
    assert_eq!(sym1, sym2);
    assert_eq!(bb.cnf.num_vars, 1); // No new variable created
    
    // Different name should create new symbol
    let sym3 = bb.get_bool_sym("y");
    assert_eq!(bb.cnf.num_vars, 2);
    assert_eq!(sym3.0, 1);
}

#[test]
fn test_lookup_bool_sym() {
    let mut bb = BitBlaster::new();
    
    // Initially no symbols exist
    assert_eq!(bb.lookup_bool_sym("x"), None);
    
    // After creating symbol, it should be found
    let sym = bb.get_bool_sym("x");
    assert_eq!(bb.lookup_bool_sym("x"), Some(sym));
    
    // Non-existent symbol should return None
    assert_eq!(bb.lookup_bool_sym("y"), None);
}

#[test]
fn test_blast_equal() {
    let mut bb = BitBlaster::new();
    
    // Create two 4-bit constants
    let a = BvTerm::Value { bits: vec![true, false, true, false] };
    let b = BvTerm::Value { bits: vec![true, false, true, false] };
    
    bb.blast_equal(&a, &b).unwrap();
    
    // Should have created variables for each bit comparison
    // 4 bits * 2 variables per bit = 8 variables
    // Plus 4 equality constraints = 8 clauses
    assert!(bb.cnf.num_vars >= 8);
    assert!(bb.cnf.clauses.len() >= 8);
}

#[test]
fn test_emit_ult_bool() {
    let mut bb = BitBlaster::new();
    
    // Create two 4-bit constants: 5 < 7
    let a = BvTerm::Value { bits: vec![true, false, true, false] }; // 5
    let b = BvTerm::Value { bits: vec![true, true, true, false] };  // 7
    
    let result = bb.emit_ult_bool(&a, &b);
    
    // Should have created variables and constraints
    assert!(bb.cnf.num_vars > 0);
    assert!(bb.cnf.clauses.len() > 0);
    
    // Result should be a valid boolean literal
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_emit_ule_bool() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false, true, false] }; // 5
    let b = BvTerm::Value { bits: vec![true, false, true, false] }; // 5
    
    let result = bb.emit_ule_bool(&a, &b);
    
    assert!(bb.cnf.num_vars > 0);
    assert!(bb.cnf.clauses.len() > 0);
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_emit_slt_bool() {
    let mut bb = BitBlaster::new();
    
    // Create two 4-bit signed numbers: -3 < 2
    let a = BvTerm::Value { bits: vec![true, false, false, true] }; // -3
    let b = BvTerm::Value { bits: vec![false, true, false, false] }; // 2
    
    let result = bb.emit_slt_bool(&a, &b);
    
    assert!(bb.cnf.num_vars > 0);
    assert!(bb.cnf.clauses.len() > 0);
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_emit_bit_value() {
    let mut bb = BitBlaster::new();
    
    let term = BvTerm::Value { bits: vec![true, false, true] };
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    let bit2 = bb.emit_bit(&term, 2);
    
    // Should create variables for each bit
    assert_eq!(bb.cnf.num_vars, 3);
    
    // Each bit should have a clause enforcing its value
    assert_eq!(bb.cnf.clauses.len(), 3);
    
    // Check that the clauses enforce the correct values
    assert!(bb.cnf.clauses.iter().any(|clause| {
        clause.len() == 1 && clause[0] == bit0 && clause[0].1 == true
    }));
    assert!(bb.cnf.clauses.iter().any(|clause| {
        clause.len() == 1 && clause[0] == bit1 && clause[0].1 == false
    }));
    assert!(bb.cnf.clauses.iter().any(|clause| {
        clause.len() == 1 && clause[0] == bit2 && clause[0].1 == true
    }));
}

#[test]
fn test_emit_bit_const() {
    let mut bb = BitBlaster::new();
    
    let sort = SortBv { width: 4 };
    let term = BvTerm::Const { name: "x".to_string(), sort };
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables for each bit
    assert_eq!(bb.cnf.num_vars, 2);
    
    // Should store the variable bits mapping
    assert_eq!(bb.var_bits.len(), 2);
    assert_eq!(bb.var_bits.get(&("x".to_string(), 0)), Some(&bit0));
    assert_eq!(bb.var_bits.get(&("x".to_string(), 1)), Some(&bit1));
    
    // Second call should return same variables
    let bit0_again = bb.emit_bit(&term, 0);
    let bit1_again = bb.emit_bit(&term, 1);
    
    assert_eq!(bit0, bit0_again);
    assert_eq!(bit1, bit1_again);
    assert_eq!(bb.cnf.num_vars, 2); // No new variables created
}

#[test]
fn test_emit_bit_not() {
    let mut bb = BitBlaster::new();
    
    let inner = BvTerm::Value { bits: vec![true, false] };
    let term = BvTerm::Not(Box::new(inner));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables for inner term and result
    assert!(bb.cnf.num_vars >= 4);
    
    // bit0 should be the negation of inner[0] (true -> false)
    // bit1 should be the negation of inner[1] (false -> true)
    assert_eq!(bit0.1, false);
    assert_eq!(bit1.1, true);
}

#[test]
fn test_emit_bit_and() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::And(Box::new(a), Box::new(b));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables and AND constraints
    assert!(bb.cnf.num_vars >= 6);
    assert!(bb.cnf.clauses.len() >= 6);
    
    // bit0 = true & false = false
    // bit1 = false & true = false
    assert_eq!(bit0.1, false);
    assert_eq!(bit1.1, false);
}

#[test]
fn test_emit_bit_or() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Or(Box::new(a), Box::new(b));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables and OR constraints
    assert!(bb.cnf.num_vars >= 6);
    assert!(bb.cnf.clauses.len() >= 6);
    
    // bit0 = true | false = true
    // bit1 = false | true = true
    assert_eq!(bit0.1, true);
    assert_eq!(bit1.1, true);
}

#[test]
fn test_emit_bit_xor() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Xor(Box::new(a), Box::new(b));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables and XOR constraints
    assert!(bb.cnf.num_vars >= 6);
    assert!(bb.cnf.clauses.len() >= 8);
    
    // bit0 = true ^ false = true
    // bit1 = false ^ true = true
    assert_eq!(bit0.1, true);
    assert_eq!(bit1.1, true);
}

#[test]
fn test_emit_bit_add() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false] };  // 1
    let b = BvTerm::Value { bits: vec![true, false] };  // 1
    let term = BvTerm::Add(Box::new(a), Box::new(b));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables and addition constraints
    assert!(bb.cnf.num_vars >= 6);
    assert!(bb.cnf.clauses.len() >= 6);
    
    // 1 + 1 = 2 = [0, 1] in binary
    assert_eq!(bit0.1, false);
    assert_eq!(bit1.1, true);
}

#[test]
fn test_emit_bit_sub() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![false, true] };  // 2
    let b = BvTerm::Value { bits: vec![true, false] };  // 1
    let term = BvTerm::Sub(Box::new(a), Box::new(b));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables and subtraction constraints
    assert!(bb.cnf.num_vars >= 6);
    assert!(bb.cnf.clauses.len() >= 6);
    
    // 2 - 1 = 1 = [1, 0] in binary
    assert_eq!(bit0.1, true);
    assert_eq!(bit1.1, false);
}

#[test]
fn test_emit_bit_mul() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false] };  // 1
    let b = BvTerm::Value { bits: vec![false, true] };  // 2
    let term = BvTerm::Mul(Box::new(a), Box::new(b));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables and multiplication constraints
    assert!(bb.cnf.num_vars >= 6);
    assert!(bb.cnf.clauses.len() >= 6);
    
    // 1 * 2 = 2 = [0, 1] in binary
    assert_eq!(bit0.1, false);
    assert_eq!(bit1.1, true);
}

#[test]
fn test_emit_bit_concat() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true] };      // 1-bit: 1
    let b = BvTerm::Value { bits: vec![false] };     // 1-bit: 0
    let term = BvTerm::Concat(Box::new(a), Box::new(b));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables for concatenation
    assert!(bb.cnf.num_vars >= 2);
    
    // concat(1, 0) = [1, 0] in binary
    assert_eq!(bit0.1, false); // b[0] = 0
    assert_eq!(bit1.1, true);  // a[0] = 1
}

#[test]
fn test_emit_bit_extract() {
    let mut bb = BitBlaster::new();
    
    let inner = BvTerm::Value { bits: vec![true, false, true, false] }; // 4-bit: 1010
    let term = BvTerm::Extract { hi: 2, lo: 1, a: Box::new(inner) };
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables for extraction
    assert!(bb.cnf.num_vars >= 2);
    
    // extract(2, 1, 1010) = 10 in binary
    assert_eq!(bit0.1, false); // inner[1] = 0
    assert_eq!(bit1.1, true);  // inner[2] = 1
}

#[test]
fn test_emit_bit_sign_extend() {
    let mut bb = BitBlaster::new();
    
    let inner = BvTerm::Value { bits: vec![true, false] }; // 2-bit: 10 (negative)
    let term = BvTerm::SignExtend { a: Box::new(inner), extra: 2 };
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    let bit2 = bb.emit_bit(&term, 2);
    let bit3 = bb.emit_bit(&term, 3);
    
    // Should create variables for sign extension
    assert!(bb.cnf.num_vars >= 4);
    
    // sign_extend(10, 2) = 1110 in binary (negative number)
    assert_eq!(bit0.1, false); // inner[0] = 0
    assert_eq!(bit1.1, true);  // inner[1] = 1
    assert_eq!(bit2.1, true);  // sign bit = 1
    assert_eq!(bit3.1, true);  // sign bit = 1
}

#[test]
fn test_emit_bit_rotate_left() {
    let mut bb = BitBlaster::new();
    
    let inner = BvTerm::Value { bits: vec![true, false, true, false] }; // 4-bit: 1010
    let term = BvTerm::RotateLeft { a: Box::new(inner), amount: 1 };
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    let bit2 = bb.emit_bit(&term, 2);
    let bit3 = bb.emit_bit(&term, 3);
    
    // Should create variables for rotation
    assert!(bb.cnf.num_vars >= 4);
    
    // rotate_left(1010, 1) = 0101
    assert_eq!(bit0.1, true);  // inner[3] = 0
    assert_eq!(bit1.1, false); // inner[0] = 1
    assert_eq!(bit2.1, true);  // inner[1] = 0
    assert_eq!(bit3.1, false); // inner[2] = 1
}

#[test]
fn test_emit_bit_rotate_right() {
    let mut bb = BitBlaster::new();
    
    let inner = BvTerm::Value { bits: vec![true, false, true, false] }; // 4-bit: 1010
    let term = BvTerm::RotateRight { a: Box::new(inner), amount: 1 };
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    let bit2 = bb.emit_bit(&term, 2);
    let bit3 = bb.emit_bit(&term, 3);
    
    // Should create variables for rotation
    assert!(bb.cnf.num_vars >= 4);
    
    // rotate_right(1010, 1) = 0101
    assert_eq!(bit0.1, true);  // inner[1] = 0
    assert_eq!(bit1.1, false); // inner[2] = 1
    assert_eq!(bit2.1, true);  // inner[3] = 0
    assert_eq!(bit3.1, false); // inner[0] = 1
}

#[test]
fn test_emit_bit_repeat() {
    let mut bb = BitBlaster::new();
    
    let inner = BvTerm::Value { bits: vec![true, false] }; // 2-bit: 10
    let term = BvTerm::Repeat { a: Box::new(inner), times: 2 };
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    let bit2 = bb.emit_bit(&term, 2);
    let bit3 = bb.emit_bit(&term, 3);
    
    // Should create variables for repetition
    assert!(bb.cnf.num_vars >= 4);
    
    // repeat(10, 2) = 1010
    assert_eq!(bit0.1, false); // inner[0] = 0
    assert_eq!(bit1.1, true);  // inner[1] = 1
    assert_eq!(bit2.1, false); // inner[0] = 0
    assert_eq!(bit3.1, true);  // inner[1] = 1
}

#[test]
fn test_emit_bit_ite() {
    let mut bb = BitBlaster::new();
    
    let cond = BvTerm::Eq(
        Box::new(BvTerm::Value { bits: vec![true] }),
        Box::new(BvTerm::Value { bits: vec![true] })
    );
    let then_term = BvTerm::Value { bits: vec![true, false] };  // 10
    let else_term = BvTerm::Value { bits: vec![false, true] }; // 01
    let term = BvTerm::Ite(Box::new(cond), Box::new(then_term), Box::new(else_term));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables for ITE
    assert!(bb.cnf.num_vars >= 6);
    assert!(bb.cnf.clauses.len() >= 6);
    
    // Since cond is true (1 == 1), should select then_term
    assert_eq!(bit0.1, false); // then_term[0] = 0
    assert_eq!(bit1.1, true);  // then_term[1] = 1
}

#[test]
fn test_emit_bit_shifts() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false, true, false] }; // 1010
    let sh = BvTerm::Value { bits: vec![false, true] };            // 01 (shift by 1)
    
    // Test left shift
    let shl_term = BvTerm::Shl(Box::new(a.clone()), Box::new(sh.clone()));
    let shl_bit = bb.emit_bit(&shl_term, 0);
    
    // Test logical right shift
    let lshr_term = BvTerm::Lshr(Box::new(a.clone()), Box::new(sh.clone()));
    let lshr_bit = bb.emit_bit(&lshr_term, 0);
    
    // Test arithmetic right shift
    let ashr_term = BvTerm::Ashr(Box::new(a), Box::new(sh));
    let ashr_bit = bb.emit_bit(&ashr_term, 0);
    
    // Should create variables for shift operations
    assert!(bb.cnf.num_vars >= 12);
    assert!(bb.cnf.clauses.len() >= 12);
    
    // All should be valid boolean literals
    assert!(shl_bit.0 < bb.cnf.num_vars);
    assert!(lshr_bit.0 < bb.cnf.num_vars);
    assert!(ashr_bit.0 < bb.cnf.num_vars);
}

#[test]
fn test_emit_bit_neg() {
    let mut bb = BitBlaster::new();
    
    let inner = BvTerm::Value { bits: vec![true, false] }; // 2-bit: 10
    let term = BvTerm::Neg(Box::new(inner));
    
    let bit0 = bb.emit_bit(&term, 0);
    let bit1 = bb.emit_bit(&term, 1);
    
    // Should create variables for negation
    assert!(bb.cnf.num_vars >= 4);
    assert!(bb.cnf.clauses.len() >= 4);
    
    // -2 = 2 in 2-bit arithmetic (overflow)
    assert_eq!(bit0.1, false);
    assert_eq!(bit1.1, true);
}

#[test]
fn test_mk_and() {
    let mut bb = BitBlaster::new();
    
    let a = bb.new_bool();
    let b = bb.new_bool();
    let c = bb.new_bool();
    
    let result = bb.mk_and(&[a, b, c]);
    
    // Should create AND constraints
    assert!(bb.cnf.clauses.len() >= 4);
    
    // Result should be a valid boolean literal
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_mk_or() {
    let mut bb = BitBlaster::new();
    
    let a = bb.new_bool();
    let b = bb.new_bool();
    let c = bb.new_bool();
    
    let result = bb.mk_or(&[a, b, c]);
    
    // Should create OR constraints
    assert!(bb.cnf.clauses.len() >= 4);
    
    // Result should be a valid boolean literal
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_mk_implies() {
    let mut bb = BitBlaster::new();
    
    let a = bb.new_bool();
    let b = bb.new_bool();
    
    let result = bb.mk_implies(a, b);
    
    // Should create implication constraints
    assert!(bb.cnf.clauses.len() >= 3);
    
    // Result should be a valid boolean literal
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_mk_not() {
    let mut bb = BitBlaster::new();
    
    let a = bb.new_bool();
    let not_a = bb.mk_not(a);
    
    // Should not create new variables for NOT
    assert_eq!(bb.cnf.num_vars, 1);
    
    // NOT should flip polarity
    assert_eq!(not_a.0, a.0);
    assert_eq!(not_a.1, !a.1);
}

#[test]
fn test_encode_xor() {
    let mut bb = BitBlaster::new();
    
    let a = bb.new_bool();
    let b = bb.new_bool();
    let out = bb.new_bool();
    
    bb.encode_xor(out, a, b);
    
    // Should create XOR constraints
    assert!(bb.cnf.clauses.len() >= 4);
}

#[test]
fn test_encode_xor_var() {
    let mut bb = BitBlaster::new();
    
    let a = bb.new_bool();
    let b = bb.new_bool();
    
    let result = bb.encode_xor_var(a, b);
    
    // Should create XOR constraints
    assert!(bb.cnf.clauses.len() >= 4);
    
    // Result should be a valid boolean literal
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_bool_eq() {
    let mut bb = BitBlaster::new();
    
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![true, false] };
    
    let result = bb.bool_eq(&a, &b);
    
    // Should create equality constraints
    assert!(bb.cnf.clauses.len() >= 4);
    
    // Result should be a valid boolean literal
    assert!(result.0 < bb.cnf.num_vars);
}

#[test]
fn test_assert_true() {
    let mut bb = BitBlaster::new();
    
    let lit = bb.new_bool();
    bb.assert_true(lit);
    
    // Should add a unit clause
    assert_eq!(bb.cnf.clauses.len(), 1);
    assert_eq!(bb.cnf.clauses[0], vec![lit]);
}

#[test]
fn test_new_bool() {
    let mut bb = BitBlaster::new();
    
    let bool1 = bb.new_bool();
    let bool2 = bb.new_bool();
    
    // Should create new boolean variables
    assert_eq!(bb.cnf.num_vars, 2);
    assert_eq!(bool1.0, 0);
    assert_eq!(bool2.0, 1);
    assert!(bool1.1);
    assert!(bool2.1);
}

#[test]
fn test_new_tmp() {
    let mut bb = BitBlaster::new();
    
    let tmp1 = bb.new_tmp();
    let tmp2 = bb.new_tmp();
    
    // Should create new temporary variables
    assert_eq!(bb.cnf.num_vars, 2);
    assert_eq!(tmp1.0, 0);
    assert_eq!(tmp2.0, 1);
    assert!(tmp1.1);
    assert!(tmp2.1);
}
