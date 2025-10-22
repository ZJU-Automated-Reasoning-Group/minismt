use minismt::solver::bv::{BvTerm, SortBv};
use minismt::solver::cnf::{BoolLit, Cnf};

#[test]
fn test_sort_bv_creation() {
    let sort = SortBv { width: 8 };
    assert_eq!(sort.width, 8);
}

#[test]
fn test_sort_bv_copy() {
    let sort1 = SortBv { width: 16 };
    let sort2 = sort1;
    assert_eq!(sort1.width, sort2.width);
    assert_eq!(sort2.width, 16);
}

#[test]
fn test_sort_bv_ordering() {
    let sort1 = SortBv { width: 8 };
    let sort2 = SortBv { width: 16 };
    let sort3 = SortBv { width: 32 };
    
    assert!(sort1 < sort2);
    assert!(sort2 < sort3);
    assert!(sort1 < sort3);
}

#[test]
fn test_bv_term_value_creation() {
    let bits = vec![true, false, true, false];
    let term = BvTerm::Value { bits: bits.clone() };
    
    assert_eq!(term.sort().unwrap().width, 4);
}

#[test]
fn test_bv_term_const_creation() {
    let sort = SortBv { width: 8 };
    let term = BvTerm::Const { name: "x".to_string(), sort };
    
    assert_eq!(term.sort().unwrap().width, 8);
}

#[test]
fn test_bv_term_not() {
    let inner = BvTerm::Value { bits: vec![true, false] };
    let term = BvTerm::Not(Box::new(inner));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_and() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::And(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_or() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Or(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_xor() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Xor(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_add() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Add(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_sub() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Sub(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_mul() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Mul(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_udiv() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Udiv(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_urem() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Urem(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_shl() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let sh = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Shl(Box::new(a), Box::new(sh));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_lshr() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let sh = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Lshr(Box::new(a), Box::new(sh));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_ashr() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let sh = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Ashr(Box::new(a), Box::new(sh));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_neg() {
    let inner = BvTerm::Value { bits: vec![true, false] };
    let term = BvTerm::Neg(Box::new(inner));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_concat() {
    let a = BvTerm::Value { bits: vec![true] };
    let b = BvTerm::Value { bits: vec![false] };
    let term = BvTerm::Concat(Box::new(a), Box::new(b));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_extract() {
    let inner = BvTerm::Value { bits: vec![true, false, true, false] };
    let term = BvTerm::Extract { hi: 2, lo: 1, a: Box::new(inner) };
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_eq() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Eq(Box::new(a), Box::new(b));
    
    // Boolean operations don't have bit-vector sorts
    assert_eq!(term.sort(), None);
}

#[test]
fn test_bv_term_ult() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Ult(Box::new(a), Box::new(b));
    
    // Boolean operations don't have bit-vector sorts
    assert_eq!(term.sort(), None);
}

#[test]
fn test_bv_term_ule() {
    let a = BvTerm::Value { bits: vec![true, false] };
    let b = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Ule(Box::new(a), Box::new(b));
    
    // Boolean operations don't have bit-vector sorts
    assert_eq!(term.sort(), None);
}

#[test]
fn test_bv_term_ite() {
    let cond = BvTerm::Eq(
        Box::new(BvTerm::Value { bits: vec![true] }),
        Box::new(BvTerm::Value { bits: vec![true] })
    );
    let then_term = BvTerm::Value { bits: vec![true, false] };
    let else_term = BvTerm::Value { bits: vec![false, true] };
    let term = BvTerm::Ite(Box::new(cond), Box::new(then_term), Box::new(else_term));
    
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bv_term_sign_extend() {
    let inner = BvTerm::Value { bits: vec![true, false] };
    let term = BvTerm::SignExtend { a: Box::new(inner), extra: 2 };
    
    assert_eq!(term.sort().unwrap().width, 4);
}

#[test]
fn test_bv_term_rotate_left() {
    let inner = BvTerm::Value { bits: vec![true, false, true, false] };
    let term = BvTerm::RotateLeft { a: Box::new(inner), amount: 1 };
    
    assert_eq!(term.sort().unwrap().width, 4);
}

#[test]
fn test_bv_term_rotate_right() {
    let inner = BvTerm::Value { bits: vec![true, false, true, false] };
    let term = BvTerm::RotateRight { a: Box::new(inner), amount: 1 };
    
    assert_eq!(term.sort().unwrap().width, 4);
}

#[test]
fn test_bv_term_repeat() {
    let inner = BvTerm::Value { bits: vec![true, false] };
    let term = BvTerm::Repeat { a: Box::new(inner), times: 3 };
    
    assert_eq!(term.sort().unwrap().width, 6);
}

#[test]
fn test_bv_term_clone() {
    let original = BvTerm::Value { bits: vec![true, false, true] };
    let cloned = original.clone();
    
    assert_eq!(original.sort(), cloned.sort());
    match (&original, &cloned) {
        (BvTerm::Value { bits: bits1 }, BvTerm::Value { bits: bits2 }) => {
            assert_eq!(bits1, bits2);
        }
        _ => panic!("Expected Value variants"),
    }
}

#[test]
fn test_bv_term_debug() {
    let term = BvTerm::Value { bits: vec![true, false] };
    let debug_str = format!("{:?}", term);
    
    // Should contain debug representation
    assert!(!debug_str.is_empty());
}

#[test]
fn test_bv_term_partial_eq() {
    let term1 = BvTerm::Value { bits: vec![true, false] };
    let term2 = BvTerm::Value { bits: vec![true, false] };
    let term3 = BvTerm::Value { bits: vec![false, true] };
    
    assert_eq!(term1, term2);
    assert_ne!(term1, term3);
}

#[test]
fn test_bv_term_hash() {
    use std::collections::HashMap;
    
    let mut map = HashMap::new();
    let term1 = BvTerm::Value { bits: vec![true, false] };
    let term2 = BvTerm::Value { bits: vec![false, true] };
    
    map.insert(term1.clone(), "first");
    map.insert(term2.clone(), "second");
    
    assert_eq!(map.get(&term1), Some(&"first"));
    assert_eq!(map.get(&term2), Some(&"second"));
}

#[test]
fn test_bool_lit_creation() {
    let lit = BoolLit(5, true);
    assert_eq!(lit.0, 5);
    assert_eq!(lit.1, true);
}

#[test]
fn test_bool_lit_copy() {
    let lit1 = BoolLit(10, false);
    let lit2 = lit1;
    assert_eq!(lit1.0, lit2.0);
    assert_eq!(lit1.1, lit2.1);
}

#[test]
fn test_bool_lit_ordering() {
    let lit1 = BoolLit(1, true);
    let lit2 = BoolLit(2, false);
    let lit3 = BoolLit(1, false);
    
    assert!(lit1 < lit2);
    assert!(lit3 < lit1);
    assert!(lit3 < lit2);
}

#[test]
fn test_bool_lit_hash() {
    use std::collections::HashMap;
    
    let mut map = HashMap::new();
    let lit1 = BoolLit(5, true);
    let lit2 = BoolLit(5, false);
    
    map.insert(lit1, "positive");
    map.insert(lit2, "negative");
    
    assert_eq!(map.get(&BoolLit(5, true)), Some(&"positive"));
    assert_eq!(map.get(&BoolLit(5, false)), Some(&"negative"));
}

#[test]
fn test_cnf_new() {
    let cnf = Cnf::default();
    assert_eq!(cnf.num_vars, 0);
    assert_eq!(cnf.clauses.len(), 0);
}

#[test]
fn test_cnf_new_var() {
    let mut cnf = Cnf::default();
    
    let var1 = cnf.new_var();
    let var2 = cnf.new_var();
    let var3 = cnf.new_var();
    
    assert_eq!(var1, 0);
    assert_eq!(var2, 1);
    assert_eq!(var3, 2);
    assert_eq!(cnf.num_vars, 3);
}

#[test]
fn test_cnf_add_clause() {
    let mut cnf = Cnf::default();
    
    let var1 = cnf.new_var();
    let var2 = cnf.new_var();
    
    let clause1 = vec![BoolLit(var1, true), BoolLit(var2, false)];
    let clause2 = vec![BoolLit(var1, false)];
    
    cnf.add_clause(clause1.clone());
    cnf.add_clause(clause2.clone());
    
    assert_eq!(cnf.clauses.len(), 2);
    assert_eq!(cnf.clauses[0], clause1);
    assert_eq!(cnf.clauses[1], clause2);
}

#[test]
fn test_cnf_add_clause_iterator() {
    let mut cnf = Cnf::default();
    
    let var1 = cnf.new_var();
    let var2 = cnf.new_var();
    
    let literals = [BoolLit(var1, true), BoolLit(var2, false)];
    cnf.add_clause(literals.iter().cloned());
    
    assert_eq!(cnf.clauses.len(), 1);
    assert_eq!(cnf.clauses[0], vec![BoolLit(var1, true), BoolLit(var2, false)]);
}

#[test]
fn test_cnf_clone() {
    let mut cnf = Cnf::default();
    cnf.add_clause(vec![BoolLit(0, true)]);
    cnf.add_clause(vec![BoolLit(1, false)]);
    
    let cloned = cnf.clone();
    
    assert_eq!(cnf.num_vars, cloned.num_vars);
    assert_eq!(cnf.clauses, cloned.clauses);
}

#[test]
fn test_cnf_debug() {
    let mut cnf = Cnf::default();
    cnf.add_clause(vec![BoolLit(0, true)]);
    
    let debug_str = format!("{:?}", cnf);
    
    // Should contain debug representation
    assert!(!debug_str.is_empty());
}

#[test]
fn test_complex_bv_term_construction() {
    // Test building a complex term: (a + b) * (c - d)
    let a = BvTerm::Const { name: "a".to_string(), sort: SortBv { width: 8 } };
    let b = BvTerm::Const { name: "b".to_string(), sort: SortBv { width: 8 } };
    let c = BvTerm::Const { name: "c".to_string(), sort: SortBv { width: 8 } };
    let d = BvTerm::Const { name: "d".to_string(), sort: SortBv { width: 8 } };
    
    let add = BvTerm::Add(Box::new(a), Box::new(b));
    let sub = BvTerm::Sub(Box::new(c), Box::new(d));
    let mul = BvTerm::Mul(Box::new(add), Box::new(sub));
    
    assert_eq!(mul.sort().unwrap().width, 8);
}

#[test]
fn test_nested_operations() {
    // Test deeply nested operations
    let base = BvTerm::Value { bits: vec![true, false] };
    
    let mut term = base.clone();
    for _ in 0..5 {
        term = BvTerm::Not(Box::new(term));
    }
    
    // After 5 NOT operations, should still have width 2
    assert_eq!(term.sort().unwrap().width, 2);
}

#[test]
fn test_bit_vector_arithmetic_chain() {
    // Test a chain of arithmetic operations
    let x = BvTerm::Const { name: "x".to_string(), sort: SortBv { width: 4 } };
    let y = BvTerm::Const { name: "y".to_string(), sort: SortBv { width: 4 } };
    let z = BvTerm::Const { name: "z".to_string(), sort: SortBv { width: 4 } };
    
    // Compute: (x + y) * z - x
    let add = BvTerm::Add(Box::new(x.clone()), Box::new(y));
    let mul = BvTerm::Mul(Box::new(add), Box::new(z));
    let result = BvTerm::Sub(Box::new(mul), Box::new(x));
    
    assert_eq!(result.sort().unwrap().width, 4);
}

#[test]
fn test_boolean_operations_chain() {
    // Test a chain of boolean operations
    let a = BvTerm::Const { name: "a".to_string(), sort: SortBv { width: 2 } };
    let b = BvTerm::Const { name: "b".to_string(), sort: SortBv { width: 2 } };
    let c = BvTerm::Const { name: "c".to_string(), sort: SortBv { width: 2 } };
    
    // Compute: (a & b) | (b & c) ^ (a | c)
    let and1 = BvTerm::And(Box::new(a.clone()), Box::new(b.clone()));
    let and2 = BvTerm::And(Box::new(b), Box::new(c.clone()));
    let or1 = BvTerm::Or(Box::new(a), Box::new(c));
    let or2 = BvTerm::Or(Box::new(and1), Box::new(and2));
    let result = BvTerm::Xor(Box::new(or2), Box::new(or1));
    
    assert_eq!(result.sort().unwrap().width, 2);
}

#[test]
fn test_shift_operations_with_different_widths() {
    // Test shift operations with different bit widths
    let a = BvTerm::Value { bits: vec![true, false, true, false, true] }; // 5-bit
    let sh1 = BvTerm::Value { bits: vec![true] };                         // 1-bit
    let sh2 = BvTerm::Value { bits: vec![false, true] };                  // 2-bit
    
    let shl1 = BvTerm::Shl(Box::new(a.clone()), Box::new(sh1.clone()));
    let shl2 = BvTerm::Shl(Box::new(a.clone()), Box::new(sh2.clone()));
    let lshr = BvTerm::Lshr(Box::new(a.clone()), Box::new(sh1.clone()));
    let ashr = BvTerm::Ashr(Box::new(a), Box::new(sh2));
    
    assert_eq!(shl1.sort().unwrap().width, 5);
    assert_eq!(shl2.sort().unwrap().width, 5);
    assert_eq!(lshr.sort().unwrap().width, 5);
    assert_eq!(ashr.sort().unwrap().width, 5);
}

#[test]
fn test_extract_with_different_ranges() {
    // Test extract operations with different ranges
    let base = BvTerm::Value { bits: vec![true, false, true, false, true, false, true, false] }; // 8-bit
    
    let extract1 = BvTerm::Extract { hi: 7, lo: 4, a: Box::new(base.clone()) };
    let extract2 = BvTerm::Extract { hi: 3, lo: 0, a: Box::new(base.clone()) };
    let extract3 = BvTerm::Extract { hi: 5, lo: 2, a: Box::new(base) };
    
    assert_eq!(extract1.sort().unwrap().width, 4);
    assert_eq!(extract2.sort().unwrap().width, 4);
    assert_eq!(extract3.sort().unwrap().width, 4);
}

#[test]
fn test_sign_extend_with_different_amounts() {
    // Test sign extension with different amounts
    let base = BvTerm::Value { bits: vec![true, false] }; // 2-bit
    
    let extend1 = BvTerm::SignExtend { a: Box::new(base.clone()), extra: 1 };
    let extend2 = BvTerm::SignExtend { a: Box::new(base.clone()), extra: 3 };
    let extend3 = BvTerm::SignExtend { a: Box::new(base), extra: 0 };
    
    assert_eq!(extend1.sort().unwrap().width, 3);
    assert_eq!(extend2.sort().unwrap().width, 5);
    assert_eq!(extend3.sort().unwrap().width, 2);
}

#[test]
fn test_rotate_with_different_amounts() {
    // Test rotation operations with different amounts
    let base = BvTerm::Value { bits: vec![true, false, true, false] }; // 4-bit
    
    let rotl1 = BvTerm::RotateLeft { a: Box::new(base.clone()), amount: 1 };
    let rotl2 = BvTerm::RotateLeft { a: Box::new(base.clone()), amount: 3 };
    let rotr1 = BvTerm::RotateRight { a: Box::new(base.clone()), amount: 2 };
    let rotr2 = BvTerm::RotateRight { a: Box::new(base), amount: 0 };
    
    assert_eq!(rotl1.sort().unwrap().width, 4);
    assert_eq!(rotl2.sort().unwrap().width, 4);
    assert_eq!(rotr1.sort().unwrap().width, 4);
    assert_eq!(rotr2.sort().unwrap().width, 4);
}

#[test]
fn test_repeat_with_different_times() {
    // Test repeat operations with different times
    let base = BvTerm::Value { bits: vec![true, false] }; // 2-bit
    
    let repeat1 = BvTerm::Repeat { a: Box::new(base.clone()), times: 1 };
    let repeat2 = BvTerm::Repeat { a: Box::new(base.clone()), times: 4 };
    let repeat3 = BvTerm::Repeat { a: Box::new(base), times: 0 };
    
    assert_eq!(repeat1.sort().unwrap().width, 2);
    assert_eq!(repeat2.sort().unwrap().width, 8);
    assert_eq!(repeat3.sort().unwrap().width, 0);
}
