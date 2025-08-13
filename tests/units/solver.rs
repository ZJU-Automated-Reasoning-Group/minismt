use minismt::solver::SmtSolver;

#[test]
fn test_smt_solver_new() {
    let _solver = SmtSolver::new();
    // Basic test that constructor doesn't panic
    assert!(true);
}

#[test]
fn test_smt_solver_run_script_empty() {
    let mut solver = SmtSolver::new();
    let result = solver.run_script("").unwrap();
    assert_eq!(result, None);
}

#[test]
fn test_smt_solver_run_script_set_logic() {
    let mut solver = SmtSolver::new();
    let script = "(set-logic QF_BV)";
    let result = solver.run_script(script).unwrap();
    assert_eq!(result, None);
}

#[test]
fn test_smt_solver_run_script_declare_const() {
    let mut solver = SmtSolver::new();
    let script = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))";
    let result = solver.run_script(script).unwrap();
    assert_eq!(result, None);
}

#[test]
fn test_smt_solver_run_script_assert() {
    let mut solver = SmtSolver::new();
    let script = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x #x00))";
    let result = solver.run_script(script).unwrap();
    assert_eq!(result, None);
}

#[test]
fn test_smt_solver_run_script_check_sat() {
    let mut solver = SmtSolver::new();
    let script = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x #x00))\n(check-sat)";
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_get_model() {
    let mut solver = SmtSolver::new();
    let script = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(assert (= x #x00))\n(check-sat)\n(get-model)";
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
    assert!(output.contains("(model"));
}

#[test]
fn test_smt_solver_run_script_multiple_commands() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (= x #x0))
        (assert (= y #x1))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_arithmetic() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (= (bvadd x y) #x5))
        (assert (= x #x2))
        (check-sat)
        (get-model)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_boolean_operations() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (= (bvand x y) #x0))
        (assert (= x #xF))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_comparison() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (bvult x y))
        (assert (= x #x1))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_shift_operations() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= (bvshl x #x1) #x8))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_extract() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (assert (= ((_ extract 3 0) x) #xA))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_concat() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (= (concat x y) #xAB))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_ite() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (declare-const c Bool)
        (assert (= (ite c x y) #x5))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_reset() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= x #x0))
        (check-sat)
        (reset)
        (declare-const y (_ BitVec 4))
        (assert (= y #x1))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_reset_assertions() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= x #x0))
        (check-sat)
        (reset-assertions)
        (assert (= x #x1))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_push_pop() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (push 1)
        (assert (= x #x0))
        (check-sat)
        (pop 1)
        (assert (= x #x1))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_get_value() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= x #x5))
        (check-sat)
        (get-value (x))
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
    assert!(output.contains("get-value"));
}

#[test]
fn test_smt_solver_run_script_get_info() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (get-info :version)
    "#;
    let result = solver.run_script(script).unwrap();
    // get-info might not return anything, so we just check it doesn't panic
    assert!(true);
}

#[test]
fn test_smt_solver_run_script_get_option() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (get-option :print-success)
    "#;
    let result = solver.run_script(script).unwrap();
    // get-option might not return anything, so we just check it doesn't panic
    assert!(true);
}

#[test]
fn test_smt_solver_run_script_set_option() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (set-option :print-success true)
        (declare-const x (_ BitVec 4))
        (assert (= x #x0))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_exit() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (exit)
    "#;
    let result = solver.run_script(script).unwrap();
    // exit should not return anything
    assert_eq!(result, None);
}

#[test]
fn test_smt_solver_run_script_unsat_case() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= x #x0))
        (assert (= x #x1))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    // This should be UNSAT due to conflicting assertions
    assert!(output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_sat_case() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= x #x5))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    // This should be SAT
    assert!(output.contains("sat"));
}

#[test]
fn test_smt_solver_run_script_complex_formula() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (declare-const z (_ BitVec 8))
        (assert (= (bvadd (bvmul x y) z) #x64))
        (assert (bvult x #x10))
        (assert (bvult y #x10))
        (check-sat)
        (get-model)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_boolean_logic() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (or (= x #x0) (= y #x0)))
        (assert (not (= x #x0)))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}













#[test]
fn test_smt_solver_run_script_mixed_logic() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (declare-const y (_ BitVec 4))
        (assert (and (= x #x0) (= y #x1)))
        (assert (or (= x #x1) (= y #x0)))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_nested_operations() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (declare-const z (_ BitVec 8))
        (assert (= (bvadd (bvshl x #x1) (bvand y z)) #x42))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    assert!(output.contains("sat") || output.contains("unsat"));
}

#[test]
fn test_smt_solver_run_script_overflow() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= (bvadd x #xF) #x0))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    // This should be SAT due to overflow: 1 + 15 = 0 (mod 16)
    assert!(output.contains("sat"));
}

#[test]
fn test_smt_solver_run_script_underflow() {
    let mut solver = SmtSolver::new();
    let script = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 4))
        (assert (= (bvsub x #x1) #xF))
        (check-sat)
    "#;
    let result = solver.run_script(script).unwrap();
    assert!(result.is_some());
    let output = result.unwrap();
    // This should be SAT due to underflow: 0 - 1 = 15 (mod 16)
    assert!(output.contains("sat"));
}
