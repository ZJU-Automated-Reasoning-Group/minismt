use anyhow::Result;
use varisat::lit::Lit;
use varisat::solver::Solver;
use varisat::cnf::CnfFormula;
use varisat::ExtendFormula;
use tracing::{debug};

use super::bv::{BoolLit, Cnf};

pub fn solve_cnf(c: &Cnf) -> Result<Option<Vec<bool>>> {
    let mut solver = Solver::new();
    let mut f = CnfFormula::new();
    debug!(num_clauses = c.clauses.len(), num_vars = c.num_vars, "solve_cnf start");
    for cl in &c.clauses {
        let lits: Vec<Lit> = cl
            .iter()
            .map(|&BoolLit(var_idx, pol)| {
                // varisat variables are 1-based; Lit::from_dimacs
                let dim: isize = if pol { (var_idx as isize) + 1 } else { -((var_idx as isize) + 1) };
                Lit::from_dimacs(dim)
            })
            .collect();
        f.add_clause(&lits);
    }
    solver.add_formula(&f);
    if solver.solve().expect("solve") {
        let model = solver.model().expect("model");
        let mut vals = vec![false; c.num_vars];
        for lit in model {
            let d = lit.to_dimacs();
            let var = d.unsigned_abs() as usize - 1;
            let sign = d > 0;
            if var < vals.len() { vals[var] = sign; }
        }
        debug!("solve_cnf: SAT");
        Ok(Some(vals))
    } else {
        debug!("solve_cnf: UNSAT");
        Ok(None)
    }
}


