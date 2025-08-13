mod solver;

use anyhow::{Context, Result};
use std::io::{self, Read};
use std::fs;
use std::env;

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();
    let input = if args.len() > 1 {
        fs::read_to_string(&args[1]).context("failed to read input file")?
    } else {
        let mut s = String::new();
        io::stdin().read_to_string(&mut s).context("failed to read stdin")?;
        s
    };

    let mut s = solver::SmtSolver::new();
    let out = s
        .run_script(&input)
        .context("failed to process SMT-LIB input")?;
    match out {
        None => Ok(()),
        Some(s) => {
            print!("{}", s);
            Ok(())
        }
    }
}
