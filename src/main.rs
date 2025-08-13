mod solver;

use anyhow::{Context, Result};
use std::io::{self, Read};
use std::fs;
use std::env;
use tracing_subscriber::{EnvFilter, fmt};
use tracing::{info, debug};

fn print_help() {
    println!("minismt - An SMT solver");
    println!();
    println!("USAGE:");
    println!("    minismt [OPTIONS] [FILE]");
    println!();
    println!("OPTIONS:");
    println!("    -h, --help, -help    Print this help message");
    println!();
    println!("ARGS:");
    println!("    <FILE>               Input SMT-LIB file (reads from stdin if not specified)");
    println!();
    println!("EXAMPLES:");
    println!("    minismt input.smt2           # Read from file");
    println!("    minismt < input.smt2         # Read from stdin");
    println!("    cat input.smt2 | minismt     # Read from stdin via pipe");
}

fn main() -> Result<()> {
    // Initialize global tracing subscriber once. Respect RUST_LOG if set.
    let _ = tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .with_target(true)
        .with_level(true)
        .try_init();

    debug!("starting minismt");
    let args: Vec<String> = env::args().collect();
    
    // Check for help flags
    if args.len() > 1 {
        let first_arg = &args[1];
        if first_arg == "-h" || first_arg == "--help" || first_arg == "-help" {
            print_help();
            return Ok(());
        }
    }
    
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
