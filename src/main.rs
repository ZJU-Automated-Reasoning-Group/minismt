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
    println!("    -h, --help, -help           Print this help message");
    println!("    --check-model               Enable model checking (verify model satisfies assertions)");
    println!();
    println!("SIMPLIFICATION OPTIONS:");
    println!("    --no-opts                   Disable all optimizations");
    println!("    --no-local-simp             Disable local constant folding (e.g., 2+3 -> 5)");
    println!("    --no-global-simp            Disable global simplifications (caching, CSE)");
    println!("    --no-rewrites               Disable rewrite rules (e.g., x+0 -> x)");
    println!("    --no-const-prop             Disable constant propagation");
    println!("    --no-bitblast-opts          Disable bitblasting optimizations");
    println!();
    println!("ARGS:");
    println!("    <FILE>                      Input SMT-LIB file (reads from stdin if not specified)");
    println!();
    println!("EXAMPLES:");
    println!("    minismt input.smt2                      # Read from file");
    println!("    minismt < input.smt2                    # Read from stdin");
    println!("    cat input.smt2 | minismt                # Read from stdin via pipe");
    println!("    minismt --check-model input.smt2        # Read from file and check model");
    println!("    minismt --no-opts input.smt2            # Disable all optimizations");
    println!("    minismt --no-local-simp input.smt2      # Disable local simplifications");
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
    
    // Parse command-line arguments
    let mut config = solver::SolverConfig::default();
    let mut file_path: Option<String> = None;
    
    let mut i = 1;
    while i < args.len() {
        let arg = &args[i];
        match arg.as_str() {
            "-h" | "--help" | "-help" => {
                print_help();
                return Ok(());
            }
            "--check-model" => {
                config.check_model = true;
            }
            "--no-opts" => {
                config.enable_local_simp = false;
                config.enable_global_simp = false;
                config.enable_rewrites = false;
                config.enable_const_prop = false;
                config.enable_bitblast_opts = false;
            }
            "--no-local-simp" => {
                config.enable_local_simp = false;
            }
            "--no-global-simp" => {
                config.enable_global_simp = false;
            }
            "--no-rewrites" => {
                config.enable_rewrites = false;
            }
            "--no-const-prop" => {
                config.enable_const_prop = false;
            }
            "--no-bitblast-opts" => {
                config.enable_bitblast_opts = false;
            }
            _ => {
                if arg.starts_with('-') {
                    eprintln!("Unknown option: {}", arg);
                    print_help();
                    return Ok(());
                }
                file_path = Some(arg.clone());
            }
        }
        i += 1;
    }
    
    let input = if let Some(path) = file_path {
        fs::read_to_string(&path).context("failed to read input file")?
    } else {
        let mut s = String::new();
        io::stdin().read_to_string(&mut s).context("failed to read stdin")?;
        s
    };

    let mut s = solver::SmtSolver::new_with_config(config);
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
