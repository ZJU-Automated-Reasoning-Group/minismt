use anyhow::{Context, Result};
use tracing::{debug, trace};

pub mod sexpr;
pub mod smtlib;
pub mod bv;
pub mod cnf;
pub mod aig;
pub mod aig_cnf;
pub mod aig_bitblaster;
pub mod aig_sat_interface;
pub mod sat;
pub mod rewrites;
pub mod config;
pub mod symbol_table;
pub mod parsed_item;
pub mod frontend;

pub use config::SolverConfig;

pub struct SmtSolver {
    engine: smtlib::Engine,
}

impl SmtSolver {
    pub fn new() -> Self {
        Self {
            engine: smtlib::Engine::new_with_config(SolverConfig::default()),
        }
    }

    pub fn new_with_options(check_model: bool) -> Self {
        let mut config = SolverConfig::default();
        config.check_model = check_model;
        Self {
            engine: smtlib::Engine::new_with_config(config),
        }
    }
    
    pub fn new_with_config(config: SolverConfig) -> Self {
        Self {
            engine: smtlib::Engine::new_with_config(config),
        }
    }

    // Returns output string (e.g., "sat\n" / model) if any
    pub fn run_script(&mut self, input: &str) -> Result<Option<String>> {
        trace!(len = input.len(), "parsing script");
        let cmds = smtlib::parse_script(input).context("parse smt2 failed")?;
        debug!(num_cmds = cmds.len(), "parsed commands");
        let mut accumulated_output = String::new();
        let mut has_output = false;
        for cmd in cmds {
            trace!(?cmd, "eval command");
            let out = self.engine.eval(cmd)?;
            if let Some(s) = out {
                accumulated_output.push_str(&s);
                has_output = true;
            }
        }
        if has_output {
            Ok(Some(accumulated_output))
        } else {
            Ok(None)
        }
    }
}



