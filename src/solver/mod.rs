use anyhow::{Context, Result};
use tracing::{debug, trace};

pub mod sexpr;
pub mod smtlib;
pub mod bv;
pub mod cnf;
pub mod sat;
pub mod rewrites;

pub struct SmtSolver {
    engine: smtlib::Engine,
}

impl SmtSolver {
    pub fn new() -> Self {
        Self {
            engine: smtlib::Engine::new(),
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



