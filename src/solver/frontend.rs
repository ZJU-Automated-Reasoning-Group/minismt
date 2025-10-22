use std::collections::HashMap;
use anyhow::{bail, Context, Result};
use tracing::trace;

use super::sexpr::{parse_all, SExpr};
use super::bv::{BvTerm, SortBv};
use super::symbol_table::SymbolTable;
use super::parsed_item::ParsingStack;
use super::aig_sat_interface::AigBitBlasterAdapter;
use super::config::SolverConfig;

/// A more sophisticated frontend parser following Bitwuzla's approach
pub struct FrontendParser {
    /// Symbol table for managing bindings
    symbol_table: SymbolTable,
    /// Parsing stack for managing parsed items
    parsing_stack: ParsingStack,
    /// Current assertion level
    assertion_level: u32,
    /// Variable declarations
    variables: HashMap<String, SortBv>,
    /// Function definitions
    function_definitions: HashMap<String, (Vec<String>, SExpr)>,
    /// Assertions
    assertions: Vec<SExpr>,
    /// Solver configuration
    config: SolverConfig,
    /// Last bit-blaster used
    last_bb: Option<AigBitBlasterAdapter>,
    /// Last model found
    last_model: Option<Vec<bool>>,
    /// Push/pop frames
    frames: Vec<usize>,
}

impl FrontendParser {
    pub fn new() -> Self {
        Self::new_with_config(SolverConfig::default())
    }
    
    pub fn new_with_config(config: SolverConfig) -> Self {
        Self {
            symbol_table: SymbolTable::new(),
            parsing_stack: ParsingStack::new(),
            assertion_level: 0,
            variables: HashMap::new(),
            function_definitions: HashMap::new(),
            assertions: Vec::new(),
            config,
            last_bb: None,
            last_model: None,
            frames: Vec::new(),
        }
    }
    
    /// Parse a complete SMT-LIB script
    pub fn parse_script(&mut self, input: &str) -> Result<Vec<Command>> {
        let exprs = parse_all(input)?;
        trace!(num_exprs = exprs.len(), "sexpr parsed");
        
        let mut commands = Vec::new();
        for expr in exprs {
            let cmd = self.parse_command(&expr)?;
            commands.push(cmd);
        }
        
        Ok(commands)
    }
    
    /// Parse a single command
    fn parse_command(&mut self, expr: &SExpr) -> Result<Command> {
        let SExpr::List(list) = expr else { 
            bail!("expected command list") 
        };
        
        if list.is_empty() {
            bail!("empty command");
        }
        
        let head = atom(&list[0])?;
        trace!(head = %head, nargs = list.len() - 1, "parse command");
        
        match head.as_str() {
            "set-logic" => {
                if list.len() != 2 { bail!("set-logic needs 1 arg"); }
                let logic = atom(&list[1])?;
                Ok(Command::SetLogic(logic))
            }
            "set-option" => {
                if list.len() != 3 { bail!("set-option needs 2 args"); }
                let key = atom(&list[1])?;
                let value = atom(&list[2])?;
                Ok(Command::SetOption(key, value))
            }
            "set-info" => {
                if list.len() != 3 { bail!("set-info needs 2 args"); }
                let key = atom(&list[1])?;
                let value = atom(&list[2])?;
                Ok(Command::SetInfo(key, value))
            }
            "declare-const" => {
                if list.len() != 3 { bail!("declare-const needs 2 args"); }
                let name = atom(&list[1])?;
                let sort = self.parse_sort(&list[2])?;
                Ok(Command::DeclareConst(name, sort))
            }
            "assert" => {
                if list.len() != 2 { bail!("assert needs 1 arg"); }
                Ok(Command::Assert(list[1].clone()))
            }
            "check-sat" => {
                if list.len() != 1 { bail!("check-sat needs 0 args"); }
                Ok(Command::CheckSat)
            }
            "get-model" => {
                if list.len() != 1 { bail!("get-model needs 0 args"); }
                Ok(Command::GetModel)
            }
            "push" => {
                if list.len() != 2 { bail!("push needs 1 arg"); }
                let n = atom(&list[1])?.parse::<u32>().context("push level")?;
                Ok(Command::Push(n))
            }
            "pop" => {
                if list.len() != 2 { bail!("pop needs 1 arg"); }
                let n = atom(&list[1])?.parse::<u32>().context("pop level")?;
                Ok(Command::Pop(n))
            }
            "get-value" => {
                if list.len() < 2 { bail!("get-value needs at least 1 arg"); }
                let mut vars = Vec::new();
                for i in 1..list.len() {
                    let var = atom(&list[i])?;
                    vars.push(var);
                }
                Ok(Command::GetValue(vars))
            }
            "reset" => {
                if list.len() != 1 { bail!("reset needs 0 args"); }
                Ok(Command::Reset)
            }
            "reset-assertions" => {
                if list.len() != 1 { bail!("reset-assertions needs 0 args"); }
                Ok(Command::ResetAssertions)
            }
            "exit" => {
                if list.len() != 1 { bail!("exit needs 0 args"); }
                Ok(Command::Exit)
            }
            "define-fun" => {
                if list.len() < 4 { bail!("define-fun needs at least 3 args"); }
                let name = atom(&list[1])?;
                let params = self.parse_parameters(&list[2])?;
                let _return_sort = self.parse_sort(&list[3])?;
                let body = list[4].clone();
                Ok(Command::DefineFun(name, params, body))
            }
            "get-info" => {
                if list.len() != 2 { bail!("get-info needs 1 arg"); }
                let key = atom(&list[1])?;
                Ok(Command::GetInfo(key))
            }
            "get-option" => {
                if list.len() != 2 { bail!("get-option needs 1 arg"); }
                let key = atom(&list[1])?;
                Ok(Command::GetOption(key))
            }
            "check-sat-assuming" => {
                if list.len() < 2 { bail!("check-sat-assuming needs at least 1 arg"); }
                let mut assumptions = Vec::new();
                for i in 1..list.len() {
                    assumptions.push(list[i].clone());
                }
                Ok(Command::CheckSatAssuming(assumptions))
            }
            _ => bail!("unknown command: {}", head)
        }
    }
    
    /// Parse a sort expression
    fn parse_sort(&self, expr: &SExpr) -> Result<SortBv> {
        match expr {
            SExpr::Atom(name) => {
                if name.starts_with("(_ BitVec ") && name.ends_with(")") {
                    let width_str = &name[11..name.len()-1];
                    let width = width_str.parse::<u32>().context("bitvector width")?;
                    Ok(SortBv { width })
                } else {
                    bail!("unsupported sort: {}", name)
                }
            }
            SExpr::List(list) => {
                if list.is_empty() { bail!("empty sort list"); }
                let head = atom(&list[0])?;
                match head.as_str() {
                    "_" => {
                        if list.len() != 3 { bail!("indexed sort needs 3 args"); }
                        let sort_name = atom(&list[1])?;
                        let index = atom(&list[2])?;
                        if sort_name == "BitVec" {
                            let width = index.parse::<u32>().context("bitvector width")?;
                            Ok(SortBv { width })
                        } else {
                            bail!("unsupported indexed sort: {}", sort_name)
                        }
                    }
                    _ => bail!("unsupported sort constructor: {}", head)
                }
            }
        }
    }
    
    /// Parse function parameters
    fn parse_parameters(&self, expr: &SExpr) -> Result<Vec<String>> {
        let SExpr::List(params) = expr else { bail!("expected parameter list") };
        let mut result = Vec::new();
        
        for param in params {
            let SExpr::List(param_list) = param else { bail!("expected parameter pair") };
            if param_list.len() != 2 { bail!("parameter needs name and sort"); }
            let name = atom(&param_list[0])?;
            result.push(name);
        }
        
        Ok(result)
    }
    
    /// Parse a term with proper symbol table management
    pub fn parse_term(&mut self, expr: &SExpr) -> Result<BvTerm> {
        self.parse_term_with_env(expr, &self.variables)
    }
    
    /// Parse a term with environment
    fn parse_term_with_env(&self, expr: &SExpr, vars: &HashMap<String, SortBv>) -> Result<BvTerm> {
        match expr {
            SExpr::Atom(name) => {
                if let Some(sort) = vars.get(name) {
                    Ok(BvTerm::Const { name: name.clone(), sort: *sort })
                } else {
                    bail!("undefined variable: {}", name)
                }
            }
            SExpr::List(items) => {
                if items.is_empty() { bail!("empty term list"); }
                let head = atom(&items[0])?;
                trace!(head = %head, nargs = items.len() - 1, "parse list term");
                
                match head.as_str() {
                    "let" => {
                        if items.len() < 3 { bail!("let needs at least 2 args"); }
                        self.parse_let_term(&items[1], &items[2], vars)
                    }
                    "_" => {
                        if items.len() < 3 { bail!("indexed term needs at least 2 args"); }
                        let sym = atom(&items[1])?;
                        if sym.starts_with("bv") {
                            let n = sym[2..].parse::<u128>().context("bv value")?;
                            let w = atom(&items[2])?.parse::<u32>().context("bv width")?;
                            let mut bits = vec![false; w as usize];
                            for i in 0..w { 
                                bits[i as usize] = ((n >> i) & 1) == 1; 
                            }
                            Ok(BvTerm::Value { bits })
                        } else {
                            bail!("unsupported indexed op")
                        }
                    }
                    "bvneg" => {
                        if items.len() != 2 { bail!("bvneg needs 1 arg"); }
                        Ok(BvTerm::Neg(Box::new(self.parse_term_with_env(&items[1], vars)?)))
                    }
                    "bvnot" => {
                        if items.len() != 2 { bail!("bvnot needs 1 arg"); }
                        Ok(BvTerm::Not(Box::new(self.parse_term_with_env(&items[1], vars)?)))
                    }
                    "bvand" => {
                        if items.len() != 3 { bail!("bvand needs 2 args"); }
                        Ok(BvTerm::And(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvor" => {
                        if items.len() != 3 { bail!("bvor needs 2 args"); }
                        Ok(BvTerm::Or(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvxor" => {
                        if items.len() != 3 { bail!("bvxor needs 2 args"); }
                        Ok(BvTerm::Xor(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvadd" => {
                        if items.len() != 3 { bail!("bvadd needs 2 args"); }
                        Ok(BvTerm::Add(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvsub" => {
                        if items.len() != 3 { bail!("bvsub needs 2 args"); }
                        Ok(BvTerm::Sub(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvmul" => {
                        if items.len() != 3 { bail!("bvmul needs 2 args"); }
                        Ok(BvTerm::Mul(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvudiv" => {
                        if items.len() != 3 { bail!("bvudiv needs 2 args"); }
                        Ok(BvTerm::Udiv(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvurem" => {
                        if items.len() != 3 { bail!("bvurem needs 2 args"); }
                        Ok(BvTerm::Urem(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvshl" => {
                        if items.len() != 3 { bail!("bvshl needs 2 args"); }
                        Ok(BvTerm::Shl(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvlshr" => {
                        if items.len() != 3 { bail!("bvlshr needs 2 args"); }
                        Ok(BvTerm::Lshr(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvashr" => {
                        if items.len() != 3 { bail!("bvashr needs 2 args"); }
                        Ok(BvTerm::Ashr(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvult" => {
                        if items.len() != 3 { bail!("bvult needs 2 args"); }
                        Ok(BvTerm::Ult(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvule" => {
                        if items.len() != 3 { bail!("bvule needs 2 args"); }
                        Ok(BvTerm::Ule(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvugt" => {
                        if items.len() != 3 { bail!("bvugt needs 2 args"); }
                        // bvugt a b = not (bvule a b)
                        Ok(BvTerm::Not(Box::new(BvTerm::Ule(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))))
                    }
                    "bvuge" => {
                        if items.len() != 3 { bail!("bvuge needs 2 args"); }
                        // bvuge a b = not (bvult a b)
                        Ok(BvTerm::Not(Box::new(BvTerm::Ult(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))))
                    }
                    "bvslt" => {
                        if items.len() != 3 { bail!("bvslt needs 2 args"); }
                        Ok(BvTerm::Slt(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvsle" => {
                        if items.len() != 3 { bail!("bvsle needs 2 args"); }
                        Ok(BvTerm::Sle(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))
                    }
                    "bvsgt" => {
                        if items.len() != 3 { bail!("bvsgt needs 2 args"); }
                        // bvsgt a b = not (bvsle a b)
                        Ok(BvTerm::Not(Box::new(BvTerm::Sle(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))))
                    }
                    "bvsge" => {
                        if items.len() != 3 { bail!("bvsge needs 2 args"); }
                        // bvsge a b = not (bvslt a b)
                        Ok(BvTerm::Not(Box::new(BvTerm::Slt(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?)
                        ))))
                    }
                    "concat" => {
                        if items.len() < 3 { bail!("concat needs at least 2 args"); }
                        let mut result = self.parse_term_with_env(&items[1], vars)?;
                        for i in 2..items.len() {
                            result = BvTerm::Concat(
                                Box::new(result),
                                Box::new(self.parse_term_with_env(&items[i], vars)?)
                            );
                        }
                        Ok(result)
                    }
                    "extract" => {
                        if items.len() != 4 { bail!("extract needs 3 args"); }
                        let high = atom(&items[1])?.parse::<u32>().context("extract high")?;
                        let low = atom(&items[2])?.parse::<u32>().context("extract low")?;
                        Ok(BvTerm::Extract {
                            hi: high,
                            lo: low,
                            a: Box::new(self.parse_term_with_env(&items[3], vars)?)
                        })
                    }
                    "zero_extend" => {
                        if items.len() != 3 { bail!("zero_extend needs 2 args"); }
                        let n = atom(&items[1])?.parse::<u32>().context("zero_extend amount")?;
                        // ZeroExtend is implemented as concat with zeros
                        let arg = self.parse_term_with_env(&items[2], vars)?;
                        let zeros = BvTerm::Value { bits: vec![false; n as usize] };
                        Ok(BvTerm::Concat(Box::new(zeros), Box::new(arg)))
                    }
                    "sign_extend" => {
                        if items.len() != 3 { bail!("sign_extend needs 2 args"); }
                        let n = atom(&items[1])?.parse::<u32>().context("sign_extend amount")?;
                        Ok(BvTerm::SignExtend {
                            a: Box::new(self.parse_term_with_env(&items[2], vars)?),
                            extra: n
                        })
                    }
                    "ite" => {
                        if items.len() != 4 { bail!("ite needs 3 args"); }
                        Ok(BvTerm::Ite(
                            Box::new(self.parse_term_with_env(&items[1], vars)?),
                            Box::new(self.parse_term_with_env(&items[2], vars)?),
                            Box::new(self.parse_term_with_env(&items[3], vars)?)
                        ))
                    }
                    _ => {
                        // Check if it's a function call
                        if let Some((params, body)) = self.function_definitions.get(&head) {
                            if items.len() - 1 != params.len() {
                                bail!("function {} expects {} args, got {}", head, params.len(), items.len() - 1);
                            }
                            
                            // Create substitution map
                            let mut substitutions = HashMap::new();
                            for (i, param) in params.iter().enumerate() {
                                let _arg = self.parse_term_with_env(&items[i + 1], vars)?;
                                substitutions.insert(param.clone(), SExpr::List(vec![
                                    SExpr::Atom("_".to_string()),
                                    SExpr::Atom(format!("bv{}", 0)), // Placeholder
                                    SExpr::Atom(format!("{}", 32)) // Placeholder
                                ]));
                            }
                            
                            // Substitute and parse
                            let substituted_body = self.substitute_let_vars(body, &substitutions);
                            self.parse_term_with_env(&substituted_body, vars)
                        } else {
                            bail!("unknown term constructor: {}", head)
                        }
                    }
                }
            }
        }
    }
    
    /// Parse a let term with proper scoping
    fn parse_let_term(&self, bindings_expr: &SExpr, body_expr: &SExpr, vars: &HashMap<String, SortBv>) -> Result<BvTerm> {
        let SExpr::List(binds) = bindings_expr else { bail!("let needs bindings list") };
        
        // Build substitution map with proper scoping
        let mut substitutions = HashMap::new();
        let mut current_body = body_expr.clone();
        
        for b in binds {
            let SExpr::List(pair) = b else { bail!("let binding must be a pair") };
            if pair.len() != 2 { bail!("let binding must have 2 elements"); }
            
            let name = atom(&pair[0])?;
            let val_expr = &pair[1];
            
            // Substitute the value using current substitutions
            let substituted_val = self.substitute_let_vars(val_expr, &substitutions);
            
            // Add this binding to the substitution map
            substitutions.insert(name, substituted_val);
        }
        
        // Apply all substitutions to the body
        current_body = self.substitute_let_vars(&current_body, &substitutions);
        
        // Parse the fully expanded body
        self.parse_term_with_env(&current_body, vars)
    }
    
    /// Substitute let variables with proper scoping
    fn substitute_let_vars(&self, expr: &SExpr, substitutions: &HashMap<String, SExpr>) -> SExpr {
        match expr {
            SExpr::Atom(name) => {
                if let Some(replacement) = substitutions.get(name) { 
                    replacement.clone() 
                } else { 
                    expr.clone() 
                }
            }
            SExpr::List(items) => {
                if items.is_empty() { 
                    return SExpr::List(vec![]); 
                }
                
                // Handle nested let with correct scoping
                if let SExpr::Atom(head) = &items[0] {
                    if head == "let" {
                        if items.len() < 3 { 
                            return expr.clone(); 
                        }
                        let mut out_subs = substitutions.clone();
                        let mut new_binds: Vec<SExpr> = Vec::new();
                        
                        if let SExpr::List(binds) = &items[1] {
                            for b in binds {
                                if let SExpr::List(pair) = b {
                                    if pair.len() == 2 {
                                        let var_name = match &pair[0] { 
                                            SExpr::Atom(n) => n.clone(), 
                                            _ => return expr.clone() 
                                        };
                                        // Substitute in value using current env
                                        let val_sub = self.substitute_let_vars(&pair[1], &out_subs);
                                        out_subs.insert(var_name.clone(), val_sub.clone());
                                        new_binds.push(SExpr::List(vec![SExpr::Atom(var_name), val_sub]));
                                    }
                                }
                            }
                        }
                        let new_body = self.substitute_let_vars(&items[2], &out_subs);
                        return SExpr::List(vec![SExpr::Atom("let".to_string()), SExpr::List(new_binds), new_body]);
                    }
                }
                
                let substituted_items: Vec<SExpr> = items.iter()
                    .map(|item| self.substitute_let_vars(item, substitutions))
                    .collect();
                SExpr::List(substituted_items)
            }
        }
    }
}

/// Commands that can be parsed
#[derive(Debug, Clone)]
pub enum Command {
    SetLogic(String), 
    SetOption(String, String), 
    SetInfo(String, String),
    DeclareConst(String, SortBv), 
    Assert(SExpr), 
    CheckSat, 
    GetModel,
    Push(u32), 
    Pop(u32), 
    GetValue(Vec<String>), 
    Reset, 
    ResetAssertions, 
    Exit,
    DefineFun0(String, SortBv, SExpr),
    DefineFun(String, Vec<String>, SExpr),
    GetInfo(String), 
    GetOption(String),
    CheckSatAssuming(Vec<SExpr>),
}

/// Helper function to extract atom from SExpr
fn atom(expr: &SExpr) -> Result<String> {
    match expr {
        SExpr::Atom(name) => Ok(name.clone()),
        _ => bail!("expected atom, got {:?}", expr)
    }
}
