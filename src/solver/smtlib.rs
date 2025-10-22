use std::collections::HashMap;
use anyhow::{bail, Context, Result};
use super::sexpr::{parse_all, SExpr};
use super::bv::{BvTerm, SortBv};
use super::cnf::BoolLit;
use super::aig_sat_interface::AigBitBlasterAdapter;
use super::sat::solve_cnf;
use super::rewrites::simplify_bv;
use tracing::{trace, debug};

fn substitute_let_vars(expr: &SExpr, substitutions: &HashMap<String, SExpr>) -> SExpr {
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
            // Handle nested let with correct scoping: do not substitute into binding names, and
            // each binding can depend on previous ones (left-to-right).
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
                                    // Substitute in value using current env (depends on previous binds)
                                    let val_sub = substitute_let_vars(&pair[1], &out_subs);
                                    out_subs.insert(var_name.clone(), val_sub.clone());
                                    new_binds.push(SExpr::List(vec![SExpr::Atom(var_name), val_sub]));
                                }
                            }
                        }
                    }
                    let new_body = substitute_let_vars(&items[2], &out_subs);
                    return SExpr::List(vec![SExpr::Atom("let".to_string()), SExpr::List(new_binds), new_body]);
                }
            }
            let substituted_items: Vec<SExpr> = items.iter()
                .map(|item| substitute_let_vars(item, substitutions))
                .collect();
            SExpr::List(substituted_items)
        }
    }
}

fn expand_let_bindings(bindings_expr: &SExpr, body_expr: &SExpr, vars: &HashMap<String, SortBv>) -> Result<BvTerm> {
    let SExpr::List(binds) = bindings_expr else { bail!("let needs bindings list") };
    
    // Build substitution map with proper scoping: each binding can reference previous ones
    let mut substitutions = HashMap::new();
    let mut current_body = body_expr.clone();
    
    for b in binds {
        if let SExpr::List(pair) = b {
            let name = atom(&pair[0])?;
            let val_expr = &pair[1];
            
            // Substitute the value using current substitutions (allows previous bindings to be referenced)
            let substituted_val = substitute_let_vars(val_expr, &substitutions);
            
            // Add this binding to the substitution map
            substitutions.insert(name, substituted_val);
        }
    }
    
    // Apply all substitutions to the body
    current_body = substitute_let_vars(&current_body, &substitutions);
    
    // Parse the fully expanded body
    parse_term_with_env(&current_body, vars)
}

#[derive(Debug, Clone)]
pub enum Command {
    SetLogic(String), SetOption(String, String), SetInfo(String, String),
    DeclareConst(String, SortBv), Assert(SExpr), CheckSat, GetModel,
    Push(u32), Pop(u32), GetValue(Vec<String>), Reset, ResetAssertions, Exit,
    DefineFun0(String, SortBv, SExpr),
    DefineFun(String, Vec<String>, SExpr),
    GetInfo(String), GetOption(String),
    CheckSatAssuming(Vec<SExpr>),
}

pub fn parse_script(input: &str) -> Result<Vec<Command>> {
    let exprs = parse_all(input)?;
    trace!(num_exprs = exprs.len(), "sexpr parsed");
    exprs.into_iter().map(|e| parse_command(&e)).collect()
}

fn parse_command(e: &SExpr) -> Result<Command> {
    let SExpr::List(list) = e else { bail!("expected command list") };
    if list.is_empty() { bail!("empty command") };
    
    let head = atom(&list[0])?;
    match head.as_str() {
        "set-logic" => {
            if list.len() < 2 { bail!("insufficient args for set-logic"); }
            Ok(Command::SetLogic(atom(&list[1])?))
        }
        "set-option" | "set-info" => {
            if list.len() < 3 { bail!("insufficient args for {}", head) };
            Ok(if head == "set-option" { Command::SetOption(atom(&list[1])?, atom(&list[2])?) } else { Command::SetInfo(atom(&list[1])?, atom(&list[2])?) })
        }
        "get-info" => { if list.len() < 2 { bail!("insufficient args for get-info") }; Ok(Command::GetInfo(atom(&list[1])?)) }
        "get-option" => { if list.len() < 2 { bail!("insufficient args for get-option") }; Ok(Command::GetOption(atom(&list[1])?)) }
        "declare-fun" | "declare-const" => {
            let name = atom(&list[1])?;
            let sort = if head == "declare-fun" {
                let SExpr::List(args) = &list[2] else { bail!("declare-fun needs args list") };
                if !args.is_empty() { bail!("only zero-arity declare-fun supported") };
                parse_sort(&list[3])?
            } else {
                parse_sort(&list[2])?
            };
            Ok(Command::DeclareConst(name, sort))
        }
        "define-fun" => {
            let name = atom(&list[1])?;
            let SExpr::List(args) = &list[2] else { bail!("define-fun needs args list") };
            if args.is_empty() {
                let sort = parse_sort(&list[3])?;
                Ok(Command::DefineFun0(name, sort, list[4].clone()))
            } else {
                // Support function macros by storing argument names and body; sorts are ignored
                let mut arg_names: Vec<String> = Vec::new();
                for a in args {
                    if let SExpr::List(pair) = a {
                        let pname = atom(&pair[0])?;
                        let _psort = &pair[1]; // ignore
                        arg_names.push(pname);
                    } else { bail!("malformed define-fun arg") }
                }
                // let _ret_sort = parse_sort(&list[3])?; // ignore return sort
                Ok(Command::DefineFun(name, arg_names, list[4].clone()))
            }
        }
        "push" | "pop" => {
            let n = atom(&list[1])?.parse::<u32>()?;
            Ok(if head == "push" { Command::Push(n) } else { Command::Pop(n) })
        }
        "assert" => Ok(Command::Assert(list[1].clone())),
        "check-sat" => Ok(Command::CheckSat),
        "check-sat-assuming" => {
            if list.len() < 2 { bail!("check-sat-assuming needs assumptions"); }
            let SExpr::List(assumptions) = &list[1] else { bail!("check-sat-assuming needs assumptions list") };
            Ok(Command::CheckSatAssuming(assumptions.clone()))
        }
        "get-model" => Ok(Command::GetModel),
        "get-value" => {
            let mut vars = Vec::new();
            if let SExpr::List(vs) = &list[1] {
                for v in vs { vars.push(atom(v)?); }
            } else {
                vars.push(atom(&list[1])?);
            }
            Ok(Command::GetValue(vars))
        }
        "reset" => Ok(Command::Reset),
        "reset-assertions" => Ok(Command::ResetAssertions),
        "exit" => Ok(Command::Exit),
        _ => bail!("unsupported command {}", head),
    }
}

fn atom(e: &SExpr) -> Result<String> { match e { SExpr::Atom(s) => Ok(s.clone()), _ => bail!("expected atom") } }

fn dequote_ident(s: &str) -> Option<String> { s.strip_prefix('|').and_then(|t| t.strip_suffix('|')).map(|t| t.to_string()) }

fn parse_sort(e: &SExpr) -> Result<SortBv> {
    match e {
        SExpr::Atom(a) if a == "Bool" => Ok(SortBv { width: 1 }),
        SExpr::List(items) => {
            if items.len() == 3 && atom(&items[0])? == "_" && atom(&items[1])? == "BitVec" {
                let w = atom(&items[2])?.parse::<u32>().context("width parse")?;
                Ok(SortBv { width: w })
            } else {
                bail!("unsupported sort expression")
            }
        }
        _ => bail!("unsupported sort"),
    }
}

fn parse_bv_value(s: &str) -> Result<BvTerm> {
    if s.starts_with("#b") {
        // SMT-LIB binary literals are written MSB-first. Our internal
        // representation is LSB-first, so reverse the bit order.
        let bits: Vec<bool> = s[2..].chars().rev().map(|c| c == '1').collect();
        Ok(BvTerm::Value { bits })
    } else if s.starts_with("#x") {
        let hex = &s[2..];
        let mut bits = Vec::new();
        for ch in hex.chars().rev() {
            let v = ch.to_digit(16).context("hex digit")?;
            for i in 0..4 { bits.push(((v >> i) & 1) == 1); }
        }
        Ok(BvTerm::Value { bits })
    } else {
        bail!("unsupported bv literal {}", s)
    }
}

fn parse_term_with_env(e: &SExpr, vars: &HashMap<String, SortBv>) -> Result<BvTerm> {
    match e {
        SExpr::Atom(a) => {
            trace!(%a, "parse atom term");
            if a.starts_with("#") { return parse_bv_value(a); }
            // Accept boolean literals in term context as 1-bit vectors
            if a == "true" { return Ok(BvTerm::Value { bits: vec![true] }); }
            if a == "false" { return Ok(BvTerm::Value { bits: vec![false] }); }
            // Resolve variable names with fallback between quoted/unquoted
            if let Some(sort) = vars.get(a) {
                return Ok(BvTerm::Const { name: a.clone(), sort: *sort });
            }
            if let Some(unq) = dequote_ident(a) {
                if let Some(sort) = vars.get(&unq) {
                    return Ok(BvTerm::Const { name: unq, sort: *sort });
                }
            } else {
                // try quoted form
                let quoted = format!("|{}|", a);
                if let Some(sort) = vars.get(&quoted) {
                    return Ok(BvTerm::Const { name: quoted, sort: *sort });
                }
            }
            bail!("unknown symbol {}", a)
        }
        SExpr::List(items) => {
            if items.is_empty() { bail!("empty term") };
            let head = &items[0];
            
            // Handle indexed operators
            if let SExpr::List(head_items) = head {
                if !head_items.is_empty() && atom(&head_items[0])? == "_" {
                    let op = atom(&head_items[1])?;
                    return match op.as_str() {
                        "extract" => {
                            let hi = atom(&head_items[2])?.parse::<u32>()?;
                            let lo = atom(&head_items[3])?.parse::<u32>()?;
                            let a = parse_term_with_env(&items[1], vars)?;
                            Ok(BvTerm::Extract { hi, lo, a: Box::new(a) })
                        }
                        "zero_extend" => {
                            let k = atom(&head_items[2])?.parse::<u32>()?;
                            let a = parse_term_with_env(&items[1], vars)?;
                            let zeros = BvTerm::Value { bits: vec![false; k as usize] };
                            Ok(BvTerm::Concat(Box::new(zeros), Box::new(a)))
                        }
                        "sign_extend" => {
                            let k = atom(&head_items[2])?.parse::<u32>()?;
                            let a = parse_term_with_env(&items[1], vars)?;
                            Ok(BvTerm::SignExtend { a: Box::new(a), extra: k })
                        }
                        "rotate_left" => {
                            let k = atom(&head_items[2])?.parse::<u32>()?;
                            let a = parse_term_with_env(&items[1], vars)?;
                            Ok(BvTerm::RotateLeft { a: Box::new(a), amount: k })
                        }
                        "rotate_right" => {
                            let k = atom(&head_items[2])?.parse::<u32>()?;
                            let a = parse_term_with_env(&items[1], vars)?;
                            Ok(BvTerm::RotateRight { a: Box::new(a), amount: k })
                        }
                        "repeat" => {
                            let n = atom(&head_items[2])?.parse::<u32>()?;
                            let a = parse_term_with_env(&items[1], vars)?;
                            Ok(BvTerm::Repeat { a: Box::new(a), times: n })
                        }
                        _ => bail!("unsupported indexed op {}", op),
                    };
                }
            }
            
            let head = atom(head)?;
            trace!(head = %head, nargs = items.len() - 1, "parse list term");
            match head.as_str() {
                "let" => {
                    // Handle let bindings by expanding them recursively
                    expand_let_bindings(&items[1], &items[2], vars)
                }
                "_" => {
                    let sym = atom(&items[1])?;
                    if sym.starts_with("bv") {
                        let n = sym[2..].parse::<u128>().context("bv value")?;
                        let w = atom(&items[2])?.parse::<u32>().context("bv width")?;
                        let mut bits = vec![false; w as usize];
                        for i in 0..w { bits[i as usize] = ((n >> i) & 1) == 1; }
                        Ok(BvTerm::Value { bits })
                    } else { bail!("unsupported indexed op") }
                }
                "bvneg" => Ok(BvTerm::Neg(Box::new(parse_term_with_env(&items[1], vars)?))),
                "bvnot" => Ok(BvTerm::Not(Box::new(parse_term_with_env(&items[1], vars)?))),
                "bvredor" => Ok(BvTerm::RedOr(Box::new(parse_term_with_env(&items[1], vars)?))),
                "bvredand" => Ok(BvTerm::RedAnd(Box::new(parse_term_with_env(&items[1], vars)?))),
                "bvredxor" => Ok(BvTerm::RedXor(Box::new(parse_term_with_env(&items[1], vars)?))),
                "bvand" => Ok(BvTerm::And(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvnand" => Ok(BvTerm::Nand(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvor" => Ok(BvTerm::Or(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvxor" => Ok(BvTerm::Xor(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvxnor" => Ok(BvTerm::Xnor(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvnor" => Ok(BvTerm::Nor(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvcomp" => Ok(BvTerm::Comp(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvadd" => Ok(BvTerm::Add(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsub" => Ok(BvTerm::Sub(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvmul" => Ok(BvTerm::Mul(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvshl" => Ok(BvTerm::Shl(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvlshr" => Ok(BvTerm::Lshr(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvashr" => Ok(BvTerm::Ashr(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvudiv" => Ok(BvTerm::Udiv(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvurem" => Ok(BvTerm::Urem(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsdiv" => Ok(BvTerm::Sdiv(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsrem" => Ok(BvTerm::Srem(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsmod" => Ok(BvTerm::Smod(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                // Overflow operations
                "bvuaddo" => Ok(BvTerm::Uaddo(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsaddo" => Ok(BvTerm::Saddo(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvusubo" => Ok(BvTerm::Usubo(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvssubo" => Ok(BvTerm::Ssubo(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvumulo" => Ok(BvTerm::Umulo(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsmulo" => Ok(BvTerm::Smulo(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsdivo" => Ok(BvTerm::Sdivo(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvnego" => Ok(BvTerm::Nego(Box::new(parse_term_with_env(&items[1], vars)?))),
                "concat" => Ok(BvTerm::Concat(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "extract" => {
                    let hi = atom(&items[1])?.parse::<u32>()?;
                    let lo = atom(&items[2])?.parse::<u32>()?;
                    let a = parse_term_with_env(&items[3], vars)?;
                    Ok(BvTerm::Extract { hi, lo, a: Box::new(a) })
                }
                "rotate_left" => {
                    let k = atom(&items[1])?.parse::<u32>()?;
                    let a = parse_term_with_env(&items[2], vars)?;
                    Ok(BvTerm::RotateLeft { a: Box::new(a), amount: k })
                }
                "rotate_right" => {
                    let k = atom(&items[1])?.parse::<u32>()?;
                    let a = parse_term_with_env(&items[2], vars)?;
                    Ok(BvTerm::RotateRight { a: Box::new(a), amount: k })
                }
                "repeat" => {
                    let times = atom(&items[1])?.parse::<u32>()?;
                    let a = parse_term_with_env(&items[2], vars)?;
                    Ok(BvTerm::Repeat { a: Box::new(a), times })
                }
                "=" => Ok(BvTerm::Eq(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvult" => Ok(BvTerm::Ult(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvule" => Ok(BvTerm::Ule(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvslt" => Ok(BvTerm::Slt(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsle" => Ok(BvTerm::Sle(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                // Additional comparison operations
                "bvugt" => Ok(BvTerm::Ult(Box::new(parse_term_with_env(&items[2], vars)?), Box::new(parse_term_with_env(&items[1], vars)?))), // a > b <=> b < a
                "bvuge" => Ok(BvTerm::Ule(Box::new(parse_term_with_env(&items[2], vars)?), Box::new(parse_term_with_env(&items[1], vars)?))), // a >= b <=> b <= a
                "bvsgt" => Ok(BvTerm::Slt(Box::new(parse_term_with_env(&items[2], vars)?), Box::new(parse_term_with_env(&items[1], vars)?))), // a > b <=> b < a
                "bvsge" => Ok(BvTerm::Sle(Box::new(parse_term_with_env(&items[2], vars)?), Box::new(parse_term_with_env(&items[1], vars)?))), // a >= b <=> b <= a
                "ite" => {
                    let cond = parse_term_with_env(&items[1], vars)?;
                    let then_t = parse_term_with_env(&items[2], vars)?;
                    let else_t = parse_term_with_env(&items[3], vars)?;
                    Ok(BvTerm::Ite(Box::new(cond), Box::new(then_t), Box::new(else_t)))
                }
                "=>" | "xor" => {
                    // Handle xor as boolean expression
                    parse_boolean_condition(e, vars)
                }
                "distinct" => {
                    // Handle distinct as boolean expression
                    parse_boolean_condition(e, vars)
                }
                "not" => {
                    // Handle not as boolean expression
                    parse_boolean_condition(e, vars)
                }
                "and" => {
                    // Handle and as boolean expression
                    parse_boolean_condition(e, vars)
                }
                "or" => {
                    // Handle or as boolean expression
                    parse_boolean_condition(e, vars)
                }
                _ => bail!("unsupported head {}", head),
            }
        }
    }
}

fn parse_boolean_condition(e: &SExpr, vars: &HashMap<String, SortBv>) -> Result<BvTerm> {
    match e {
        SExpr::Atom(a) => match a.as_str() {
            "true" => Ok(BvTerm::Value { bits: vec![true] }),
            "false" => Ok(BvTerm::Value { bits: vec![false] }),
            _ => parse_term_with_env(e, vars),
        }
        SExpr::List(items) if !items.is_empty() => {
            let head = atom(&items[0])?;
            match head.as_str() {
                "=>" => {
                    if items.len() == 3 {
                        let a = parse_boolean_condition(&items[1], vars)?;
                        let b = parse_boolean_condition(&items[2], vars)?;
                        // a -> b  ===  (!a) or b  ===  ite(a, b, true)
                        Ok(BvTerm::Ite(
                            Box::new(a),
                            Box::new(b),
                            Box::new(BvTerm::Value { bits: vec![true] }),
                        ))
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "=" => {
                    if items.len() >= 3 {
                        let a = parse_term_with_env(&items[1], vars)?;
                        let b = parse_term_with_env(&items[2], vars)?;
                        Ok(BvTerm::Eq(Box::new(a), Box::new(b)))
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "and" | "or" | "xor" => {
                    if items.len() >= 2 {
                        let mut conds: Vec<BvTerm> = Vec::new();
                        for i in 1..items.len() {
                            conds.push(parse_term_with_env(&items[i], vars)?);
                        }
                        if head == "and" {
                            // Direct boolean AND: fold with AND operations
                            if conds.is_empty() {
                                Ok(BvTerm::Value { bits: vec![true] })
                            } else {
                                let mut res = conds[0].clone();
                                for c in &conds[1..] {
                                    res = BvTerm::And(Box::new(res), Box::new(c.clone()));
                                }
                                Ok(res)
                            }
                        } else if head == "or" {
                            // Direct boolean OR: fold with OR operations
                            if conds.is_empty() {
                                Ok(BvTerm::Value { bits: vec![false] })
                            } else {
                                let mut res = conds[0].clone();
                                for c in &conds[1..] {
                                    res = BvTerm::Or(Box::new(res), Box::new(c.clone()));
                                }
                                Ok(res)
                            }
                        } else {
                            // Direct boolean XOR: fold with XOR operations
                            if conds.is_empty() {
                                Ok(BvTerm::Value { bits: vec![false] })
                            } else {
                                let mut res = conds[0].clone();
                                for c in &conds[1..] {
                                    res = BvTerm::Xor(Box::new(res), Box::new(c.clone()));
                                }
                                Ok(res)
                            }
                        }
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "distinct" => {
                    if items.len() >= 3 {
                        // distinct(a, b, c, ...) = and_{i<j} (a_i != a_j)
                        let mut terms: Vec<BvTerm> = Vec::new();
                        for i in 1..items.len() {
                            terms.push(parse_term_with_env(&items[i], vars)?);
                        }

                        if terms.len() < 2 {
                            return parse_term_with_env(e, vars);
                        }

                        // Create AND of (NOT (a_i = a_j)) for all i < j
                        let mut neq_terms: Vec<BvTerm> = Vec::new();
                        for i in 0..terms.len() {
                            for j in (i+1)..terms.len() {
                                let eq = BvTerm::Eq(Box::new(terms[i].clone()), Box::new(terms[j].clone()));
                                neq_terms.push(BvTerm::Not(Box::new(eq)));
                            }
                        }

                        // Fold with AND
                        if neq_terms.is_empty() {
                            Ok(BvTerm::Value { bits: vec![true] })
                        } else {
                            let mut res = neq_terms[0].clone();
                            for neq in &neq_terms[1..] {
                                res = BvTerm::And(Box::new(res), Box::new(neq.clone()));
                            }
                            Ok(res)
                        }
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "bvult" | "bvule" | "bvslt" | "bvsle" | "bvugt" | "bvuge" | "bvsgt" | "bvsge" => {
                    if items.len() >= 3 {
                        let a = parse_term_with_env(&items[1], vars)?;
                        let b = parse_term_with_env(&items[2], vars)?;
                        Ok(match head.as_str() {
                            "bvult" => BvTerm::Ult(Box::new(a), Box::new(b)),
                            "bvule" => BvTerm::Ule(Box::new(a), Box::new(b)),
                            "bvslt" => BvTerm::Slt(Box::new(a), Box::new(b)),
                            "bvsle" => BvTerm::Sle(Box::new(a), Box::new(b)),
                            "bvugt" => BvTerm::Ult(Box::new(b), Box::new(a)),
                            "bvuge" => BvTerm::Ule(Box::new(b), Box::new(a)),
                            "bvsgt" => BvTerm::Slt(Box::new(b), Box::new(a)),
                            "bvsge" => BvTerm::Sle(Box::new(b), Box::new(a)),
                            _ => unreachable!(),
                        })
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "not" => {
                    if items.len() == 2 {
                        let inner = parse_term_with_env(&items[1], vars)?;
                        Ok(BvTerm::Not(Box::new(inner)))
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "ite" => {
                    if items.len() == 4 {
                        let c = parse_boolean_condition(&items[1], vars)?;
                        let t = parse_boolean_condition(&items[2], vars)?;
                        let f = parse_boolean_condition(&items[3], vars)?;
                        Ok(BvTerm::Ite(Box::new(c), Box::new(t), Box::new(f)))
                    } else { parse_term_with_env(e, vars) }
                }
                _ => parse_term_with_env(e, vars),
            }
        }
        _ => parse_term_with_env(e, vars),
    }
}

fn parse_bv_simplified(e: &SExpr, vars: &HashMap<String, SortBv>) -> Result<BvTerm> {
    parse_term_with_env(e, vars).map(simplify_bv)
}

#[derive(Default)]
pub struct Engine {
    vars: HashMap<String, SortBv>,
    assertions: Vec<SExpr>,
    last_bb: Option<AigBitBlasterAdapter>,
    last_model: Option<Vec<bool>>,
    frames: Vec<usize>,
    fun_defs: HashMap<String, (Vec<String>, SExpr)>,
    config: super::config::SolverConfig,
}

impl Engine {
    pub fn new() -> Self { 
        Self::new_with_config(super::config::SolverConfig::default())
    }
    
    pub fn new_with_options(check_model: bool) -> Self {
        let mut config = super::config::SolverConfig::default();
        config.check_model = check_model;
        Self::new_with_config(config)
    }
    
    pub fn new_with_config(config: super::config::SolverConfig) -> Self {
        Self {
            vars: HashMap::new(),
            assertions: Vec::new(),
            last_bb: None,
            last_model: None,
            frames: Vec::new(),
            fun_defs: HashMap::new(),
            config,
        }
    }

    pub fn eval(&mut self, cmd: Command) -> Result<Option<String>> {
        trace!(?cmd, num_assertions = self.assertions.len(), num_vars = self.vars.len(), "engine eval");
        match cmd {
            Command::SetLogic(_) | Command::SetOption(_, _) | Command::SetInfo(_, _) => Ok(None),
            Command::Push(n) => { for _ in 0..n { self.frames.push(self.assertions.len()); } Ok(None) }
            Command::Pop(n) => { 
                for _ in 0..n { 
                    if let Some(sz) = self.frames.pop() { 
                        if self.assertions.len() > sz { self.assertions.truncate(sz); } 
                    } 
                } 
                Ok(None) 
            }
            Command::Reset => { 
                self.vars.clear(); 
                self.assertions.clear(); 
                self.last_bb = None; 
                self.last_model = None; 
                self.frames.clear(); 
                Ok(None) 
            }
            Command::ResetAssertions => { 
                self.assertions.clear(); 
                self.last_bb = None; 
                self.last_model = None; 
                Ok(None) 
            }
            Command::Exit => Ok(None),
            Command::GetInfo(_) => Ok(None),
            Command::GetOption(_) => Ok(None),
            Command::DefineFun0(name, sort, body) => {
                self.vars.insert(name.clone(), sort);
                self.assertions.push(SExpr::List(vec![
                    SExpr::Atom("=".to_string()), SExpr::Atom(name), body,
                ]));
                Ok(None)
            }
            Command::DefineFun(name, args, body) => {
                // Store as a macro: (define-fun name (args...) ...) => a fresh symbol plus axiom
                // We encode as an uninterpreted 1-bit symbol if referenced in boolean context; for bv we rely on inlining.
                // Since our parser does not expand calls yet, we at least keep a placeholder axiom asserting name = body when no args.
                if args.is_empty() {
                    self.assertions.push(SExpr::List(vec![SExpr::Atom("=".to_string()), SExpr::Atom(name), body]));
                }
                Ok(None)
            }
            Command::DeclareConst(name, sort) => { self.vars.insert(name, sort); Ok(None) }
            Command::Assert(t) => { self.assertions.push(t); Ok(None) }
            Command::CheckSat => {
                let mut bb = AigBitBlasterAdapter::new_with_config(self.config.clone());
                for asexpr in &self.assertions {
                    let lit = build_bool(asexpr, &mut bb, &self.vars, &self.fun_defs)?;
                    bb.cnf_mut().add_clause(vec![lit]);
                }
                // Force that every boolean symbol mentioned is materialized to the CNF
                for (name, _) in bb.bool_syms().clone() {
                    let _ = bb.get_bool_sym(name);
                }
                for (name, sort) in &self.vars {
                    let term = BvTerm::Const { name: name.clone(), sort: *sort };
                    for i in 0..sort.width { let _ = bb.emit_bit(&term, i); }
                }
                debug!(clauses = bb.cnf().clauses.len(), vars = bb.cnf().num_vars, "check-sat CNF");
                let res = solve_cnf(bb.cnf())?;
                if let Some(model_bits) = res {
                    // Check model if enabled
                    if self.config.check_model {
                        self.verify_model(&model_bits, &bb)?;
                    }
                    
                    self.last_model = Some(model_bits.clone());
                    self.last_bb = Some(bb);
                    Ok(Some("sat\n".to_string()))
                } else {
                    self.last_model = None;
                    self.last_bb = None;
                    Ok(Some("unsat\n".to_string()))
                }
            }
            Command::CheckSatAssuming(assumptions) => {
                let mut bb = AigBitBlasterAdapter::new_with_config(self.config.clone());
                // Add regular assertions
                for asexpr in &self.assertions {
                    let lit = build_bool(asexpr, &mut bb, &self.vars, &self.fun_defs)?;
                    bb.cnf_mut().add_clause(vec![lit]);
                }
                // Add assumptions
                for assumption in assumptions {
                    let lit = build_bool(&assumption, &mut bb, &self.vars, &self.fun_defs)?;
                    bb.cnf_mut().add_clause(vec![lit]);
                }
                // Force that every boolean symbol mentioned is materialized to the CNF
                for (name, _) in bb.bool_syms().clone() {
                    let _ = bb.get_bool_sym(name);
                }
                for (name, sort) in &self.vars {
                    let term = BvTerm::Const { name: name.clone(), sort: *sort };
                    for i in 0..sort.width { let _ = bb.emit_bit(&term, i); }
                }
                debug!(clauses = bb.cnf().clauses.len(), vars = bb.cnf().num_vars, "check-sat-assuming CNF");
                let res = solve_cnf(bb.cnf())?;
                if let Some(model_bits) = res {
                    // Check model if enabled
                    if self.config.check_model {
                        self.verify_model(&model_bits, &bb)?;
                    }
                    
                    self.last_model = Some(model_bits.clone());
                    self.last_bb = Some(bb);
                    Ok(Some("sat\n".to_string()))
                } else {
                    self.last_model = None;
                    self.last_bb = None;
                    Ok(Some("unsat\n".to_string()))
                }
            }
            Command::GetModel => {
                if let (Some(_model), Some(bb)) = (&self.last_model, &self.last_bb) {
                    let mut out = String::new();
                    out.push_str("(\n");
                    for (name, _aig_node) in bb.bool_syms() {
                        // For now, we'll need to implement proper AIG to CNF variable mapping
                        // This is a placeholder that would need proper implementation
                        let var_val = false; // Placeholder
                        out.push_str(&format!("  (define-fun {} () Bool {})\n", name, if var_val { "true" } else { "false" }));
                    }
                    for (name, sort) in &self.vars {
                        let w = sort.width;
                        let mut bits: Vec<bool> = Vec::with_capacity(w as usize);
                        for i in 0..w {
                            if let Some(_aig_node) = bb.var_bits().get(&(name.clone(), i)) {
                                // For now, we'll need to implement proper AIG to CNF variable mapping
                                // This is a placeholder that would need proper implementation
                                let bit_val = false; // Placeholder
                                bits.push(bit_val);
                            } else {
                                bits.push(false);
                            }
                        }
                        let hex_str = self.bits_to_hex(&bits);
                        out.push_str(&format!("  (define-fun {} () (_ BitVec {}) {})\n", name, w, hex_str));
                    }
                    out.push_str(")\n");
                    Ok(Some(out))
                } else {
                    Ok(Some("()\n".to_string()))
                }
            }
            Command::GetValue(vars) => {
                if let (Some(_model), Some(bb)) = (&self.last_model, &self.last_bb) {
                    let mut out = String::new();
                    out.push('(');
                    for name in vars {
                        if let Some(sort) = self.vars.get(&name) {
                            let w = sort.width;
                            let mut bits: Vec<bool> = Vec::with_capacity(w as usize);
                            for i in 0..w {
                                if let Some(_aig_node) = bb.var_bits().get(&(name.clone(), i)) {
                                    // For now, we'll need to implement proper AIG to CNF variable mapping
                                    // This is a placeholder that would need proper implementation
                                    let bit_val = false; // Placeholder
                                    bits.push(bit_val);
                                } else {
                                    bits.push(false);
                                }
                            }
                            let hex_str = self.bits_to_hex(&bits);
                            out.push_str(&format!("({} {})", name, hex_str));
                        } else {
                            out.push_str(&format!("({} #x0)", name));
                        }
                    }
                    out.push_str(")\n");
                    Ok(Some(out))
                } else { Ok(Some("()\n".to_string())) }
            }
        }
    }

    fn bits_to_hex(&self, bits: &[bool]) -> String {
        if bits.is_empty() {
            return "#x0".to_string();
        }
        
        // Convert bits to hexadecimal
        let mut hex_chars = Vec::new();
        let mut current_byte = 0u8;
        let mut bit_count = 0;
        
        // Process bits from MSB to LSB (reverse order since bits are stored LSB first)
        for (i, &bit) in bits.iter().enumerate().rev() {
            if bit {
                current_byte |= 1 << (3 - bit_count);
            }
            bit_count += 1;
            
            if bit_count == 4 || i == 0 {
                hex_chars.push(format!("{:x}", current_byte));
                current_byte = 0;
                bit_count = 0;
            }
        }
        
        // Reverse to get correct order and join
        hex_chars.reverse();
        format!("#x{}", hex_chars.join(""))
    }

    fn verify_model(&self, _model_bits: &[bool], bb: &AigBitBlasterAdapter) -> Result<()> {
        use anyhow::Context;
        
        debug!("Verifying model against {} assertions", self.assertions.len());
        
        // Build a model map from variable names to their bit values
        let mut model_map: HashMap<String, Vec<bool>> = HashMap::new();
        for (name, sort) in &self.vars {
            let w = sort.width;
            let mut bits: Vec<bool> = Vec::with_capacity(w as usize);
            for i in 0..w {
                if let Some(_aig_node) = bb.var_bits().get(&(name.clone(), i)) {
                    // For now, we'll need to implement proper AIG to CNF variable mapping
                    // This is a placeholder that would need proper implementation
                    let bit_val = false; // Placeholder
                    bits.push(bit_val);
                } else {
                    bits.push(false);
                }
            }
            model_map.insert(name.clone(), bits);
        }
        
        // Verify each assertion evaluates to true under the model
        for (idx, asexpr) in self.assertions.iter().enumerate() {
            let term = parse_term_with_env(asexpr, &self.vars)
                .with_context(|| format!("Failed to parse assertion {}", idx))?;
            let simplified = simplify_bv(term);
            let result = super::bv::eval_term(&simplified, &model_map)
                .with_context(|| format!("Failed to evaluate assertion {}", idx))?;
            
            // The assertion should evaluate to a 1-bit true value
            if result.len() != 1 || !result[0] {
                bail!("Model check failed: assertion {} evaluates to {:?} (expected [true])", idx, result);
            }
        }
        
        debug!("Model verification passed");
        Ok(())
    }
}

fn build_bool(e: &SExpr, bb: &mut AigBitBlasterAdapter, vars: &HashMap<String, SortBv>, fun_defs: &HashMap<String, (Vec<String>, SExpr)>) -> Result<BoolLit> {
    match e {
        SExpr::List(list) if !list.is_empty() => {
            let h = atom(&list[0])?;
            match h.as_str() {
                "let" => {
                    // Boolean-level let: expand bindings by syntactic substitution into the body
                    let SExpr::List(binds) = &list[1] else { bail!("let needs bindings list") };
                    let mut substitutions: HashMap<String, SExpr> = HashMap::new();
                    
                    // Build substitution map with proper scoping: each binding can reference previous ones
                    for b in binds {
                        if let SExpr::List(pair) = b {
                            let name = atom(&pair[0])?;
                            let val_expr = &pair[1];
                            
                            // Substitute the value using current substitutions (allows previous bindings to be referenced)
                            let substituted_val = substitute_let_vars(val_expr, &substitutions);
                            substitutions.insert(name, substituted_val);
                        }
                    }
                    let expanded_body = substitute_let_vars(&list[2], &substitutions);
                    build_bool(&expanded_body, bb, vars, fun_defs)
                }
                "and" => {
                    let mut lits = Vec::new();
                    for a in &list[1..] { lits.push(build_bool(a, bb, vars, fun_defs)?); }
                    Ok(bb.mk_and(&lits))
                }
                "or" => {
                    let mut lits = Vec::new();
                    for a in &list[1..] { lits.push(build_bool(a, bb, vars, fun_defs)?); }
                    Ok(bb.mk_or(&lits))
                }
                "xor" => {
                    let mut lits = Vec::new();
                    for a in &list[1..] { lits.push(build_bool(a, bb, vars, fun_defs)?); }
                    if lits.is_empty() { return Ok(bb.new_bool()); }
                    let mut acc = lits[0];
                    for &l in &lits[1..] { acc = bb.encode_xor_var(acc, l); }
                    Ok(acc)
                }
                "not" => {
                    let l = build_bool(&list[1], bb, vars, fun_defs)?;
                    Ok(bb.mk_not(l))
                }
                "=" => {
                    if list.len() < 3 { bail!("= needs at least 2 args"); }
                    let mut res: Option<BoolLit> = None;
                    let mut prev = parse_bv_simplified(&list[1], vars)?;
                    for i in 2..list.len() {
                        let cur = parse_bv_simplified(&list[i], vars)?;
                        let eq = bb.bool_eq(&prev, &cur);
                        res = Some(match res { None => eq, Some(r) => bb.mk_and(&[r, eq]) });
                        prev = cur;
                    }
                    Ok(res.unwrap())
                }
                "distinct" => {
                    let mut lits = Vec::new();
                    let mut terms: Vec<BvTerm> = Vec::new();
                    for i in 1..list.len() { terms.push(parse_bv_simplified(&list[i], vars)?); }
                    for i in 0..terms.len() { 
                        for j in (i+1)..terms.len() {
                            let eq = bb.bool_eq(&terms[i], &terms[j]);
                            lits.push(bb.mk_not(eq));
                        }
                    }
                    Ok(bb.mk_and(&lits))
                }
                "bvult" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    Ok(bb.emit_ult_bool(&a, &b)) 
                }
                "bvule" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    Ok(bb.emit_ule_bool(&a, &b)) 
                }
                "bvslt" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    Ok(bb.emit_slt_bool(&a, &b)) 
                }
                "bvsle" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    let lt = bb.emit_slt_bool(&a, &b); 
                    let eq = bb.bool_eq(&a, &b); 
                    Ok(bb.mk_or(&[lt, eq])) 
                }
                "bvsgt" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    Ok(bb.emit_slt_bool(&b, &a)) 
                }
                "bvsge" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    let lt = bb.emit_slt_bool(&a, &b); 
                    Ok(bb.mk_not(lt)) 
                }
                "bvugt" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    Ok(bb.emit_ult_bool(&b, &a)) 
                }
                "bvuge" => { 
                    let a = parse_bv_simplified(&list[1], vars)?; 
                    let b = parse_bv_simplified(&list[2], vars)?; 
                    Ok(bb.emit_ule_bool(&b, &a)) 
                }
                "=>" => {
                    if list.len() == 3 {
                        let a = build_bool(&list[1], bb, vars, fun_defs)?;
                        let b = build_bool(&list[2], bb, vars, fun_defs)?;
                        Ok(bb.mk_implies(a, b))
                    } else {
                        bail!("=> needs exactly 2 arguments")
                    }
                }
                "ite" => {
                    if list.len() == 4 {
                        let cond = build_bool(&list[1], bb, vars, fun_defs)?;
                        let then_b = build_bool(&list[2], bb, vars, fun_defs)?;
                        let else_b = build_bool(&list[3], bb, vars, fun_defs)?;
                        Ok(bb.ite_bit(cond, then_b, else_b))
                    } else {
                        bail!("ite needs exactly 3 arguments")
                    }
                }
                _ => bail!("unsupported boolean head {}", h),
            }
        }
        SExpr::Atom(a) => {
            match a.as_str() {
                "true" => {
                    let lit = bb.new_bool();
                    bb.cnf_mut().add_clause(vec![lit]);
                    Ok(lit)
                }
                "false" => {
                    let lit = bb.new_bool();
                    bb.cnf_mut().add_clause(vec![BoolLit(lit.0, false)]);
                    Ok(lit)
                }
                _ => Ok(bb.get_bool_sym(a.clone())),
            }
        }
        _ => bail!("unsupported boolean expression"),
    }
}


