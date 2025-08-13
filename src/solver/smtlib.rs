use std::collections::HashMap;
use anyhow::{bail, Context, Result};
use super::sexpr::{parse_all, SExpr};
use super::bv::{BvTerm, SortBv, BoolLit};
use super::cnf::BitBlaster;
use super::sat::solve_cnf;
use super::rewrites::simplify_bv;

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
            let substituted_items: Vec<SExpr> = items.iter()
                .map(|item| substitute_let_vars(item, substitutions))
                .collect();
            SExpr::List(substituted_items)
        }
    }
}

fn expand_let_bindings(bindings_expr: &SExpr, body_expr: &SExpr, vars: &HashMap<String, SortBv>) -> Result<BvTerm> {
    let SExpr::List(binds) = bindings_expr else { bail!("let needs bindings list") };
    
    // Recursively expand all let bindings by substituting them into the body
    let mut current_body = body_expr.clone();
    
    for b in binds {
        if let SExpr::List(pair) = b {
            let name = atom(&pair[0])?;
            let val_expr = &pair[1];
            
            // Create substitution map for this binding
            let mut substitutions = HashMap::new();
            substitutions.insert(name, val_expr.clone());
            
            // Apply substitution to current body
            current_body = substitute_let_vars(&current_body, &substitutions);
        }
    }
    
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
    parse_all(input)?.into_iter().map(|e| parse_command(&e)).collect()
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
            let name = normalize_ident(&atom(&list[1])?);
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
            let name = normalize_ident(&atom(&list[1])?);
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
        let bits: Vec<bool> = s[2..].chars().map(|c| c == '1').collect();
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
            match head.as_str() {
                "=>" => {
                    // Treat boolean implication at term level as boolean condition
                    // so it can appear under ite, not/and/or contexts if needed.
                    let a = parse_boolean_condition(&items[1], vars)?;
                    let b = parse_boolean_condition(&items[2], vars)?;
                    Ok(BvTerm::Ite(
                        Box::new(a),
                        Box::new(b.clone()),
                        Box::new(BvTerm::Not(Box::new(b)))
                    ))
                }
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
                    let cond = parse_boolean_condition(&items[1], vars)?;
                    let then_t = parse_term_with_env(&items[2], vars)?;
                    let else_t = parse_term_with_env(&items[3], vars)?;
                    Ok(BvTerm::Ite(Box::new(cond), Box::new(then_t), Box::new(else_t)))
                }
                "xor" => {
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
                        for i in 1..items.len() { conds.push(parse_term_with_env(&items[i], vars)?); }
                        if head == "and" {
                            // res = fold: Ite(c_i, res, false) with res starting at true
                            let mut res = BvTerm::Value { bits: vec![true] };
                            for c in conds {
                                res = BvTerm::Ite(Box::new(c), Box::new(res), Box::new(BvTerm::Value { bits: vec![false] }));
                            }
                            Ok(res)
                        } else if head == "or" {
                            // OR: res = fold: Ite(c_i, true, res) with res starting at false
                            let mut res = BvTerm::Value { bits: vec![false] };
                            for c in conds {
                                res = BvTerm::Ite(Box::new(c), Box::new(BvTerm::Value { bits: vec![true] }), Box::new(res));
                            }
                            Ok(res)
                        } else {
                            // XOR: chain XOR operations
                            if conds.is_empty() {
                                Ok(BvTerm::Value { bits: vec![false] })
                            } else {
                                let mut res = conds[0].clone();
                                for c in &conds[1..] {
                                    // res XOR c = Ite(res, Not(c), c)
                                    let not_c = BvTerm::Ite(Box::new(c.clone()), Box::new(BvTerm::Value { bits: vec![false] }), Box::new(BvTerm::Value { bits: vec![true] }));
                                    res = BvTerm::Ite(Box::new(res), Box::new(not_c), Box::new(c.clone()));
                                }
                                Ok(res)
                            }
                        }
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "distinct" => {
                    if items.len() == 3 {
                        let a = parse_term_with_env(&items[1], vars)?;
                        let b = parse_term_with_env(&items[2], vars)?;
                        Ok(BvTerm::Not(Box::new(BvTerm::Eq(Box::new(a), Box::new(b)))))
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
                        let inner = parse_boolean_condition(&items[1], vars)?;
                        Ok(BvTerm::Ite(Box::new(inner), Box::new(BvTerm::Value { bits: vec![false] }), Box::new(BvTerm::Value { bits: vec![true] })))
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
    last_bb: Option<BitBlaster>,
    last_model: Option<Vec<bool>>,
    frames: Vec<usize>,
    fun_defs: HashMap<String, (Vec<String>, SExpr)>,
}

impl Engine {
    pub fn new() -> Self { Self::default() }

    pub fn eval(&mut self, cmd: Command) -> Result<Option<String>> {
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
                let mut bb = BitBlaster::new();
                for asexpr in &self.assertions {
                    let lit = build_bool(asexpr, &mut bb, &self.vars, &self.fun_defs)?;
                    bb.cnf.add_clause(vec![lit]);
                }
                // Force that every boolean symbol mentioned is materialized to the CNF
                for (name, _) in bb.bool_syms.clone() {
                    let _ = bb.get_bool_sym(name);
                }
                for (name, sort) in &self.vars {
                    let term = BvTerm::Const { name: name.clone(), sort: *sort };
                    for i in 0..sort.width { let _ = bb.emit_bit(&term, i); }
                }
                let res = solve_cnf(&bb.cnf)?;
                if let Some(model_bits) = res {
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
                let mut bb = BitBlaster::new();
                // Add regular assertions
                for asexpr in &self.assertions {
                    let lit = build_bool(asexpr, &mut bb, &self.vars, &self.fun_defs)?;
                    bb.cnf.add_clause(vec![lit]);
                }
                // Add assumptions
                for assumption in assumptions {
                    let lit = build_bool(&assumption, &mut bb, &self.vars, &self.fun_defs)?;
                    bb.cnf.add_clause(vec![lit]);
                }
                // Force that every boolean symbol mentioned is materialized to the CNF
                for (name, _) in bb.bool_syms.clone() {
                    let _ = bb.get_bool_sym(name);
                }
                for (name, sort) in &self.vars {
                    let term = BvTerm::Const { name: name.clone(), sort: *sort };
                    for i in 0..sort.width { let _ = bb.emit_bit(&term, i); }
                }
                let res = solve_cnf(&bb.cnf)?;
                if let Some(model_bits) = res {
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
                if let (Some(model), Some(bb)) = (&self.last_model, &self.last_bb) {
                    let mut out = String::new();
                    out.push_str("(model\n");
                    for (name, lit) in &bb.bool_syms {
                        let val = model[lit.0];
                        out.push_str(&format!("  (define-fun {} () Bool {})\n", name, if val { "true" } else { "false" }));
                    }
                    for (name, sort) in &self.vars {
                        let w = sort.width;
                        let mut bits: Vec<bool> = Vec::with_capacity(w as usize);
                        for i in 0..w {
                            if let Some(&lit) = bb.var_bits.get(&(name.clone(), i)) {
                                bits.push(model[lit.0]);
                            } else {
                                bits.push(false);
                            }
                        }
                        let mut s = String::from("#b");
                        for i in (0..bits.len()).rev() { s.push(if bits[i] { '1' } else { '0' }); }
                        out.push_str(&format!("  (define-fun {} () (_ BitVec {}) {})\n", name, w, s));
                    }
                    out.push_str(")\n");
                    Ok(Some(out))
                } else {
                    Ok(Some("(model)\n".to_string()))
                }
            }
            Command::GetValue(vars) => {
                if let (Some(model), Some(bb)) = (&self.last_model, &self.last_bb) {
                    let mut out = String::new();
                    out.push('(');
                    for name in vars {
                        if let Some(sort) = self.vars.get(&name) {
                            let w = sort.width;
                            let mut bits: Vec<bool> = Vec::with_capacity(w as usize);
                            for i in 0..w {
                                if let Some(&lit) = bb.var_bits.get(&(name.clone(), i)) {
                                    bits.push(model[lit.0]);
                                } else {
                                    bits.push(false);
                                }
                            }
                            let mut s = String::from("#b");
                            for i in (0..bits.len()).rev() { s.push(if bits[i] { '1' } else { '0' }); }
                            out.push_str(&format!("({} {})", name, s));
                        } else {
                            out.push_str(&format!("({} #b0)", name));
                        }
                    }
                    out.push_str(")\n");
                    Ok(Some(out))
                } else { Ok(Some("()\n".to_string())) }
            }
        }
    }
}

fn build_bool(e: &SExpr, bb: &mut BitBlaster, vars: &HashMap<String, SortBv>, fun_defs: &HashMap<String, (Vec<String>, SExpr)>) -> Result<BoolLit> {
    match e {
        SExpr::List(list) if !list.is_empty() => {
            let h = atom(&list[0])?;
            match h.as_str() {
                "let" => {
                    // Boolean-level let: expand bindings by syntactic substitution into the body
                    let SExpr::List(binds) = &list[1] else { bail!("let needs bindings list") };
                    let mut substitutions: HashMap<String, SExpr> = HashMap::new();
                    for b in binds {
                        if let SExpr::List(pair) = b {
                            let name = atom(&pair[0])?;
                            let val_expr = pair[1].clone();
                            substitutions.insert(name, val_expr);
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
                    bb.cnf.add_clause(vec![lit]);
                    Ok(lit)
                }
                "false" => {
                    let lit = bb.new_bool();
                    bb.cnf.add_clause(vec![BoolLit(lit.0, false)]);
                    Ok(lit)
                }
                _ => Ok(bb.get_bool_sym(a.clone())),
            }
        }
        _ => bail!("unsupported boolean expression"),
    }
}


