use std::collections::HashMap;
use anyhow::{bail, Context, Result};
use super::sexpr::{parse_all, SExpr};
use super::bv::{BvTerm, SortBv, BoolLit};
use super::cnf::BitBlaster;
use super::sat::solve_cnf;
use super::rewrites::simplify_bv;

#[derive(Debug, Clone)]
pub enum Command {
    SetLogic(String), SetOption(String, String), SetInfo(String, String),
    DeclareConst(String, SortBv), Assert(SExpr), CheckSat, GetModel,
    Push(u32), Pop(u32), GetValue(Vec<String>), Reset, ResetAssertions, Exit,
    DefineFun0(String, SortBv, SExpr),
}

pub fn parse_script(input: &str) -> Result<Vec<Command>> {
    parse_all(input)?.into_iter().map(|e| parse_command(&e)).collect()
}

fn parse_command(e: &SExpr) -> Result<Command> {
    let SExpr::List(list) = e else { bail!("expected command list") };
    if list.is_empty() { bail!("empty command") };
    
    let head = atom(&list[0])?;
    match head.as_str() {
        "set-logic" | "set-option" | "set-info" => {
            if list.len() < 3 { bail!("insufficient args for {}", head) };
            Ok(match head.as_str() {
                "set-logic" => Command::SetLogic(atom(&list[1])?),
                "set-option" => Command::SetOption(atom(&list[1])?, atom(&list[2])?),
                _ => Command::SetInfo(atom(&list[1])?, atom(&list[2])?),
            })
        }
        "declare-fun" | "declare-const" => {
            let name = atom(&list[1])?;
            let sort = if head == "declare-fun" {
                let SExpr::List(args) = &list[2] else { bail!("declare-fun needs args list") };
                if !args.is_empty() { bail!("only zero-arity declare-fun supported") };
                parse_sort(&list[3])?
            } else {
                parse_sort(&list[2])?
            };
            if sort.width == 0 { // Bool case
                Ok(Command::SetInfo("decl-bool".to_string(), name))
            } else {
                Ok(Command::DeclareConst(name, sort))
            }
        }
        "define-fun" => {
            let name = atom(&list[1])?;
            let SExpr::List(args) = &list[2] else { bail!("define-fun needs args list") };
            if !args.is_empty() { bail!("only zero-arity define-fun supported") };
            let sort = parse_sort(&list[3])?;
            Ok(Command::DefineFun0(name, sort, list[4].clone()))
        }
        "push" | "pop" => {
            let n = atom(&list[1])?.parse::<u32>()?;
            Ok(if head == "push" { Command::Push(n) } else { Command::Pop(n) })
        }
        "assert" => Ok(Command::Assert(list[1].clone())),
        "check-sat" => Ok(Command::CheckSat),
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

fn atom(e: &SExpr) -> Result<String> {
    match e { SExpr::Atom(s) => Ok(s.clone()), _ => bail!("expected atom") }
}

fn parse_sort(e: &SExpr) -> Result<SortBv> {
    let SExpr::List(items) = e else { bail!("unsupported sort") };
    if items.len() == 3 && atom(&items[0])? == "_" && atom(&items[1])? == "BitVec" {
        let w = atom(&items[2])?.parse::<u32>().context("width parse")?;
        Ok(SortBv { width: w })
    } else {
        bail!("unsupported sort expression")
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
            if let Some(sort) = vars.get(a) { return Ok(BvTerm::Const { name: a.clone(), sort: *sort }); }
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
                "let" => {
                    let mut local = vars.clone();
                    let SExpr::List(binds) = &items[1] else { bail!("let needs bindings list") };
                    for b in binds {
                        if let SExpr::List(pair) = b {
                            let name = atom(&pair[0])?;
                            let val = parse_term_with_env(&pair[1], &local)?;
                            if let Some(sort) = val.sort() { local.insert(name, sort); }
                        }
                    }
                    parse_term_with_env(&items[2], &local)
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
                "bvand" => Ok(BvTerm::And(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvor" => Ok(BvTerm::Or(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvxor" => Ok(BvTerm::Xor(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvadd" => Ok(BvTerm::Add(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvsub" => Ok(BvTerm::Sub(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvmul" => Ok(BvTerm::Mul(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvshl" => Ok(BvTerm::Shl(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvlshr" => Ok(BvTerm::Lshr(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvashr" => Ok(BvTerm::Ashr(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvudiv" => Ok(BvTerm::Udiv(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
                "bvurem" => Ok(BvTerm::Urem(Box::new(parse_term_with_env(&items[1], vars)?), Box::new(parse_term_with_env(&items[2], vars)?))),
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
                "ite" => {
                    let cond = parse_boolean_condition(&items[1], vars)?;
                    let then_t = parse_term_with_env(&items[2], vars)?;
                    let else_t = parse_term_with_env(&items[3], vars)?;
                    Ok(BvTerm::Ite(Box::new(cond), Box::new(then_t), Box::new(else_t)))
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
                "and" | "or" => {
                    if items.len() >= 2 {
                        let mut conds: Vec<BvTerm> = Vec::new();
                        for i in 1..items.len() { conds.push(parse_term_with_env(&items[i], vars)?); }
                        if head == "and" {
                            // Build nested ITEs for AND
                            let mut res = conds.last().unwrap().clone();
                            for c in conds.iter().rev().skip(1) {
                                res = BvTerm::Ite(Box::new(c.clone()), Box::new(res), Box::new(BvTerm::Value { bits: vec![false] }));
                            }
                            Ok(conds[0].clone())
                        } else {
                            // Build nested ITEs for OR
                            let mut res = BvTerm::Value { bits: vec![false] };
                            for c in conds.iter().rev() {
                                res = BvTerm::Ite(Box::new(c.clone()), Box::new(BvTerm::Value { bits: vec![true] }), Box::new(res));
                            }
                            Ok(conds[0].clone())
                        }
                    } else {
                        parse_term_with_env(e, vars)
                    }
                }
                "distinct" => {
                    if items.len() == 3 {
                        let a = parse_term_with_env(&items[1], vars)?;
                        let b = parse_term_with_env(&items[2], vars)?;
                        Ok(BvTerm::Eq(Box::new(a), Box::new(b)))
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
                        // For not, we'll handle the negation in the ITE construction
                        Ok(inner)
                    } else {
                        parse_term_with_env(e, vars)
                    }
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
            Command::DefineFun0(name, sort, body) => {
                self.vars.insert(name.clone(), sort);
                self.assertions.push(SExpr::List(vec![
                    SExpr::Atom("=".to_string()), SExpr::Atom(name), body,
                ]));
                Ok(None)
            }
            Command::DeclareConst(name, sort) => { self.vars.insert(name, sort); Ok(None) }
            Command::Assert(t) => { self.assertions.push(t); Ok(None) }
            Command::CheckSat => {
                let mut bb = BitBlaster::new();
                for asexpr in &self.assertions {
                    let lit = build_bool(asexpr, &mut bb, &self.vars)?;
                    bb.cnf.add_clause(vec![lit]);
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

fn build_bool(e: &SExpr, bb: &mut BitBlaster, vars: &HashMap<String, SortBv>) -> Result<BoolLit> {
    match e {
        SExpr::List(list) if !list.is_empty() => {
            let h = atom(&list[0])?;
            match h.as_str() {
                "let" => {
                    let SExpr::List(binds) = &list[1] else { bail!("let needs bindings list") };
                    let mut local = vars.clone();
                    for b in binds { 
                        if let SExpr::List(pair) = b { 
                            let name = atom(&pair[0])?; 
                            let val = parse_bv_simplified(&pair[1], &local)?; 
                            if let Some(sort) = val.sort() { local.insert(name, sort); } 
                        } 
                    }
                    build_bool(&list[2], bb, &local)
                }
                "and" => {
                    let mut lits = Vec::new();
                    for a in &list[1..] { lits.push(build_bool(a, bb, vars)?); }
                    Ok(bb.mk_and(&lits))
                }
                "or" => {
                    let mut lits = Vec::new();
                    for a in &list[1..] { lits.push(build_bool(a, bb, vars)?); }
                    Ok(bb.mk_or(&lits))
                }
                "xor" => {
                    let mut lits = Vec::new();
                    for a in &list[1..] { lits.push(build_bool(a, bb, vars)?); }
                    if lits.is_empty() { return Ok(bb.new_bool()); }
                    let mut acc = lits[0];
                    for &l in &lits[1..] { acc = bb.encode_xor_var(acc, l); }
                    Ok(acc)
                }
                "not" => {
                    let l = build_bool(&list[1], bb, vars)?;
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


