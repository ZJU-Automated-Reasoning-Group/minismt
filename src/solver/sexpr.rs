use anyhow::{bail, Result};

#[derive(Debug, Clone, PartialEq)]
pub enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

pub fn parse_all(input: &str) -> Result<Vec<SExpr>> {
    let mut p = Parser { s: input, i: 0 };
    let mut exprs = Vec::new();
    while p.skip_ws() {
        let e = p.parse_expr()?;
        exprs.push(e);
    }
    Ok(exprs)
}

struct Parser<'a> {
    s: &'a str,
    i: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<char> {
        self.s[self.i..].chars().next()
    }

    fn bump(&mut self) -> Option<char> {
        if let Some(ch) = self.peek() {
            self.i += ch.len_utf8();
            Some(ch)
        } else {
            None
        }
    }

    fn skip_ws(&mut self) -> bool {
        loop {
            while self.peek().map_or(false, |c| c.is_whitespace()) {
                self.bump();
            }
            if self.peek() == Some(';') {
                while let Some(c) = self.bump() {
                    if c == '\n' { break; }
                }
                continue;
            }
            break;
        }
        self.i < self.s.len()
    }

    fn parse_expr(&mut self) -> Result<SExpr> {
        match self.peek() {
            Some('(') => self.parse_list(),
            Some(')') => bail!("unexpected closing paren"),
            Some(_) => self.parse_atom(),
            None => bail!("unexpected end of input"),
        }
    }

    fn parse_list(&mut self) -> Result<SExpr> {
        assert_eq!(self.bump(), Some('('));
        let mut items = Vec::new();
        loop {
            self.skip_ws();
            match self.peek() {
                Some(')') => { self.bump(); break; }
                Some(_) => items.push(self.parse_expr()?),
                None => bail!("unterminated list"),
            }
        }
        Ok(SExpr::List(items))
    }

    fn parse_atom(&mut self) -> Result<SExpr> {
        // FIXME: this is not elegant
        if self.peek() == Some('|') {
            // Quoted symbol: read everything until the next '|'
            assert_eq!(self.bump(), Some('|'));
            let mut s = String::new();
            while let Some(c) = self.peek() {
                if c == '|' {
                    self.bump();
                    break;
                }
                s.push(c);
                self.bump();
            }
            return Ok(SExpr::Atom(s));
        }
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_whitespace() || c == '(' || c == ')' { break; }
            s.push(c);
            self.bump();
        }
        Ok(SExpr::Atom(s))
    }
}


