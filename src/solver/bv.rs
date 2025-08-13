

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SortBv {
    pub width: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BvTerm {
    Const { name: String, sort: SortBv },
    Value { bits: Vec<bool> },
    Not(Box<BvTerm>),
    And(Box<BvTerm>, Box<BvTerm>),
    Or(Box<BvTerm>, Box<BvTerm>),
    Xor(Box<BvTerm>, Box<BvTerm>),
    Add(Box<BvTerm>, Box<BvTerm>),
    Sub(Box<BvTerm>, Box<BvTerm>),
    Mul(Box<BvTerm>, Box<BvTerm>),
    Udiv(Box<BvTerm>, Box<BvTerm>),
    Urem(Box<BvTerm>, Box<BvTerm>),
    Shl(Box<BvTerm>, Box<BvTerm>),
    Lshr(Box<BvTerm>, Box<BvTerm>),
    Ashr(Box<BvTerm>, Box<BvTerm>),
    Neg(Box<BvTerm>),
    Concat(Box<BvTerm>, Box<BvTerm>),
    Extract { hi: u32, lo: u32, a: Box<BvTerm> },
    Eq(Box<BvTerm>, Box<BvTerm>),
    Ult(Box<BvTerm>, Box<BvTerm>),
    Ule(Box<BvTerm>, Box<BvTerm>),
    Slt(Box<BvTerm>, Box<BvTerm>),
    Sle(Box<BvTerm>, Box<BvTerm>),
    Ite(Box<BvTerm>, Box<BvTerm>, Box<BvTerm>), // cond (bool from Eq/Ult/Ule), then, else
    SignExtend { a: Box<BvTerm>, extra: u32 },
    RotateLeft { a: Box<BvTerm>, amount: u32 },
    RotateRight { a: Box<BvTerm>, amount: u32 },
    Repeat { a: Box<BvTerm>, times: u32 },
}

impl BvTerm {
    pub fn sort(&self) -> Option<SortBv> {
        match self {
            BvTerm::Const { sort, .. } => Some(*sort),
            BvTerm::Value { bits } => Some(SortBv { width: bits.len() as u32 }),
            BvTerm::Not(a) => a.sort(),
            BvTerm::And(a, _) | BvTerm::Or(a, _) | BvTerm::Xor(a, _)
            | BvTerm::Add(a, _) | BvTerm::Sub(a, _) | BvTerm::Mul(a, _)
            | BvTerm::Udiv(a, _) | BvTerm::Urem(a, _) | BvTerm::Shl(a, _) | BvTerm::Lshr(a, _) | BvTerm::Ashr(a, _)
            | BvTerm::Neg(a) => a.sort(),
            BvTerm::Concat(a, b) => {
                match (a.sort(), b.sort()) {
                    (Some(sa), Some(sb)) => Some(SortBv { width: sa.width + sb.width }),
                    _ => None,
                }
            },
            BvTerm::Extract { hi, lo, .. } => Some(SortBv { width: (hi - lo + 1) }),
            BvTerm::Eq(_, _) | BvTerm::Ult(_, _) | BvTerm::Ule(_, _) | BvTerm::Slt(_, _) | BvTerm::Sle(_, _) => None,
            BvTerm::Ite(_, a, _) => a.sort(),
            BvTerm::SignExtend { a, extra } => a.sort().map(|s| SortBv { width: s.width + *extra }),
            BvTerm::RotateLeft { a, .. } | BvTerm::RotateRight { a, .. } => a.sort(),
            BvTerm::Repeat { a, times } => a.sort().map(|s| SortBv { width: s.width * *times }),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct BoolLit(pub usize, pub bool); // var index, polarity

#[derive(Debug, Default, Clone)]
pub struct Cnf {
    pub num_vars: usize,
    pub clauses: Vec<Vec<BoolLit>>,
}

impl Cnf {
    pub fn new_var(&mut self) -> usize { self.num_vars += 1; self.num_vars - 1 }
    pub fn add_clause<I: IntoIterator<Item = BoolLit>>(&mut self, lits: I) {
        self.clauses.push(lits.into_iter().collect());
    }
}


