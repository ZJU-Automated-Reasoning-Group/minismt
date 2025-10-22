/// Boolean literal used in CNF clauses.
/// The first field is the zero-based variable index, the second is the polarity (true = positive).
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BoolLit(pub usize, pub bool);

/// A simple CNF container holding clauses and the number of allocated variables.
#[derive(Clone, Debug, Default)]
pub struct Cnf {
    pub clauses: Vec<Vec<BoolLit>>,
    pub num_vars: usize,
}

impl Cnf {
    pub fn new() -> Self { Self { clauses: Vec::new(), num_vars: 0 } }

    pub fn add_clause<I>(&mut self, clause: I)
    where
        I: IntoIterator<Item = BoolLit>,
    {
        self.clauses.push(clause.into_iter().collect());
    }

    pub fn new_var(&mut self) -> usize { let idx = self.num_vars; self.num_vars += 1; idx }
}
