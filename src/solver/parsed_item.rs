use super::sexpr::SExpr;
use super::bv::{BvTerm, SortBv};
use super::cnf::BoolLit;
// use super::aig_bitblaster::AigNode;
use super::symbol_table::SymbolNode;

/// A parsed item in the parsing stack, similar to Bitwuzla's ParsedItem
#[derive(Debug, Clone)]
pub struct ParsedItem {
    /// The kind of the item (command, term, etc.)
    pub kind: ParsedItemKind,
    /// The associated data
    pub data: ParsedItemData,
    /// Line number in the input
    pub line: usize,
    /// Column number in the input
    pub column: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ParsedItemKind {
    Command,
    Term,
    Sort,
    Symbol,
    LetBinding,
    LetBody,
    QuantifierBinding,
    QuantifierBody,
    FunctionDefinition,
    Assertion,
    LeftParen,
    RightParen,
}

#[derive(Debug, Clone)]
pub enum ParsedItemData {
    Command(super::smtlib::Command),
    Term(BvTerm),
    Sort(SortBv),
    Symbol(String),
    SymbolNode(Box<SymbolNode>),
    BoolLit(BoolLit),
    // AigNode(AigNode),
    SExpr(SExpr),
    UInt(u64),
    String(String),
    Empty,
}

impl ParsedItem {
    pub fn new(kind: ParsedItemKind, data: ParsedItemData, line: usize, column: usize) -> Self {
        Self {
            kind,
            data,
            line,
            column,
        }
    }
    
    pub fn command(cmd: super::smtlib::Command, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Command, ParsedItemData::Command(cmd), line, column)
    }
    
    pub fn term(term: BvTerm, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Term, ParsedItemData::Term(term), line, column)
    }
    
    pub fn sort(sort: SortBv, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Sort, ParsedItemData::Sort(sort), line, column)
    }
    
    pub fn symbol(name: String, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Symbol, ParsedItemData::Symbol(name), line, column)
    }
    
    pub fn symbol_node(node: Box<SymbolNode>, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Symbol, ParsedItemData::SymbolNode(node), line, column)
    }
    
    pub fn bool_lit(lit: BoolLit, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Term, ParsedItemData::BoolLit(lit), line, column)
    }
    
    // pub fn aig_node(node: AigNode, line: usize, column: usize) -> Self {
    //     Self::new(ParsedItemKind::Term, ParsedItemData::AigNode(node), line, column)
    // }
    
    pub fn sexpr(expr: SExpr, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Term, ParsedItemData::SExpr(expr), line, column)
    }
    
    pub fn uint(value: u64, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Term, ParsedItemData::UInt(value), line, column)
    }
    
    pub fn string(value: String, line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::Term, ParsedItemData::String(value), line, column)
    }
    
    pub fn left_paren(line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::LeftParen, ParsedItemData::Empty, line, column)
    }
    
    pub fn right_paren(line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::RightParen, ParsedItemData::Empty, line, column)
    }
    
    pub fn let_binding(line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::LetBinding, ParsedItemData::Empty, line, column)
    }
    
    pub fn let_body(line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::LetBody, ParsedItemData::Empty, line, column)
    }
    
    pub fn quantifier_binding(line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::QuantifierBinding, ParsedItemData::Empty, line, column)
    }
    
    pub fn quantifier_body(line: usize, column: usize) -> Self {
        Self::new(ParsedItemKind::QuantifierBody, ParsedItemData::Empty, line, column)
    }
    
    /// Check if this is a term argument
    pub fn is_term_arg(&self) -> bool {
        matches!(self.kind, ParsedItemKind::Term)
    }
    
    /// Check if this is a symbol argument
    pub fn is_symbol_arg(&self) -> bool {
        matches!(self.kind, ParsedItemKind::Symbol)
    }
    
    /// Check if this is a sort argument
    pub fn is_sort_arg(&self) -> bool {
        matches!(self.kind, ParsedItemKind::Sort)
    }
    
    /// Check if this is a left parenthesis
    pub fn is_left_paren(&self) -> bool {
        matches!(self.kind, ParsedItemKind::LeftParen)
    }
    
    /// Check if this is a right parenthesis
    pub fn is_right_paren(&self) -> bool {
        matches!(self.kind, ParsedItemKind::RightParen)
    }
    
    /// Check if this is a let binding
    pub fn is_let_binding(&self) -> bool {
        matches!(self.kind, ParsedItemKind::LetBinding)
    }
    
    /// Check if this is a let body
    pub fn is_let_body(&self) -> bool {
        matches!(self.kind, ParsedItemKind::LetBody)
    }
    
    /// Check if this is a quantifier binding
    pub fn is_quantifier_binding(&self) -> bool {
        matches!(self.kind, ParsedItemKind::QuantifierBinding)
    }
    
    /// Check if this is a quantifier body
    pub fn is_quantifier_body(&self) -> bool {
        matches!(self.kind, ParsedItemKind::QuantifierBody)
    }
}

/// A parsing stack for managing parsed items
pub struct ParsingStack {
    items: Vec<ParsedItem>,
    control_stack: Vec<usize>,
}

impl ParsingStack {
    pub fn new() -> Self {
        Self {
            items: Vec::new(),
            control_stack: Vec::new(),
        }
    }
    
    /// Push an item onto the stack
    pub fn push(&mut self, item: ParsedItem) {
        self.items.push(item);
    }
    
    /// Pop an item from the stack
    pub fn pop(&mut self) -> Option<ParsedItem> {
        self.items.pop()
    }
    
    /// Peek at the top item without removing it
    pub fn peek(&self) -> Option<&ParsedItem> {
        self.items.last()
    }
    
    /// Get the number of items on the stack
    pub fn len(&self) -> usize {
        self.items.len()
    }
    
    /// Check if the stack is empty
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
    
    /// Get the index of the last open parenthesis
    pub fn last_open_paren(&self) -> Option<usize> {
        self.control_stack.last().copied()
    }
    
    /// Push a control point (e.g., open parenthesis)
    pub fn push_control(&mut self, index: usize) {
        self.control_stack.push(index);
    }
    
    /// Pop a control point
    pub fn pop_control(&mut self) -> Option<usize> {
        self.control_stack.pop()
    }
    
    /// Get the number of arguments for the current open item
    pub fn num_args(&self) -> usize {
        if let Some(open_idx) = self.last_open_paren() {
            self.items.len() - open_idx - 1
        } else {
            0
        }
    }
    
    /// Check if we're expecting a right parenthesis
    pub fn expecting_rparen(&self) -> bool {
        !self.control_stack.is_empty()
    }
    
    /// Clear the stack
    pub fn clear(&mut self) {
        self.items.clear();
        self.control_stack.clear();
    }
    
    /// Get all items as a slice
    pub fn items(&self) -> &[ParsedItem] {
        &self.items
    }
    
    /// Get items starting from a specific index
    pub fn items_from(&self, start: usize) -> &[ParsedItem] {
        if start < self.items.len() {
            &self.items[start..]
        } else {
            &[]
        }
    }
}

impl Default for ParsingStack {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_parsing_stack_basic() {
        let mut stack = ParsingStack::new();
        
        let item = ParsedItem::symbol("x".to_string(), 1, 1);
        stack.push(item);
        
        assert_eq!(stack.len(), 1);
        assert!(!stack.is_empty());
        
        let popped = stack.pop().unwrap();
        assert_eq!(popped.kind, ParsedItemKind::Symbol);
    }
    
    #[test]
    fn test_control_stack() {
        let mut stack = ParsingStack::new();
        
        let item1 = ParsedItem::left_paren(1, 1);
        let item2 = ParsedItem::symbol("x".to_string(), 1, 2);
        let item3 = ParsedItem::symbol("y".to_string(), 1, 4);
        
        stack.push(item1);
        stack.push_control(0);
        stack.push(item2);
        stack.push(item3);
        
        assert_eq!(stack.num_args(), 2);
        assert!(stack.expecting_rparen());
        
        let item4 = ParsedItem::right_paren(1, 5);
        stack.push(item4);
        stack.pop_control();
        
        assert!(!stack.expecting_rparen());
    }
}
