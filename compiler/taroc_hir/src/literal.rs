use taroc_span::Symbol;

#[derive(Debug, Clone)]
pub enum Literal {
    Bool(bool),
    Rune(char),
    String(Symbol),
    Integer(u64),
    Float(f64),
    Nil,
    Void,
}
