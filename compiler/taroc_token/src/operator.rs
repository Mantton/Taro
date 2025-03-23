#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinaryOperator {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `%`
    Rem,
    /// `&&`
    BoolAnd,
    /// `||`
    BoolOr,
    /// `&`
    BitAnd,
    /// `|`
    BitOr,
    /// `^`
    BitXor,
    /// `<<`
    BitShl,
    /// `>>`
    BitShr,
    /// `==`
    Eql,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `<=`
    Leq,
    /// `>=`
    Geq,
    /// `!=`
    Neq,
    /// `~=`
    PatMatch,
    /// Pointer Equality
    /// `===`
    PtrEq,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnaryOperator {
    // !
    LogicalNot,
    // &
    Reference,
    // *
    Dereference,
    // -
    Negate,
    // ~
    BitwiseNot,
}
