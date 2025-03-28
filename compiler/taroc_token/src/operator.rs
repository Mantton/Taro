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
    Reference(bool),
    // *
    Dereference,
    // -
    Negate,
    // ~
    BitwiseNot,
}

#[derive(Debug, Clone)]
pub enum OperatorKind {
    Add,
    Sub,
    Div,
    Mul,
    Rem,

    BitShl,
    BitShr,
    BitAnd,
    BitOr,
    BitXor,

    Neg,
    Not,
    BitwiseNot,
    ExprMatch,

    AddAssign,
    SubAssign,
    DivAssign,
    MulAssign,
    RemAssign,

    BitShlAssign,
    BitShrAssign,
    BitAndAssign,
    BitOrAssign,
    BitXorAssign,

    BoolAnd,
    BoolOr,

    Lt,
    Gt,
    Leq,
    Geq,
    Eq,
    Neq,

    Index,
}
