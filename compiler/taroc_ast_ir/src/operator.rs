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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
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

impl OperatorKind {
    pub fn from_binary(binary: BinaryOperator) -> OperatorKind {
        use OperatorKind::*;
        match binary {
            BinaryOperator::Add => Add,
            BinaryOperator::Sub => Sub,
            BinaryOperator::Mul => Mul,
            BinaryOperator::Div => Div,
            BinaryOperator::Rem => Rem,

            BinaryOperator::BoolAnd => BoolAnd,
            BinaryOperator::BoolOr => BoolOr,

            BinaryOperator::BitAnd => BitAnd,
            BinaryOperator::BitOr => BitOr,
            BinaryOperator::BitXor => BitXor,
            BinaryOperator::BitShl => BitShl,
            BinaryOperator::BitShr => BitShr,

            BinaryOperator::Eql => Eq,
            BinaryOperator::Lt => Lt,
            BinaryOperator::Gt => Gt,
            BinaryOperator::Leq => Leq,
            BinaryOperator::Geq => Geq,
            BinaryOperator::Neq => Neq,

            BinaryOperator::PatMatch => ExprMatch,

            BinaryOperator::PtrEq => todo!("ptr equality"),
        }
    }
}
