#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
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
    /// Pointer Equality
    /// `===`
    PtrEq,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnaryOperator {
    // !
    LogicalNot,
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

            BinaryOperator::PtrEq => {
                unreachable!("ICE: pointer equality should be custom handled")
            }
        }
    }

    pub fn from_unary(unary: UnaryOperator) -> OperatorKind {
        match unary {
            UnaryOperator::LogicalNot => OperatorKind::Not,
            UnaryOperator::Negate => OperatorKind::Neg,
            UnaryOperator::BitwiseNot => OperatorKind::BitwiseNot,
        }
    }
}

impl OperatorKind {
    /// Given a “plain” binary operator, returns the corresponding
    /// assignment operator kind (e.g. `+` → `AddAssign`), or `None`
    /// if there is no `op=` form.
    pub fn assign_from_binary(op: BinaryOperator) -> Option<OperatorKind> {
        match op {
            BinaryOperator::Add => Some(OperatorKind::AddAssign),
            BinaryOperator::Sub => Some(OperatorKind::SubAssign),
            BinaryOperator::Mul => Some(OperatorKind::MulAssign),
            BinaryOperator::Div => Some(OperatorKind::DivAssign),
            BinaryOperator::Rem => Some(OperatorKind::RemAssign),

            BinaryOperator::BitShl => Some(OperatorKind::BitShlAssign),
            BinaryOperator::BitShr => Some(OperatorKind::BitShrAssign),
            BinaryOperator::BitAnd => Some(OperatorKind::BitAndAssign),
            BinaryOperator::BitOr => Some(OperatorKind::BitOrAssign),
            BinaryOperator::BitXor => Some(OperatorKind::BitXorAssign),

            // all other binary ops (like `==`, `<`, `&&`, etc.) have no assignment form
            _ => None,
        }
    }
}
