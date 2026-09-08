use crate::sema::models::{IntTy, Ty, TyKind, UIntTy};

// Unsigned unary negation is an existing arithmetic operation. Its operand
// must fit; lowering retains the operation and its runtime overflow policy.
pub(crate) fn integer_expression_literal_fits(value: i128, ty: Ty<'_>) -> bool {
    let value = if matches!(ty.kind(), TyKind::UInt(_)) {
        value.abs()
    } else {
        value
    };
    integer_literal_fits(value, ty)
}

pub(crate) fn integer_literal_fits<'ctx>(value: i128, ty: Ty<'ctx>) -> bool {
    match ty.kind() {
        TyKind::UInt(kind) => value >= 0 && value as u128 <= unsigned_max_u128(kind),
        TyKind::Int(kind) => {
            let max = signed_nonnegative_max_u128(kind) as i128;
            (-max - 1..=max).contains(&value)
        }
        _ => true,
    }
}

fn signed_nonnegative_max_u128(kind: IntTy) -> u128 {
    let bits = match kind {
        IntTy::ISize => isize::BITS,
        IntTy::I8 => 8,
        IntTy::I16 => 16,
        IntTy::I32 => 32,
        IntTy::I64 => 64,
    };
    (1u128 << (bits - 1)) - 1
}

fn unsigned_max_u128(kind: UIntTy) -> u128 {
    let bits = match kind {
        UIntTy::USize => usize::BITS,
        UIntTy::U8 => 8,
        UIntTy::U16 => 16,
        UIntTy::U32 => 32,
        UIntTy::U64 => 64,
    };

    if bits == 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}
