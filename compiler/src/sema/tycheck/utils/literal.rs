use crate::sema::models::{IntTy, Ty, TyKind, UIntTy};

// Unsigned unary negation is an existing arithmetic operation. Its operand
// must fit; lowering retains the operation and its runtime overflow policy.
pub(crate) fn integer_expression_literal_fits(value: i128, ty: Ty<'_>, pointer_bits: u32) -> bool {
    let value = if matches!(ty.kind(), TyKind::UInt(_)) {
        value.abs()
    } else {
        value
    };
    integer_literal_fits(value, ty, pointer_bits)
}

pub(crate) fn integer_literal_fits(value: i128, ty: Ty<'_>, pointer_bits: u32) -> bool {
    match ty.kind() {
        TyKind::UInt(kind) => value >= 0 && value as u128 <= unsigned_max_u128(kind, pointer_bits),
        TyKind::Int(kind) => {
            let max = signed_nonnegative_max_u128(kind, pointer_bits) as i128;
            (-max - 1..=max).contains(&value)
        }
        _ => true,
    }
}

fn signed_nonnegative_max_u128(kind: IntTy, pointer_bits: u32) -> u128 {
    let bits = match kind {
        IntTy::ISize => pointer_bits,
        IntTy::I8 => 8,
        IntTy::I16 => 16,
        IntTy::I32 => 32,
        IntTy::I64 => 64,
    };
    (1u128 << (bits - 1)) - 1
}

fn unsigned_max_u128(kind: UIntTy, pointer_bits: u32) -> u128 {
    let bits = match kind {
        UIntTy::USize => pointer_bits,
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
