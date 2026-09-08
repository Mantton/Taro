use crate::sema::models::{IntTy, Ty, TyKind, UIntTy};

pub(crate) fn integer_literal_fits<'ctx>(value: u64, ty: Ty<'ctx>, negative: bool) -> bool {
    let value = value as u128;
    match ty.kind() {
        TyKind::UInt(kind) => !negative && value <= unsigned_max_u128(kind),
        TyKind::Int(kind) => value <= signed_nonnegative_max_u128(kind) + u128::from(negative),
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
