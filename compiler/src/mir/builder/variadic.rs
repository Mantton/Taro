//! Compiler-owned variadic packs use ordinary owned storage and dependent views.
use super::MirBuilder;
use crate::sema::models::{Const, ConstKind, ConstValue, Ty, TyKind};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub(super) fn variadic_pack_ty(&self, element: Ty<'ctx>, count: usize) -> Ty<'ctx> {
        Ty::new(
            TyKind::Array {
                element,
                len: Const {
                    ty: self.gcx.types.uint,
                    kind: ConstKind::Value(ConstValue::Integer(count as i128)),
                },
            },
            self.gcx,
        )
    }
}
