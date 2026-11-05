//! Shared result shapes for ordinary and Result-returning initializers. The
//! public result and the private construction storage have distinct types.
use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, StdItem},
    sema::{
        models::{GenericArgument, Ty, TyKind},
        tycheck::utils::normalize_aliases,
    },
};

impl<'ctx> Gcx<'ctx> {
    pub fn result_parts(self, ty: Ty<'ctx>) -> Option<(Ty<'ctx>, Ty<'ctx>)> {
        let TyKind::Adt(definition, arguments) = normalize_aliases(self, ty).kind() else {
            return None;
        };
        if Some(definition.id) != self.std_item_def(StdItem::Result) {
            return None;
        }
        Some((arguments.first()?.ty()?, arguments.get(1)?.ty()?))
    }

    /// An initializer constructs its success value; failure contains no self.
    pub fn constructor_value(self, output: Ty<'ctx>) -> Ty<'ctx> {
        self.result_parts(output).map_or(output, |(value, _)| value)
    }

    pub fn constructor_result(self, output: Ty<'ctx>, success: Ty<'ctx>) -> Ty<'ctx> {
        let Some((_, error)) = self.result_parts(output) else {
            return success;
        };
        let TyKind::Adt(definition, _) = normalize_aliases(self, output).kind() else {
            unreachable!()
        };
        Ty::new(
            TyKind::Adt(
                definition,
                self.store.interners.intern_generic_args(vec![
                    GenericArgument::Type(success),
                    GenericArgument::Type(error),
                ]),
            ),
            self,
        )
    }

    pub fn initializer_target(self, initializer: DefinitionID) -> Ty<'ctx> {
        self.constructor_value(self.get_signature(initializer).output)
    }
}
