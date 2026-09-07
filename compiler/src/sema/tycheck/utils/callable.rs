use crate::{
    compile::context::Gcx,
    hir::{DefinitionID, Mutability},
    sema::{
        impl_engine::ref_ops::{collect_interface_with_superfaces, interface_ref_with_self},
        models::{
            ClosureKind, InterfaceReference, Ty, TyKind, TyList, callable_inputs, callable_kind,
        },
    },
};

/// The callable view of an existential, including inherited callable interfaces.
/// All consumers use the same receiver choice and argument pack.
#[derive(Clone, Copy)]
pub struct ExistentialCallable<'ctx> {
    pub root_interface: DefinitionID,
    pub table_index: usize,
    pub interface: InterfaceReference<'ctx>,
    pub kind: ClosureKind,
}

impl<'ctx> ExistentialCallable<'ctx> {
    pub fn signature(self, gcx: Gcx<'ctx>) -> Option<(TyList<'ctx>, Ty<'ctx>)> {
        Some((
            callable_inputs(gcx, self.interface.arguments.get(1)?.ty()?),
            self.interface.arguments.get(2)?.ty()?,
        ))
    }

    pub fn receiver_mutability(self) -> Option<Mutability> {
        match self.kind {
            ClosureKind::Fn | ClosureKind::AsyncFn => Some(Mutability::Immutable),
            ClosureKind::FnMut | ClosureKind::AsyncFnMut => Some(Mutability::Mutable),
            ClosureKind::FnOnce | ClosureKind::AsyncFnOnce => None,
        }
    }

    pub fn is_async(self) -> bool {
        matches!(
            self.kind,
            ClosureKind::AsyncFn | ClosureKind::AsyncFnMut | ClosureKind::AsyncFnOnce
        )
    }

    pub fn method_id(self, gcx: Gcx<'ctx>) -> Option<DefinitionID> {
        let name = match self.receiver_mutability() {
            Some(Mutability::Immutable) => "call",
            Some(Mutability::Mutable) => "callMut",
            None => "callOnce",
        };
        gcx.get_interface_requirements(self.interface.id)?
            .methods
            .iter()
            .find(|method| gcx.symbol_eq(method.name, name))
            .map(|method| method.id)
    }
}

pub fn existential_callable<'ctx>(
    gcx: Gcx<'ctx>,
    ty: Ty<'ctx>,
) -> Option<ExistentialCallable<'ctx>> {
    select_existential_callable(gcx, ty).ok().flatten()
}

/// Ambiguous callable intersections require an explicit interface view.
pub fn select_existential_callable<'ctx>(
    gcx: Gcx<'ctx>,
    mut ty: Ty<'ctx>,
) -> Result<Option<ExistentialCallable<'ctx>>, ()> {
    while let TyKind::Reference(inner, _) = ty.kind() {
        ty = inner;
    }
    let TyKind::BoxedExistential { interfaces } = ty.kind() else {
        return Ok(None);
    };
    let mut best: Option<ExistentialCallable<'ctx>> = None;
    for (table_index, root) in interfaces.iter().enumerate() {
        let root = interface_ref_with_self(gcx, ty, *root);
        for interface in collect_interface_with_superfaces(gcx, root) {
            let Some(kind) = callable_kind(gcx, interface.id) else {
                continue;
            };
            let candidate = ExistentialCallable {
                root_interface: root.id,
                table_index,
                interface,
                kind,
            };
            if let Some(current) = best {
                // Different signatures cannot be disambiguated by an implicit call.
                if candidate.signature(gcx) != current.signature(gcx)
                    || candidate.is_async() != current.is_async()
                {
                    return Err(());
                }
                if current.kind as usize <= kind as usize {
                    continue;
                }
            }
            best = Some(candidate);
        }
    }
    Ok(best)
}
