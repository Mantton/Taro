use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{
            AliasKind, Const, ConstKind, GenericArgument, GenericArguments, InterfaceReference, Ty,
            TyKind,
        },
        tycheck::{
            fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
            resolve_conformance_witness,
            utils::instantiate::instantiate_ty_with_args,
        },
    },
};

/// Normalize types after monomorphization (no InferCtx, no ParamEnv).
///
/// This is analogous to rustc's `normalize_erasing_regions` - it assumes:
/// 1. No inference variables remain
/// 2. All type parameters have been substituted
/// 3. All projections can be resolved to concrete types
///
/// # Panics
///
/// This function will panic (ICE) if:
/// - Inference variables are encountered (should be resolved during typeck)
/// - Type parameters are encountered (should be substituted during monomorphization)
/// - Projections cannot be resolved (indicates a missing conformance)
pub fn normalize_post_monomorphization<'ctx>(gcx: GlobalContext<'ctx>, ty: Ty<'ctx>) -> Ty<'ctx> {
    let mut folder = PostMonoNormalizeFolder { gcx };
    ty.fold_with(&mut folder)
}

struct PostMonoNormalizeFolder<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for PostMonoNormalizeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            // Handle all alias kinds
            TyKind::Alias { kind, def_id, args } => {
                match kind {
                    AliasKind::Weak | AliasKind::Inherent => {
                        // Resolve weak/inherent aliases
                        let base = self.gcx.get_alias_type(def_id);
                        let instantiated = instantiate_ty_with_args(self.gcx, base, args);
                        // Recursively normalize
                        instantiated.fold_with(self)
                    }
                    AliasKind::Projection => {
                        // First, fold the args to resolve any nested aliases/projections.
                        // For nested projections like `Range[int32].Iterator.Element`,
                        // the Self arg may itself be an alias (e.g. `Range[int32].Iterator`).
                        // We need to resolve it to its concrete type first.
                        let folded_args: Vec<_> = args
                            .iter()
                            .map(|arg| match arg {
                                GenericArgument::Type(ty) => {
                                    GenericArgument::Type(ty.fold_with(self))
                                }
                                GenericArgument::Const(c) => GenericArgument::Const(*c),
                            })
                            .collect();
                        let folded_args = self.gcx.store.interners.intern_generic_args(folded_args);

                        // Resolve projection: T.Item where T is concrete
                        if let Some(resolved) = self.resolve_projection(def_id, folded_args) {
                            // Recursively normalize the result
                            resolved.fold_with(self)
                        } else {
                            // This is an ICE - should never happen in monomorphized code
                            panic!(
                                "ICE: failed to resolve projection {} in post-monomorphization context",
                                ty.format(self.gcx)
                            )
                        }
                    }
                }
            }
            // Panic on inference variables - these should be gone
            TyKind::Infer(_) => {
                panic!(
                    "ICE: inference variable in post-monomorphization normalization: {}",
                    ty.format(self.gcx)
                )
            }
            // Panic on type parameters - these should be substituted
            // EXCEPTION: Self parameters in interface methods are valid for witness tables
            TyKind::Parameter(_) => {
                // Allow Self to pass through for interface method signatures
                if ty == self.gcx.types.self_type_parameter {
                    return ty;
                }
                panic!(
                    "ICE: type parameter in post-monomorphization normalization: {}",
                    ty.format(self.gcx)
                )
            }
            // Recurse into composite types
            _ => ty.super_fold_with(self),
        }
    }

    fn fold_const(&mut self, c: Const<'ctx>) -> Const<'ctx> {
        match c.kind {
            ConstKind::Param(_) | ConstKind::Infer(_) => {
                panic!(
                    "ICE: const parameter in post-monomorphization normalization: {}",
                    c.ty.format(self.gcx)
                )
            }
            _ => Const {
                ty: c.ty.fold_with(self),
                kind: c.kind,
            },
        }
    }
}

impl<'ctx> PostMonoNormalizeFolder<'ctx> {
    fn resolve_projection(
        &self,
        assoc_id: DefinitionID,
        args: GenericArguments<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let gcx = self.gcx;
        let interface_id = gcx.definition_parent(assoc_id)?;
        let self_arg = args.get(0)?;
        let GenericArgument::Type(self_ty) = self_arg else {
            return None;
        };

        // Self must be concrete - no parameters, no inference vars
        // EXCEPTION: Allow Self parameter for interface methods (e.g., Self.Item in interface definitions)
        if let TyKind::Parameter(param) = self_ty.kind() {
            if gcx.symbol_eq(param.name, "Self") {
                // Return the projection unchanged - it's valid in interface method context
                return None;
            } else {
                panic!(
                    "ICE: projection with type parameter in post-mono context: {}",
                    self_ty.format(gcx)
                );
            }
        }

        if self_ty.is_infer() {
            panic!(
                "ICE: projection with inference variable in post-mono context: {}",
                self_ty.format(gcx)
            );
        }

        // Build the full interface arguments [Self, ...interface generics...].
        let interface_generic_count = gcx.generics_of(interface_id).total_count();
        let interface_args = if interface_generic_count == 0 {
            gcx.store.interners.intern_generic_args(Vec::new())
        } else {
            let slice: Vec<_> = args
                .iter()
                .take(interface_generic_count)
                .cloned()
                .collect();
            gcx.store.interners.intern_generic_args(slice)
        };

        let interface = InterfaceReference {
            id: interface_id,
            arguments: interface_args,
            bindings: &[],
        };

        // Resolve the witness and get the associated type
        let witness = resolve_conformance_witness(gcx, interface)?;
        let witness_ty = witness.type_witnesses.get(&assoc_id)?;

        // The witness type may contain impl-block generic parameters
        // (e.g., FilterIterator[Item, Inner, F] from a generic impl block).
        // We need to deduce the concrete impl args from the concrete Self type
        // and use those for substitution, not just the projection args.
        if let Some(extension_id) = witness.extension_id {
            if let Some(deduced_args) =
                crate::sema::impl_engine::deduce_impl_subst(gcx, extension_id, *self_ty, &[])
            {
                return Some(instantiate_ty_with_args(gcx, *witness_ty, deduced_args));
            }
        }

        // Fallback: instantiate with the projection's args (works for simple cases)
        Some(instantiate_ty_with_args(gcx, *witness_ty, args))
    }

}
