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
    try_normalize_post_monomorphization(gcx, ty)
        .unwrap_or_else(|error| panic!("ICE: {}", error.format(gcx)))
}

/// An erased payload's unbound associated type is a source limitation, not a
/// missing concrete conformance or an inference-engine invariant failure.
#[derive(Clone, Copy, Debug)]
pub struct UnboundErasedProjection<'ctx> {
    pub projection: Ty<'ctx>,
    pub associated_type: DefinitionID,
}
impl<'ctx> UnboundErasedProjection<'ctx> {
    pub fn format(self, gcx: GlobalContext<'ctx>) -> String {
        format!(
            "cannot use unbound erased associated type '{}'; bind the associated type explicitly",
            self.projection.format(gcx)
        )
    }
}

/// Recover only the expected erased-projection boundary. Inference variables,
/// unsubstituted parameters and missing concrete witnesses remain compiler
/// invariant failures, rather than being accepted as arbitrary error storage.
pub fn try_normalize_post_monomorphization<'ctx>(
    gcx: GlobalContext<'ctx>,
    ty: Ty<'ctx>,
) -> Result<Ty<'ctx>, UnboundErasedProjection<'ctx>> {
    let mut folder = PostMonoNormalizeFolder {
        gcx,
        erased_projection: None,
    };
    let result = ty.fold_with(&mut folder);
    match folder.erased_projection {
        Some(error) => Err(error),
        None => Ok(result),
    }
}

struct PostMonoNormalizeFolder<'ctx> {
    gcx: GlobalContext<'ctx>,
    erased_projection: Option<UnboundErasedProjection<'ctx>>,
}

impl<'ctx> TypeFolder<'ctx> for PostMonoNormalizeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        if self.erased_projection.is_some() {
            return Ty::error(self.gcx);
        }
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

                        if self.erased_projection.is_some() {
                            return Ty::error(self.gcx);
                        }
                        let erased = folded_args
                            .first()
                            .and_then(|arg| arg.ty())
                            .is_some_and(|ty| matches!(ty.kind(), TyKind::BoxedExistential { .. }));
                        // Known existential bindings still normalize normally.
                        if let Some(resolved) = self.resolve_projection(def_id, folded_args) {
                            let result = resolved.fold_with(self);
                            if erased && super::erased_self::has_free_self(result) {
                                self.erased_projection = Some(UnboundErasedProjection {
                                    projection: ty,
                                    associated_type: def_id,
                                });
                                Ty::error(self.gcx)
                            } else {
                                result
                            }
                        } else if erased {
                            self.erased_projection = Some(UnboundErasedProjection {
                                projection: ty,
                                associated_type: def_id,
                            });
                            Ty::error(self.gcx)
                        } else {
                            // This is an ICE - should never happen in monomorphized code
                            panic!(
                                "ICE: failed to resolve projection {} in post-monomorphization context",
                                ty.format(self.gcx)
                            )
                        }
                    }
                    AliasKind::Opaque => {
                        let hidden = self.gcx.get_alias_type(def_id);
                        let instantiated = instantiate_ty_with_args(self.gcx, hidden, args);
                        instantiated.fold_with(self)
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
            let slice: Vec<_> = args.iter().take(interface_generic_count).cloned().collect();
            gcx.store.interners.intern_generic_args(slice)
        };

        let interface = InterfaceReference {
            id: interface_id,
            arguments: interface_args,
            bindings: &[],
        };

        // An existential has no concrete conformance witness of its own. Its
        // explicitly stored bindings nevertheless give projections a known ABI,
        // including bindings supplied by an inherited interface. Keep hidden
        // Self markers intact: substituting the container for them would turn
        // a payload-dependent result into unrelated container storage.
        if let TyKind::BoxedExistential { interfaces } = self_ty.kind() {
            use crate::sema::impl_engine::ref_ops::{
                InterfaceRefMatch, collect_interface_with_superfaces, interface_ref_matches,
            };
            let name = gcx.definition_ident(assoc_id).symbol;
            for root in interfaces {
                for candidate in collect_interface_with_superfaces(gcx, *root) {
                    if interface_ref_matches(interface, candidate, InterfaceRefMatch::Header)
                        && let Some(binding) = candidate.bindings.iter().find(|b| b.name == name)
                    {
                        return Some(binding.ty);
                    }
                }
            }
            return None;
        }

        // Resolve the witness and get the associated type
        let witness = resolve_conformance_witness(gcx, interface)?;
        let witness_ty = witness.type_witnesses.get(&assoc_id)?;

        // The selected witness is already in the projection receiver's
        // coordinates. Interface arguments are not a second impl substitution.
        Some(*witness_ty)
    }
}

#[cfg(test)]
mod erased_projection_tests {
    use super::*;
    #[test]
    fn missing_erased_associated_type_is_recoverable_and_explicit_binding_resolves() {
        crate::test_support::analyze_script(
            "interface P { type Output; func produce() -> Self::Output; }\nfunc main() {}",
            |package, gcx| {
                let id = package.root.declarations[0].id;
                let requirements = gcx.get_interface_requirements(id).unwrap();
                let associated = requirements.types[0].id;
                let arguments = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(gcx.types.existential_self)]);
                let make = |bindings| {
                    let interfaces =
                        gcx.store
                            .arenas
                            .global
                            .alloc_slice_copy(&[InterfaceReference {
                                id,
                                arguments,
                                bindings,
                            }]);
                    Ty::new(TyKind::BoxedExistential { interfaces }, gcx)
                };
                let project = |receiver| {
                    let args = gcx
                        .store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(receiver)]);
                    Ty::new(
                        TyKind::Alias {
                            kind: AliasKind::Projection,
                            def_id: associated,
                            args,
                        },
                        gcx,
                    )
                };
                let unbound = project(make(&[]));
                assert!(try_normalize_post_monomorphization(gcx, unbound).is_err());
                let bindings = gcx.store.arenas.global.alloc_slice_copy(&[
                    crate::sema::models::AssociatedTypeBinding {
                        name: gcx.definition_ident(associated).symbol,
                        ty: gcx.types.int32,
                    },
                ]);
                assert_eq!(
                    try_normalize_post_monomorphization(gcx, project(make(bindings))).unwrap(),
                    gcx.types.int32
                );
            },
        );
    }
}
