use crate::sema::tycheck::{
    infer::InferCtx,
    resolve_conformance_witness_with_param_env,
    utils::{instantiate::instantiate_ty_with_args, param_env::ParamEnv},
};
use crate::{
    compile::context::GlobalContext,
    hir::DefinitionID,
    sema::{
        models::{
            AliasKind, Const, GenericArgument, GenericArguments, InterfaceReference, Ty, TyKind,
        },
        tycheck::fold::{TypeFoldable, TypeFolder, TypeSuperFoldable},
    },
};
use rustc_hash::FxHashSet;
use std::cell::OnceCell;
use std::rc::Rc;

/// Normalize a type using the given inference context and parameter environment.
/// The inference context is used to resolve inference variables before normalizing.
pub fn normalize_ty<'ctx>(icx: Rc<InferCtx<'ctx>>, ty: Ty<'ctx>, env: &ParamEnv<'ctx>) -> Ty<'ctx> {
    let mut in_progress = FxHashSet::default();
    in_progress.reserve(env.normalization_set_capacity_hint());
    let mut folder = NormalizeFolder {
        icx,
        env,
        in_progress,
        selection_param_env: OnceCell::new(),
    };
    ty.fold_with(&mut folder)
}

/// Shallow normalization that only resolves type aliases (weak/inherent).
/// Does NOT resolve projections or inference variables.
/// Used for contexts without InferCtx like codegen or canonical constraint building.
pub fn normalize_aliases<'ctx, T: TypeFoldable<'ctx>>(gcx: GlobalContext<'ctx>, value: T) -> T {
    let mut folder = ShallowNormalizeFolder { gcx };
    value.fold_with(&mut folder)
}

struct ShallowNormalizeFolder<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> TypeFolder<'ctx> for ShallowNormalizeFolder<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.gcx
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        match ty.kind() {
            TyKind::Alias { kind, def_id, args }
                if matches!(kind, AliasKind::Weak | AliasKind::Inherent) =>
            {
                let base = self.gcx.get_alias_type(def_id);
                let instantiated = instantiate_ty_with_args(self.gcx, base, args);
                return instantiated.fold_with(self);
            }
            _ => ty.super_fold_with(self),
        }
    }
}

struct NormalizeFolder<'a, 'ctx> {
    icx: Rc<InferCtx<'ctx>>,
    env: &'a ParamEnv<'ctx>,
    in_progress: FxHashSet<Ty<'ctx>>,
    selection_param_env: OnceCell<&'ctx [crate::sema::models::Constraint<'ctx>]>,
}

impl<'a, 'ctx> NormalizeFolder<'a, 'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.icx.gcx
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn projection_bounds_match_the_complete_interface_header() {
        crate::test_support::analyze_script(
            "interface Choice[T] { type Output; }\nstruct Value {}\nconform Value to Choice[int32] { type Output = bool; }\nconform Value to Choice[bool] { type Output = int32; }\nfunc main() {}",
            |package, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| declaration.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let choice = find("Choice");
                let value = gcx.get_type(find("Value"));
                let output = &gcx.get_interface_requirements(choice).unwrap().types[0];
                let arguments = |argument| {
                    gcx.store.interners.intern_generic_args(vec![
                        GenericArgument::Type(value),
                        GenericArgument::Type(argument),
                    ])
                };
                let binding = gcx.store.arenas.global.alloc_slice_copy(&[
                    crate::sema::models::AssociatedTypeBinding {
                        name: output.name,
                        ty: gcx.types.bool,
                    },
                ]);
                let env = ParamEnv::new(vec![crate::sema::models::Constraint::Bound {
                    ty: value,
                    interface: InterfaceReference {
                        id: choice,
                        arguments: arguments(gcx.types.int32),
                        bindings: binding,
                    },
                }]);
                let projection = Ty::new(
                    TyKind::Alias {
                        kind: AliasKind::Projection,
                        def_id: output.id,
                        args: arguments(gcx.types.bool),
                    },
                    gcx,
                );
                assert_eq!(
                    normalize_ty(Rc::new(InferCtx::new(gcx)), projection, &env),
                    gcx.types.int32
                );
            },
        );
    }

    #[test]
    fn g30_witness_selection_does_not_import_caller_inference_variables() {
        crate::test_support::analyze_script(
            "interface Input { type Item; }\ninterface Output { type Item; }\nstruct Value {}\nconform Value to Input { type Item = int32; }\nstruct Wrapper[T] {}\nconform[T: Input[Item = U], U] Wrapper[T] to Output { type Item = U; }\nfunc main() {}",
            |package, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| declaration.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let input = find("Input");
                let output = find("Output");
                let span = gcx.definition_ident(input).span;
                let icx = Rc::new(InferCtx::new(gcx));
                let mut unresolved = gcx.types.int32;
                for _ in 0..8 {
                    unresolved = icx.next_ty_var(span);
                }
                let args = |ty| {
                    gcx.store
                        .interners
                        .intern_generic_args(vec![GenericArgument::Type(ty)])
                };
                let env = ParamEnv::new(vec![crate::sema::models::Constraint::Bound {
                    ty: unresolved,
                    interface: InterfaceReference {
                        id: input,
                        arguments: args(unresolved),
                        bindings: &[],
                    },
                }]);
                let wrapper = instantiate_ty_with_args(
                    gcx,
                    gcx.get_type(find("Wrapper")),
                    args(gcx.get_type(find("Value"))),
                );
                let projection = Ty::new(
                    TyKind::Alias {
                        kind: AliasKind::Projection,
                        def_id: gcx.get_interface_requirements(output).unwrap().types[0].id,
                        args: args(wrapper),
                    },
                    gcx,
                );
                assert_eq!(normalize_ty(icx.clone(), projection, &env), gcx.types.int32);
                super::super::unify::TypeUnifier::new(icx.clone())
                    .unify(unresolved, gcx.get_type(find("Value")))
                    .unwrap();
                assert_eq!(
                    normalize_ty(icx, projection, &env),
                    gcx.types.int32,
                    "a resolved pending requirement must not become an independent caller proof"
                );
            },
        );
    }

    #[test]
    fn generic_associated_receiver_preserves_declared_element_equality() {
        crate::test_support::analyze_script(
            "interface Yield { type Item; func value() -> Self::Item; }\ninterface Source { type Item; type Cursor: Yield[Item = Self::Item]; func cursor() -> Self::Cursor; }\nfunc read[C: Source[Item = int32]](_ source: &C) -> int32 { source.cursor().value() }\nfunc main() {}",
            |_, _| {},
        );
    }

    #[test]
    fn nested_associated_receiver_normalizes_in_one_pass() {
        crate::test_support::analyze_script(
            "interface Leaf { type Item; }\ninterface Root { type Child: Leaf; }\ninterface Inspect: Root { func get() -> Self::Child::Item; }\nstruct LeafValue { value: int32 }\nstruct RootValue { value: LeafValue }\nconform LeafValue to Leaf { type Item = int32; }\nconform RootValue to Root { type Child = LeafValue; }\nfunc main() {}",
            |package, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|decl| decl.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let inspect = find("Inspect");
                let concrete = gcx.get_type(find("RootValue"));
                let method = gcx.get_interface_requirements(inspect).unwrap().methods[0].id;
                let output = gcx.get_signature(method).output;
                let args = gcx
                    .store
                    .interners
                    .intern_generic_args(vec![GenericArgument::Type(concrete)]);
                let nested = instantiate_ty_with_args(gcx, output, args);
                let normalized =
                    normalize_ty(Rc::new(InferCtx::new(gcx)), nested, &ParamEnv::default());
                assert_eq!(normalized, gcx.types.int32, "{}", normalized.format(gcx));
            },
        );
    }

    #[test]
    fn superinterface_associated_type_binding_normalizes_projection() {
        let diagnostics = crate::test_support::analyze_script_diagnostics(
            r#"
interface Combine[Rhs = Self] {
    type Output = Self
    func combine(_ rhs: Rhs) -> Self::Output
}
interface Closed: Combine[Self, Output = Self] {}
func twice[T: Closed](_ x: T) -> T {
    x.combine(x)
}
func main() {}
"#,
        );
        assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    }
}

impl<'a, 'ctx> TypeFolder<'ctx> for NormalizeFolder<'a, 'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx> {
        self.icx.gcx
    }

    fn fold_const(&mut self, value: Const<'ctx>) -> Const<'ctx> {
        let value = self.icx.shallow_resolve_const(value);
        Const {
            ty: value.ty.fold_with(self),
            ..value
        }
    }

    fn fold_ty(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        // Resolve one level of inference first; recursive folding handles nested structure.
        let ty = self.icx.shallow_resolve(ty);
        let has_type_equalities = self.env.has_type_equalities();

        match ty.kind() {
            // These forms are terminal under normalization.
            TyKind::Bool
            | TyKind::Rune
            | TyKind::String
            | TyKind::Int(_)
            | TyKind::UInt(_)
            | TyKind::Float(_)
            | TyKind::Infer(_)
            | TyKind::Opaque(_)
            | TyKind::Error
            | TyKind::Never => return ty,
            // Non-generic concrete ADTs cannot change under normalization.
            TyKind::Adt(_, args) if args.is_empty() => return ty,
            // Unit tuple cannot change under normalization.
            TyKind::Tuple(items) if items.is_empty() => return ty,
            // Parameters only normalize via explicit equality constraints.
            TyKind::Parameter(_) if !has_type_equalities => return ty,
            _ => {}
        }

        // Without equality constraints, types that contain no alias/inference content
        // cannot be changed by normalization.
        if !has_type_equalities && !ty.contains_inference() {
            return ty;
        }

        // Break normalization cycles such as `T.Item == U` and `U == T.Item`.
        if !self.in_progress.insert(ty) {
            return ty;
        }

        let normalized = match ty.kind() {
            TyKind::Alias {
                kind: AliasKind::Projection,
                def_id,
                args,
            } => {
                // Priority 1: Check ParamEnv for explicit type equalities.
                // This handles parametric normalization like `T: Container[Item=int]`
                // where we want `T.Item` to normalize to `int`.

                if has_type_equalities {
                    let equiv_types = self.env.equivalent_types(ty);

                    // Prefer non-alias equalities first (including parameters).
                    // Cycle prevention is handled by `in_progress`.
                    if let Some(&resolved) = equiv_types.iter().find(|&&t| {
                        t != ty && !matches!(t.kind(), TyKind::Alias { .. } | TyKind::Infer(_))
                    }) {
                        resolved.fold_with(self)
                    } else if let Some(resolved) = self.resolve_projection(def_id, args) {
                        resolved.fold_with(self)
                    } else {
                        ty.super_fold_with(self)
                    }
                } else if let Some(resolved) = self.resolve_projection(def_id, args) {
                    resolved.fold_with(self)
                } else {
                    ty.super_fold_with(self)
                }
            }
            TyKind::Alias {
                kind: AliasKind::Weak | AliasKind::Inherent,
                def_id,
                args,
            } => {
                let base = self.gcx().get_alias_type(def_id);
                let instantiated = instantiate_ty_with_args(self.gcx(), base, args);
                instantiated.fold_with(self)
            }
            // Handle type parameters with equality constraints
            // e.g., for `where T == string`, normalize T to string
            TyKind::Parameter(_) => {
                if !has_type_equalities {
                    ty
                } else {
                    let equiv_types = self.env.equivalent_types(ty);
                    // Find a concrete type equivalent to this parameter
                    // Prefer non-parameter, non-alias types
                    if let Some(&resolved) = equiv_types.iter().find(|&&t| {
                        !matches!(
                            t.kind(),
                            TyKind::Parameter(_) | TyKind::Alias { .. } | TyKind::Infer(_)
                        )
                    }) {
                        resolved.fold_with(self)
                    } else if let Some(&resolved) = equiv_types.iter().find(|&&t| {
                        if t == ty || matches!(t.kind(), TyKind::Parameter(_) | TyKind::Infer(_)) {
                            return false;
                        }
                        // Avoid selecting a projection currently being normalized.
                        if matches!(
                            t.kind(),
                            TyKind::Alias {
                                kind: AliasKind::Projection,
                                ..
                            }
                        ) && self.in_progress.contains(&t)
                        {
                            return false;
                        }
                        true
                    }) {
                        resolved.fold_with(self)
                    } else {
                        ty
                    }
                }
            }
            _ => ty.super_fold_with(self),
        };

        self.in_progress.remove(&ty);
        normalized
    }
}

impl<'a, 'ctx> NormalizeFolder<'a, 'ctx> {
    fn conformance_witness(
        &self,
        interface: InterfaceReference<'ctx>,
    ) -> Option<crate::sema::models::ConformanceWitness<'ctx>> {
        // Conditional implementations may rely on bounds from the generic
        // definition currently being checked. Materialize that environment
        // lazily so types without projections pay no allocation cost and all
        // projections in one normalization pass share the same baseline slice.
        let full_param_env = *self.selection_param_env.get_or_init(|| {
            use crate::sema::{models::Constraint, tycheck::utils::unresolved::*};
            // Witness selection owns a separate inference context. Pending
            // call requirements are not caller proofs and must never enter
            // that context's variable table, even if they resolve later.
            let constraints: Vec<_> = self
                .env
                .witness_constraints()
                .into_iter()
                .filter(|constraint| match *constraint {
                    Constraint::TypeEquality(left, right) => {
                        !ty_contains_unresolved_inference(left)
                            && !ty_contains_unresolved_inference(right)
                    }
                    Constraint::Bound { ty, interface } => {
                        !ty_contains_unresolved_inference(ty)
                            && !interface_ref_contains_unresolved_inference(interface)
                    }
                })
                .collect();
            self.gcx()
                .store
                .arenas
                .global
                .alloc_slice_clone(&constraints)
        });
        let self_ty = interface.self_ty()?;
        let is_goal_bound = |constraint: &crate::sema::models::Constraint<'ctx>| {
            matches!(
                constraint,
                crate::sema::models::Constraint::Bound { ty, interface: bound }
                    if *ty == self_ty
                        && bound.id == interface.id
                        && bound.arguments == interface.arguments
            )
        };

        // A declaration may also assume the goal itself. Selection needs a
        // concrete associated type witness here. Any explicit type binding
        // has already been considered by the projection lookup.
        let param_env = if !full_param_env.iter().any(is_goal_bound) {
            full_param_env
        } else {
            let filtered: Vec<_> = full_param_env
                .iter()
                .filter(|constraint| !is_goal_bound(constraint))
                .copied()
                .collect();
            self.gcx().store.arenas.global.alloc_slice_clone(&filtered)
        };
        resolve_conformance_witness_with_param_env(self.gcx(), interface, param_env)
    }

    fn resolve_projection(
        &mut self,
        assoc_id: DefinitionID,
        args: GenericArguments<'ctx>,
    ) -> Option<Ty<'ctx>> {
        // Resolve an associated receiver before selecting its conformance.
        // Otherwise Root.Child.Item selects Leaf on the unresolved Root.Child,
        // then folds Child but never retries Item, exposing a half-normalized
        // type to one-pass consumers such as MIR assignment validation. Reuse
        // this folder so recursive projection arguments share its cycle guard.
        let args = args.fold_with(self);
        let gcx = self.gcx();
        let interface_id = gcx.definition_parent(assoc_id)?;
        let self_arg = args.get(0)?;
        let GenericArgument::Type(self_ty) = self_arg else {
            return None;
        };

        // Recursively normalize substituted Self type
        let self_ty = self.icx.resolve_vars_if_possible(*self_ty);

        // If Self is still an inference variable, cannot resolve yet
        if self_ty.is_infer() {
            return None;
        }

        // Existential types with associated type bindings: resolve projections directly.
        // For `any Producer[Output = int].Output`, extract `int` from the binding.
        // This is the most direct resolution path since bindings are explicit.
        if let TyKind::BoxedExistential { interfaces } = self_ty.kind() {
            let assoc_name = gcx.definition_ident(assoc_id).symbol;

            for iface in interfaces.iter() {
                // Match interface by ID (direct match or parent of associated type)
                if iface.id == interface_id || gcx.definition_parent(assoc_id) == Some(iface.id) {
                    for binding in iface.bindings {
                        if binding.name == assoc_name {
                            return Some(binding.ty);
                        }
                    }
                }
            }
        }

        // A type can implement one interface for several argument lists.
        // Match the complete header (including superinterfaces implied by a
        // declared bound), resolving caller variables first, rather than
        // taking the first bound for Self and the interface name alone.
        let matching_bounds: Vec<_> = self
            .env
            .bounds_for_type(gcx, self_ty, |bound_ty| {
                self.icx.resolve_vars_if_possible(bound_ty) == self_ty
            })
            .into_iter()
            .flat_map(|bound| {
                crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(gcx, bound)
            })
            .filter(|bound| {
                bound.id == interface_id
                    && bound.arguments.len() == args.len()
                    && self
                        .icx
                        .resolve_args_if_possible(bound.arguments)
                        .iter()
                        .zip(args.iter())
                        .all(|(left, right)| match (*left, *right) {
                            (GenericArgument::Type(a), GenericArgument::Type(b)) => {
                                a == b || self.env.equivalent_types(a).contains(&b)
                            }
                            (a, b) => a == b,
                        })
            })
            .map(|bound| InterfaceReference {
                arguments: args,
                ..bound
            })
            .collect();
        if !matching_bounds.is_empty() {
            // An associated type binding on a generic bound (or one of its
            // superinterfaces) is already the canonical answer. Exact
            // structural lookup is intentional here: an impl-local receiver
            // that only later resolves to this type must fall through to its
            // concrete witness so associated variables such as `Inner` can be
            // inferred.
            let assoc_name = gcx.definition_ident(assoc_id).symbol;
            for bound_iface in &matching_bounds {
                if let Some(binding) = bound_iface
                    .bindings
                    .iter()
                    .find(|binding| binding.name == assoc_name)
                {
                    return Some(self.icx.resolve_vars_if_possible(binding.ty));
                }
            }
            // Found matching bound - look up type witness from conformance.
            let witness = self.conformance_witness(matching_bounds[0])?;
            return witness.type_witnesses.get(&assoc_id).copied();
        }

        // A generic call constraint may have entered the environment before
        // argument unification completed. Its receiver can therefore match
        // only after inference resolution. Such a late match is authoritative
        // when it supplies a known binding, but an unresolved binding belongs
        // to impl-argument inference and must fall through to the concrete
        // witness below.
        if let Some(bound_iface) = self
            .env
            .first_bound_for_interface_resolved(self_ty, interface_id, |ty| {
                self.icx.resolve_vars_if_possible(ty)
            })
            .filter(|bound| self.icx.resolve_args_if_possible(bound.arguments) == args)
        {
            let assoc_name = gcx.definition_ident(assoc_id).symbol;
            if let Some(binding) = bound_iface
                .bindings
                .iter()
                .find(|binding| binding.name == assoc_name)
            {
                let binding_ty = self.icx.resolve_vars_if_possible(binding.ty);
                if !binding_ty.contains_inference() {
                    return Some(binding_ty);
                }
            }
        }

        // Strategy 2: For concrete types without explicit bounds, try direct lookup.
        let interface = InterfaceReference {
            id: interface_id,
            arguments: args,
            bindings: &[],
        };
        let witness = self.conformance_witness(interface)?;
        // Witness selection has already substituted the selected block's
        // arguments, including an inherited generic base. Re-instantiating
        // with projection arguments would rebind an inherited output to Self.
        witness.type_witnesses.get(&assoc_id).copied()
    }
}
