//! Native indexing selects a logical declaration through its getter. Remaining
//! capabilities keep their own method environments, including inherited bodies.
use super::*;
use crate::sema::tycheck::solve::IndexAccessGoalData;

#[cfg(test)]
#[path = "index/tests.rs"]
mod tests;

impl<'ctx> Checker<'ctx> {
    pub(super) fn synth_index(
        &self,
        expression: &hir::Expression,
        target: &hir::Expression,
        indices: &[hir::ExpressionArgument],
        nodes: hir::IndexCallNodes,
        cs: &mut Cs<'ctx>,
    ) -> Ty<'ctx> {
        let receiver = self.synth(target, cs);
        let may_be_lazy = self
            .gcx()
            .has_lazy_callable_named(self.gcx().intern_symbol("__subscript_get"));
        let keys = indices
            .iter()
            .map(|index| self.synth_call_argument(index, None, may_be_lazy, cs))
            .collect::<Vec<_>>();
        let output = cs.infer_cx.next_ty_var(expression.span);
        let is_const_receiver = matches!(
            &target.kind,
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if matches!(
                    path.resolution,
                    hir::Resolution::Definition(
                        _,
                        DefinitionKind::Constant | DefinitionKind::AssociatedConstant
                    )
                )
        );
        let data = IndexAccessGoalData {
            receiver_addressable: self.receiver_is_addressable(target, cs) || is_const_receiver,
            nodes,
            receiver,
            keys,
            output,
            method_ty: cs.infer_cx.next_ty_var(expression.span),
            span: expression.span,
        };
        cs.record_expr_ty(nodes.receiver, receiver);
        cs.record_expr_ty(nodes.call, output);
        cs.add_goal(Goal::IndexAccess(data), expression.span);
        self.pending_indices
            .borrow_mut()
            .insert(expression.id, (nodes, expression.span));
        let roots = self.receiver_index_roots.borrow().get(&target.id).cloned();
        if let Some(roots) = roots {
            self.receiver_index_roots
                .borrow_mut()
                .insert(nodes.receiver, roots);
        }
        output
    }

    pub(super) fn finalize_index_accesses(&self, cs: &mut Cs<'ctx>) {
        let sources = cs.resolved_overload_sources();
        let instantiations = cs.resolved_instantiations();
        let mut places = self.index_place_requests.borrow().clone();
        for (node, adjustments) in cs.resolved_adjustments() {
            if adjustments.iter().any(|adjustment| {
                matches!(
                    adjustment,
                    crate::sema::tycheck::solve::Adjustment::Reference
                )
            }) {
                places.insert(node);
            }
        }
        let mut address_roots = rustc_hash::FxHashSet::default();
        for node in places {
            if let Some(roots) = self.receiver_index_roots.borrow().get(&node) {
                for (root, projections) in roots {
                    let crosses_shared_storage = projections.iter().any(|id| {
                        cs.expr_ty(*id).is_some_and(|ty| {
                            let ty = cs.infer_cx.resolve_vars_if_possible(ty);
                            matches!(ty.kind(), TyKind::Reference(_) | TyKind::Pointer(..))
                                || self.gcx().is_class_type(ty)
                        })
                    });
                    if !crosses_shared_storage {
                        address_roots.insert(*root);
                    }
                }
            }
        }
        let pending = self.pending_indices.borrow().clone();
        for (node, (nodes, span)) in pending {
            if cs.expr_ty(node).is_none() {
                continue;
            }
            self.pending_indices.borrow_mut().remove(&node);
            let Some(source) = sources.get(&nodes.call).copied() else {
                continue;
            };
            let Some(mut entry) = self.resolve_native_index(
                source,
                nodes,
                instantiations.get(&nodes.call).copied().unwrap_or_default(),
                cs,
            ) else {
                continue;
            };
            if self.index_setter_uses.borrow().contains(&node) && entry.setter.is_none() {
                self.gcx()
                    .dcx()
                    .emit_error("subscript has no set accessor".into(), Some(span));
            }
            if self.index_compound_uses.borrow().contains(&node) {
                if entry.address.is_some() {
                    address_roots.insert(node);
                } else if entry.setter.is_none() {
                    self.gcx().dcx().emit_error(
                        "numeric compound assignment requires a subscript address or set accessor"
                            .into(),
                        Some(span),
                    );
                }
            }
            if address_roots.contains(&node) {
                if entry.address.is_none() {
                    self.gcx().dcx().emit_error("this access requires a subscript address accessor; get/set does not provide element storage".into(), Some(span));
                } else {
                    entry.use_address = true;
                }
            }
            self.results.borrow_mut().native_indices.insert(node, entry);
        }
    }

    fn resolve_native_index(
        &self,
        source: hir::DefinitionID,
        nodes: hir::IndexCallNodes,
        args: crate::sema::models::GenericArguments<'ctx>,
        cs: &Cs<'ctx>,
    ) -> Option<crate::sema::tycheck::results::NativeIndex<'ctx>> {
        use crate::sema::{
            models::{GenericArgument, GenericArguments, InterfaceReference, MethodImplementation},
            tycheck::results::{NativeAccessor, NativeIndex},
        };
        let gcx = self.gcx();
        let mut receiver = cs
            .infer_cx
            .resolve_vars_if_possible(cs.expr_ty(nodes.receiver)?);
        while let TyKind::Reference(inner) = receiver.kind() {
            receiver = inner;
        }
        let (_, mut entry) = gcx.native_subscript_for_receiver(source, receiver)?;
        let mut implementation = source;
        let mut implementation_args = args;
        let parent = gcx.definition_parent(source)?;
        let required_entry =
            (gcx.definition_kind(parent) == hir::DefinitionKind::Interface).then_some(entry);
        if gcx.definition_kind(parent) == hir::DefinitionKind::Interface {
            let self_ty = args.first().and_then(|argument| {
                if let GenericArgument::Type(ty) = argument {
                    Some(*ty)
                } else {
                    None
                }
            })?;
            // Abstract/erased values expose exactly their bound capabilities.
            // Concrete values may use extra capabilities on their selected witness.
            if !matches!(
                self_ty.kind(),
                TyKind::Parameter(_)
                    | TyKind::BoxedExistential { .. }
                    | TyKind::ExistentialSelf(_)
                    | TyKind::Alias { .. }
            ) {
                let count = gcx.generics_of(parent).total_count();
                let interface = InterfaceReference {
                    id: parent,
                    arguments: gcx
                        .store
                        .interners
                        .intern_generic_args_slice(&args[..count]),
                    bindings: &[],
                };
                if let Some(witness) =
                    crate::sema::tycheck::resolve_conformance_witness_with_param_env(
                        gcx,
                        interface,
                        cs.assumptions(),
                    )
                    && let Some(method) = witness.method_witnesses.get(&source)
                    && let MethodImplementation::Concrete(actual) = method.implementation
                    && let Some((_, actual_entry)) =
                        gcx.native_subscript_for_receiver(actual, self_ty)
                {
                    implementation = actual;
                    receiver = self_ty;
                    entry = actual_entry;
                    implementation_args = gcx
                        .class_method_arguments(self_ty, actual, GenericArguments::empty())
                        .or_else(|| {
                            crate::sema::impl_engine::deduce_impl_subst(
                                gcx,
                                gcx.definition_parent(actual)?,
                                self_ty,
                                cs.assumptions(),
                            )
                        })
                        .unwrap_or_else(|| {
                            crate::sema::tycheck::utils::instantiate::instantiate_generic_args(
                                gcx,
                                method.args_template,
                                args,
                            )
                        });
                }
            }
        }
        let accessor = |id: Option<hir::DefinitionID>, requirement: Option<hir::DefinitionID>| {
            if let Some(source) = requirement {
                return Some(NativeAccessor {
                    source,
                    arguments: args,
                });
            }
            id.filter(|source| gcx.is_definition_visible(*source, self.current_def))
                .map(|source| NativeAccessor {
                    source,
                    arguments: if gcx.definition_parent(source)
                        == gcx.definition_parent(implementation)
                    {
                        implementation_args
                    } else {
                        gcx.class_method_arguments(receiver, source, GenericArguments::empty())
                            .expect("inherited subscript accessor environment")
                    },
                })
        };
        Some(NativeIndex {
            getter: NativeAccessor {
                source,
                arguments: args,
            },
            setter: accessor(entry.setter, required_entry.and_then(|entry| entry.setter)),
            address: accessor(
                entry.address,
                required_entry.and_then(|entry| entry.address),
            ),
            use_address: false,
        })
    }
}
