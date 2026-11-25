use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, HirVisitor, NodeID},
    sema::{
        models::{
            Const, ConstKind, ConstValue, GenericArgument, GenericArguments,
            GenericParameterDefinition, GenericParameterDefinitionKind, InterfaceReference, Ty,
            TyKind,
        },
        resolve::models::{DefinitionKind, TypeHead, VariantCtorKind},
        tycheck::{
            check::{checker::Checker, gather::GatherLocalsVisitor},
            infer::InferCtx,
            lower::lowerer::TypeLowerer,
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, AssignOpGoalData, BinOpGoalData,
                BindOverloadGoalData, ConstraintSystem, DerefGoalData, DisjunctionBranch, Goal,
                InferredStaticMemberGoalData, MemberGoalData, MethodCallData, StructLiteralField,
                StructLiteralGoalData, TupleAccessGoalData, UnOpGoalData,
            },
            utils::{
                arguments::validate_arity,
                const_eval::eval_const_expression_with_type_results,
                generics::{
                    GenericsBuilder, const_arg_ty_mismatches,
                    const_param_from_type_arg as generic_const_param_from_type_arg,
                    emit_const_arg_type_mismatch, error_generic_argument, expected_const_param_ty,
                },
                instantiate::{
                    instantiate_const_with_args, instantiate_interface_ref_with_args,
                    instantiate_signature_with_args, instantiate_ty_with_args,
                },
                literal::integer_expression_literal_fits,
                type_head_from_value_ty,
            },
        },
    },
    span::{Span, Symbol},
};
use rustc_hash::FxHashSet;
use std::rc::Rc;

#[path = "async_surface.rs"]
mod async_surface;
#[cfg(test)]
#[path = "await_scope_tests.rs"]
mod await_scope_tests;
#[path = "bound_method.rs"]
mod bound_method;
#[path = "brackets.rs"]
mod brackets;
#[path = "class_init.rs"]
mod class_init;
#[path = "closure.rs"]
mod closure;
#[cfg(test)]
#[path = "collection_tests.rs"]
mod collection_tests;
#[path = "expr.rs"]
mod expr;
#[path = "index.rs"]
mod index;
#[path = "path.rs"]
mod path;
#[path = "pattern.rs"]
mod pattern;
#[cfg(test)]
#[path = "property_tests.rs"]
mod property_tests;
#[path = "raw_pointer.rs"]
mod raw_pointer;
#[cfg(test)]
#[path = "result_conversion_tests.rs"]
mod result_conversion_tests;
#[path = "stmt.rs"]
mod stmt;
#[cfg(test)]
#[path = "syntax_sugar_tests.rs"]
mod syntax_sugar_tests;
#[path = "tuple_assignment.rs"]
mod tuple_assignment;

#[derive(Clone, Copy, PartialEq, Eq)]
struct ArgumentExpectation<'ctx> {
    is_lazy: bool,
    ty: Ty<'ctx>,
    expects_async_callable: bool,
}

#[derive(Clone, Copy)]
struct ResolvedCallableBound<'ctx> {
    fn_signature_ty: Option<Ty<'ctx>>,
    expects_async_callable: bool,
}

impl<'ctx> Checker<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.context
    }

    pub fn check_constant(&mut self, id: DefinitionID, node: &hir::Constant) -> bool {
        let gcx = self.gcx();
        let expected = gcx.get_type(id);
        let Some(expr) = &node.expr else {
            gcx.dcx().emit_error(
                "constant declarations must have an initializer".into(),
                Some(node.identifier.span),
            );
            return false;
        };

        let provided = self.top_level_check(expr, Some(expected));
        if provided.is_error() {
            return false;
        }

        if crate::mir::const_eval::hir_expr_needs_mir_const_eval(expr) {
            return true;
        }

        let results = self.results.borrow();
        let Some(value) = eval_const_expression_with_type_results(gcx, expr, &results) else {
            return false;
        };
        drop(results);

        gcx.cache_const(
            id,
            Const {
                ty: expected,
                kind: ConstKind::Value(value),
            },
        );
        false
    }

    pub fn check_static_variable(&mut self, id: DefinitionID, node: &hir::StaticVariable) {
        let gcx = self.gcx();
        let expected = gcx.get_type(id);

        let provided = self.top_level_check(&node.initializer, Some(expected));
        if provided.is_error() {
            return;
        }

        gcx.static_initializer_function(id);
    }

    pub fn check_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        function_context: hir::FunctionContext,
    ) {
        let gcx = self.gcx();
        let signature = gcx.get_signature(id);
        let identity_args = GenericsBuilder::identity_for_item(gcx, id);
        let signature = instantiate_signature_with_args(gcx, signature, identity_args);
        let signature = Ty::from_labeled_signature(gcx, &signature);
        let (param_tys, return_ty) = match signature.kind() {
            TyKind::FnPointer { inputs, output, .. } => (inputs, output),
            _ => unreachable!("function signature must be of function pointer type"),
        };

        let body_return_ty = if matches!(function_context, hir::FunctionContext::Initializer(_)) {
            gcx.types.void
        } else if node.is_async {
            gcx.function_body_output(id)
        } else {
            return_ty
        };

        let fallible_initializer = matches!(function_context, hir::FunctionContext::Initializer(_))
            && gcx.result_parts(return_ty).is_some();
        self.return_ty.set(Some(if fallible_initializer {
            return_ty
        } else {
            body_return_ty
        }));
        if matches!(function_context, hir::FunctionContext::Initializer(_)) {
            let binding = &node.block.as_ref().expect("initializer body").statements[0];
            let hir::StatementKind::Variable(local) = &binding.kind else {
                unreachable!("constructor self binding")
            };
            self.constructor_self.set(Some(local.pattern.id));
            let convenience = node
                .initializer_kind
                .is_some_and(|kind| kind.is_convenience);
            self.constructor_convenience.set(convenience);
            let target = gcx.constructor_value(return_ty);
            if gcx.is_class_type(target) && !convenience {
                self.constructor_payload
                    .set(gcx.ensure_class_payload(target));
                if fallible_initializer {
                    self.return_ty.set(Some(
                        gcx.constructor_result(return_ty, self.constructor_payload.get().unwrap()),
                    ));
                }
            }
        }

        let param_ids: Vec<NodeID> = node
            .signature
            .prototype
            .inputs
            .iter()
            .map(|param| param.id)
            .collect();
        let param_symbols: Vec<Symbol> = node
            .signature
            .prototype
            .inputs
            .iter()
            .map(|param| param.name.symbol)
            .collect();

        // Add Parameters To Locals Map
        for (parameter, parameter_ty) in node
            .signature
            .prototype
            .inputs
            .iter()
            .zip(param_tys.iter().cloned())
        {
            self.locals.borrow_mut().insert(
                parameter.id,
                crate::sema::tycheck::check::checker::LocalBinding {
                    ty: parameter_ty,
                    // A value receiver is a writable local copy. A reference
                    // receiver already carries access to its target storage.
                    mutable: gcx.symbol_eq(parameter.name.symbol, "self"),
                },
            );

            if let Some(expr) = &parameter.default_value {
                if let Some(bindings) = parameter.caller_bindings {
                    for (id, param) in bindings.into_iter().zip(gcx.caller_parameters()) {
                        self.locals.borrow_mut().insert(
                            id,
                            crate::sema::tycheck::check::checker::LocalBinding {
                                ty: param.ty,
                                mutable: false,
                            },
                        );
                    }
                }
                let mut checker = DefaultParamRefChecker {
                    param_ids: &param_ids,
                    param_symbols: &param_symbols,
                    found: false,
                };
                hir::walk_expression(&mut checker, expr);
                if checker.found {
                    gcx.dcx().emit_error(
                        "default parameter values cannot reference parameters".into(),
                        Some(expr.span),
                    );
                }
                self.with_return_ty(Some(parameter_ty), || {
                    self.top_level_check(expr, Some(parameter_ty));
                });
            }
        }

        let Some(body) = &node.block else {
            // Extern function declaration.
            return;
        };
        #[cfg(test)]
        gcx.dcx()
            .analysis_work
            .checked_function_bodies
            .update(|count| count + 1);

        // Async functions introduce an async context for their body.
        if node.is_async {
            self.async_depth.set(1);
        }

        let has_yield = hir::block_contains_yield(body);
        if node.is_const {
            if node.is_async {
                gcx.dcx().emit_error(
                    "`const` functions cannot be `async`".into(),
                    Some(node.signature.span),
                );
            }
            if node.is_unsafe {
                gcx.dcx().emit_error(
                    "`const` functions cannot be `unsafe`".into(),
                    Some(node.signature.span),
                );
            }
            if has_yield {
                gcx.dcx().emit_error(
                    "`const` functions cannot use `yield`".into(),
                    Some(node.signature.span),
                );
            }
        }
        let mut generator_hidden_ty = None;
        let mut effective_body_return_ty = body_return_ty;
        let mut is_async_generator = false;
        if has_yield && node.is_async {
            gcx.dcx().emit_error(
                "async generator functions do not take the `async` modifier; return `some AsyncIterator[Element = T]` or `some AsyncIterable[Element = T]` directly"
                    .into(),
                Some(node.signature.span),
            );
        } else if has_yield && !node.is_async {
            if let Some(element_ty) = self.extract_sync_generator_element_ty(id, body_return_ty) {
                self.generator_element_ty.set(Some(element_ty));
                effective_body_return_ty = gcx.types.void;
                self.return_ty.set(Some(gcx.types.void));
                if let Some(sync_gen_def) = gcx.std_item_def(hir::StdItem::SyncGenerator) {
                    let adt_def = gcx.get_struct_definition(sync_gen_def).adt_def;
                    let args = gcx.store.interners.intern_generic_args(vec![
                        crate::sema::models::GenericArgument::Type(element_ty),
                    ]);
                    let hidden = Ty::new(TyKind::Adt(adt_def, args), gcx);
                    generator_hidden_ty = Some(hidden);
                    gcx.register_sync_generator(id, element_ty);
                    self.results.borrow_mut().sync_generators.insert(id, element_ty);
                } else {
                    gcx.dcx().emit_error(
                        "synchronous generators require standard library type `SyncGenerator`"
                            .into(),
                        Some(node.signature.span),
                    );
                    self.generator_element_ty.set(Some(Ty::error(gcx)));
                }
            } else if let Some(element_ty) =
                self.extract_async_generator_element_ty(id, body_return_ty)
            {
                is_async_generator = true;
                self.async_depth.set(1);
                self.generator_element_ty.set(Some(element_ty));
                effective_body_return_ty = gcx.types.void;
                self.return_ty.set(Some(gcx.types.void));
                if let Some(async_gen_def) = gcx.std_item_def(hir::StdItem::AsyncGenerator) {
                    let adt_def = gcx.get_struct_definition(async_gen_def).adt_def;
                    let args = gcx.store.interners.intern_generic_args(vec![
                        crate::sema::models::GenericArgument::Type(element_ty),
                    ]);
                    let hidden = Ty::new(TyKind::Adt(adt_def, args), gcx);
                    generator_hidden_ty = Some(hidden);
                    gcx.register_async_generator(id, element_ty);
                    self.results
                        .borrow_mut()
                        .async_generators
                        .insert(id, element_ty);
                } else {
                    gcx.dcx().emit_error(
                        "async generators require standard library type `AsyncGenerator`"
                            .into(),
                        Some(node.signature.span),
                    );
                    self.generator_element_ty.set(Some(Ty::error(gcx)));
                }
            }
        }

        if effective_body_return_ty == gcx.types.void {
            // Unit destinations deliberately evaluate and discard their tail
            // in MIR. Only explicit return expressions promise a value here.
            self.check_block(body, None);
        } else if let Some(body) = hir::is_expression_bodied(body) {
            // --- single-expression body ---
            self.check_return(Some(body), body.span, None);
        } else {
            // --- regular block body ---
            for statement in &body.statements {
                self.check_statement(statement, None);
            }
            if let Some(tail) = body.tail.as_deref() {
                if matches!(tail.kind, hir::ExpressionKind::Return { .. }) {
                    // Explicit return checks its own value; do not register
                    // its Never expression as another opaque return candidate.
                    self.top_level_check(tail, None);
                } else {
                    // A function tail is a return site, even after statements.
                    // This records packing/wrapping adjustments on the value,
                    // and rejects mismatches before MIR construction.
                    self.check_return(Some(tail), tail.span, None);
                }
            }
        }

        if has_yield && !node.is_async {
            self.generator_element_ty.set(None);
            self.return_ty.set(Some(body_return_ty));
            if let Some(hidden) = generator_hidden_ty {
                self.opaque_return_candidates.borrow_mut().push(
                    super::checker::OpaqueReturnCandidate {
                        ty: hidden,
                        infer_cx: None,
                        span: node.signature.span,
                    },
                );
            }
        }

        if matches!(
            body_return_ty.kind(),
            TyKind::Alias {
                kind: crate::sema::models::AliasKind::Opaque,
                def_id,
                ..
            } if def_id == id
        ) {
            self.finalize_opaque_return(id, node);
        }

        if node.is_async || is_async_generator {
            self.async_depth.set(0);
        }
    }

    fn extract_async_generator_element_ty(
        &self,
        id: DefinitionID,
        body_return_ty: Ty<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let gcx = self.gcx();
        if let Some(async_gen_def) = gcx.std_item_def(hir::StdItem::AsyncGenerator)
            && let TyKind::Adt(adt, args) = body_return_ty.kind()
            && adt.id == async_gen_def
            && let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = args.first()
        {
            return Some(*elem_ty);
        }
        if !crate::sema::tycheck::opaque::is_owner_return(body_return_ty, id) {
            return None;
        }
        let iter_def = gcx.std_item_def(hir::StdItem::AsyncIterator);
        let iterable_def = gcx.std_item_def(hir::StdItem::AsyncIterable);
        let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(gcx, id);
        for constraint in &constraints {
            if let crate::sema::models::Constraint::Bound { ty, interface } = constraint.value
                && ty == body_return_ty
            {
                for superface in
                    crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(
                        gcx, interface,
                    )
                {
                    if (iter_def == Some(superface.id) || iterable_def == Some(superface.id))
                        && let Some(binding) = superface
                            .bindings
                            .iter()
                            .find(|b| gcx.symbol_eq(b.name, "Element"))
                    {
                        return Some(binding.ty);
                    }
                }
            }
        }
        None
    }

    fn extract_sync_generator_element_ty(
        &self,
        id: DefinitionID,
        body_return_ty: Ty<'ctx>,
    ) -> Option<Ty<'ctx>> {
        let gcx = self.gcx();
        if let Some(sync_gen_def) = gcx.std_item_def(hir::StdItem::SyncGenerator)
            && let TyKind::Adt(adt, args) = body_return_ty.kind()
            && adt.id == sync_gen_def
            && let Some(crate::sema::models::GenericArgument::Type(elem_ty)) = args.first()
        {
            return Some(*elem_ty);
        }
        if !crate::sema::tycheck::opaque::is_owner_return(body_return_ty, id) {
            return None;
        }
        let iter_def = gcx.std_item_def(hir::StdItem::Iterator);
        let iterable_def = gcx.std_item_def(hir::StdItem::Iterable);
        let constraints = crate::sema::tycheck::constraints::canonical_constraints_of(gcx, id);
        for constraint in &constraints {
            if let crate::sema::models::Constraint::Bound { ty, interface } = constraint.value
                && ty == body_return_ty
            {
                for superface in
                    crate::sema::impl_engine::ref_ops::collect_interface_with_superfaces(
                        gcx, interface,
                    )
                {
                    if (iter_def == Some(superface.id) || iterable_def == Some(superface.id))
                        && let Some(binding) = superface
                            .bindings
                            .iter()
                            .find(|b| gcx.symbol_eq(b.name, "Element"))
                    {
                        return Some(binding.ty);
                    }
                }
            }
        }
        None
    }

    fn finalize_opaque_return(&self, id: DefinitionID, node: &hir::Function) {
        let gcx = self.gcx();
        let mut hidden_ty = None;
        for candidate in self.opaque_return_candidates.borrow().iter() {
            let candidate_ty = candidate
                .infer_cx
                .as_ref()
                .map_or(candidate.ty, |icx| icx.resolve_vars_or_error(candidate.ty));
            if candidate_ty.is_error() {
                continue;
            }
            let candidate_ty = crate::sema::tycheck::utils::normalize_aliases(gcx, candidate_ty);
            if crate::sema::tycheck::opaque::contains_opaque_owner_through_hidden(
                gcx,
                candidate_ty,
                id,
            ) {
                gcx.dcx().emit_error(
                    "opaque return type recursively refers to itself".into(),
                    Some(candidate.span),
                );
                gcx.cache_alias_type(id, gcx.types.error);
                return;
            }
            if let Some(expected) = hidden_ty {
                if candidate_ty != expected {
                    gcx.dcx().emit_error(
                        format!(
                            "opaque return type must resolve to one concrete type; expected '{}', found '{}'",
                            expected.format(gcx),
                            candidate_ty.format(gcx)
                        ),
                        Some(candidate.span),
                    );
                }
            } else {
                hidden_ty = Some(candidate_ty);
            }
        }

        let Some(hidden_ty) = hidden_ty else {
            if self.opaque_return_candidates.borrow().is_empty() {
                gcx.dcx().emit_error(
                    "opaque-returning function has no value-producing return path".into(),
                    Some(node.signature.span),
                );
            }
            gcx.cache_alias_type(id, gcx.types.error);
            return;
        };

        let mut cs = self.new_cs();
        self.add_type_constraints(hidden_ty, node.signature.span, &mut cs);
        if let Some(bounds) = crate::sema::tycheck::opaque::opaque_return_bounds(node) {
            let lowering = crate::sema::tycheck::lower::DefTyLoweringCtx::new(id, gcx);
            for bound in bounds {
                let interfaces = lowering
                    .lowerer()
                    .lower_interface_references(hidden_ty, bound);
                for interface in interfaces {
                    if matches!(hidden_ty.kind(), TyKind::Parameter(_)) {
                        let param_env =
                            crate::sema::tycheck::constraints::canonical_constraints_of(gcx, id)
                                .into_iter()
                                .map(|constraint| constraint.value)
                                .collect::<Vec<_>>();
                        let param_env = gcx.store.arenas.global.alloc_slice_clone(&param_env);
                        let goal = interface.to_goal_with_self_ty(gcx, param_env, hidden_ty);
                        if !matches!(
                            gcx.prove_interface_goal(
                                goal,
                                crate::sema::models::SelectionMode::Typecheck,
                            ),
                            crate::sema::models::GoalResult::Proven
                        ) {
                            gcx.dcx().emit_error(
                                crate::sema::error::TypeError::NonConformance {
                                    ty: hidden_ty,
                                    interface,
                                }
                                .format(gcx),
                                Some(bound.span),
                            );
                        }
                        continue;
                    }
                    cs.add_goal(
                        Goal::Conforms {
                            ty: hidden_ty,
                            interface,
                        },
                        bound.span,
                    );
                }
            }
        }
        cs.solve_all();
        gcx.cache_alias_type(id, hidden_ty);
    }
}

impl<'ctx> Checker<'ctx> {
    pub(super) fn top_level_check(
        &self,
        expression: &hir::Expression,
        expectation: Option<Ty<'ctx>>,
    ) -> Ty<'ctx> {
        let mut cs = self.new_cs();
        let result = self.with_infer_ctx(cs.infer_cx.clone(), || {
            let provided = self.synth_with_expectation(expression, expectation, &mut cs);
            if let Some(expectation) = expectation {
                self.add_type_constraints(expectation, expression.span, &mut cs);
                cs.add_goal(
                    Goal::Coerce {
                        node_id: expression.id,
                        from: provided,
                        to: expectation,
                    },
                    expression.span,
                );
            }
            self.finish_member_values(&mut cs);
            self.finish_enum_patterns(&mut cs);
            cs.solve_all();

            self.commit_constraint_results(&mut cs, Some(expression));

            let provided = cs.infer_cx.resolve_vars_if_possible(provided);
            if provided.is_infer() {
                return Ty::error(self.gcx());
            }
            provided
        });
        result
    }

    fn new_cs(&self) -> Cs<'ctx> {
        if let Some(infer_cx) = self.infer_ctx() {
            Cs::with_infer_ctx(
                self.context,
                self.current_def,
                infer_cx,
                self.visible_traits.clone(),
            )
        } else {
            Cs::with_infer_ctx(
                self.context,
                self.current_def,
                Rc::new(InferCtx::new(self.context)),
                self.visible_traits.clone(),
            )
        }
    }

    /// Commits all resolved results from a constraint system to the checker's results.
    /// Used when solving sub-expressions in separate constraint systems (e.g., match scrutinee).
    fn commit_constraint_results(
        &self,
        cs: &mut Cs<'ctx>,
        root_expr: Option<&hir::Expression>,
    ) {
        for site in cs.opaque_return_sites() {
            if site.node_id.is_none() {
                self.gcx().dcx().emit_error(
                    "an opaque-returning function must return a value".into(),
                    Some(site.span),
                );
            } else {
                self.opaque_return_candidates.borrow_mut().push(
                    super::checker::OpaqueReturnCandidate {
                        ty: site.ty,
                        span: site.span,
                        infer_cx: Some(cs.infer_cx.clone()),
                    },
                );
            }
        }
        self.finalize_compound_assignments(cs);
        self.finalize_index_accesses(cs);
        self.finalize_lazy_arguments(cs, root_expr);
        self.finalize_closure_captures(cs);
        let expression_types = cs.resolved_expr_types();

        // A generic default can finish resolving after method binding. Hidden
        // payload types are legal only under their existential binder, never as
        // independently usable expression storage. Diagnose before codegen.
        if !self.gcx().dcx().has_error()
            && let Some((&id, _)) = expression_types
                .iter()
                .filter(|(_, ty)| {
                    crate::sema::tycheck::utils::erased_self::has_free_self(
                        cs.infer_cx.resolve_vars_if_possible(**ty),
                    )
                })
                .min_by_key(|(id, _)| **id)
        {
            let span = self
                .expression_contexts
                .borrow()
                .get(&id)
                .map(|(span, _)| *span);
            self.gcx().dcx().emit_error(
                crate::sema::error::TypeError::ErasedMethodUsesHiddenType.format(self.gcx()),
                span,
            );
        }
        // Diagnose concrete snapshot representation limits at the source use,
        // before release inlining can move or erase the corresponding local.
        let mut expression_types: Vec<_> = expression_types.into_iter().collect();
        expression_types.sort_by_key(|(id, _)| *id);
        for (id, ty) in expression_types {
            let ty = cs.infer_cx.resolve_vars_or_error(ty);
            let ty = if crate::sema::tycheck::utils::erased_self::has_free_self(ty) {
                Ty::error(self.gcx())
            } else {
                ty
            };
            if !self.gcx().dcx().has_error()
                && let Some((span, _)) = self.expression_contexts.borrow().get(&id)
            {
                let _ = crate::sema::tycheck::utils::atomic_handle::validate(self.gcx(), ty, *span);
            }
            self.results.borrow_mut().record_node_type(id, ty);

            if let TyKind::Closure { closure_def_id, .. } = ty.kind() {
                self.update_closure_signature(closure_def_id, ty);
            }
        }
        for (id, adjustments) in cs.resolved_adjustments() {
            self.validate_raw_deref_adjustments(id, &adjustments, cs);
            let adjustments: Vec<_> = adjustments
                .into_iter()
                .map(|adjustment| self.resolve_adjustment(cs, adjustment))
                .collect();
            self.results
                .borrow_mut()
                .record_node_adjustments(id, adjustments);
        }
        for (id, conversion) in cs.resolved_result_propagation_conversions() {
            let kind = match conversion.kind {
                crate::sema::tycheck::results::ResultPropagationConversionKind::BoxExistential {
                    interfaces,
                } => crate::sema::tycheck::results::ResultPropagationConversionKind::BoxExistential {
                    interfaces: self.resolve_interface_refs_for_adjustment(cs, interfaces),
                },
                crate::sema::tycheck::results::ResultPropagationConversionKind::From {
                    method_id,
                    generic_args,
                } => crate::sema::tycheck::results::ResultPropagationConversionKind::From {
                    method_id,
                    generic_args: self.resolve_generic_args_or_error(cs, generic_args),
                },
            };
            let target_ty = cs.infer_cx.resolve_vars_or_error(conversion.target_ty);
            self.results
                .borrow_mut()
                .record_result_propagation_conversion(
                    id,
                    crate::sema::tycheck::results::ResultPropagationConversion { kind, target_ty },
                );
        }
        for (id, info) in cs.resolved_interface_calls() {
            self.results.borrow_mut().record_interface_call(id, info);
        }
        for (id, def_id) in cs.resolved_overload_sources() {
            self.results.borrow_mut().record_overload_source(id, def_id);
        }
        for (id, resolution) in cs.resolved_value_resolutions() {
            self.results
                .borrow_mut()
                .record_value_resolution(id, resolution);
        }
        for (id, index) in cs.resolved_field_indices() {
            self.results.borrow_mut().record_field_index(id, index);
        }
        for (id, info) in cs.resolved_property_reads() {
            self.results.borrow_mut().record_property_read(id, info);
        }
        for (id, args) in cs.resolved_instantiations() {
            let resolved_args = cs.infer_cx.resolve_args_if_possible(args);
            self.results
                .borrow_mut()
                .record_instantiation(id, resolved_args);
        }
        for (id, ty) in cs.resolved_local_types() {
            let ty = cs.infer_cx.resolve_vars_or_error(ty);
            self.finalize_local(id, ty);
            self.results.borrow_mut().record_node_type(id, ty);
        }

        self.finalize_deferred_async_call_surface_checks(cs);
    }

    fn resolve_adjustment(&self, cs: &Cs<'ctx>, adjustment: Adjustment<'ctx>) -> Adjustment<'ctx> {
        match adjustment {
            Adjustment::DerefCall {
                method,
                arguments,
                result,
            } => Adjustment::DerefCall {
                method,
                arguments: self.resolve_generic_args_or_error(cs, arguments),
                result: cs.structurally_resolve(result),
            },
            Adjustment::BoxExistential { from, interfaces } => Adjustment::BoxExistential {
                from: cs.infer_cx.resolve_vars_or_error(from),
                interfaces: self.resolve_interface_refs_for_adjustment(cs, interfaces),
            },
            Adjustment::CollectionToSpan { to } => Adjustment::CollectionToSpan {
                to: cs.infer_cx.resolve_vars_or_error(to),
            },
            Adjustment::ClassUpcast { to } => Adjustment::ClassUpcast {
                to: cs.infer_cx.resolve_vars_or_error(to),
            },
            Adjustment::NullPointer { to } => Adjustment::NullPointer {
                to: cs.infer_cx.resolve_vars_or_error(to),
            },
            Adjustment::ExistentialUpcast { from, to } => Adjustment::ExistentialUpcast {
                from: cs.infer_cx.resolve_vars_or_error(from),
                to: cs.infer_cx.resolve_vars_or_error(to),
            },
            Adjustment::OptionalWrap {
                is_some,
                generic_args,
            } => Adjustment::OptionalWrap {
                is_some,
                generic_args: self.resolve_generic_args_or_error(cs, generic_args),
            },
            Adjustment::ResultOkWrap { generic_args } => Adjustment::ResultOkWrap {
                generic_args: self.resolve_generic_args_or_error(cs, generic_args),
            },
            other => other,
        }
    }

    fn resolve_interface_refs_for_adjustment(
        &self,
        cs: &Cs<'ctx>,
        interfaces: &'ctx [InterfaceReference<'ctx>],
    ) -> &'ctx [InterfaceReference<'ctx>] {
        if interfaces.is_empty() {
            return interfaces;
        }

        let resolved: Vec<_> = interfaces
            .iter()
            .map(|iface| {
                let arguments = self.resolve_generic_args_or_error(cs, iface.arguments);
                let bindings: Vec<_> = iface
                    .bindings
                    .iter()
                    .map(|binding| crate::sema::models::AssociatedTypeBinding {
                        name: binding.name,
                        ty: cs.infer_cx.resolve_vars_or_error(binding.ty),
                    })
                    .collect();
                let bindings = self.gcx().store.arenas.global.alloc_slice_clone(&bindings);

                InterfaceReference {
                    id: iface.id,
                    arguments,
                    bindings,
                }
            })
            .collect();

        self.gcx().store.arenas.global.alloc_slice_clone(&resolved)
    }

    fn resolve_generic_args_or_error(
        &self,
        cs: &Cs<'ctx>,
        args: GenericArguments<'ctx>,
    ) -> GenericArguments<'ctx> {
        if args.is_empty() {
            return args;
        }

        let resolved: Vec<_> = args
            .iter()
            .map(|arg| match arg {
                GenericArgument::Type(ty) => {
                    GenericArgument::Type(cs.infer_cx.resolve_vars_or_error(*ty))
                }
                GenericArgument::Const(c) => {
                    GenericArgument::Const(cs.infer_cx.resolve_const_if_possible(*c))
                }
            })
            .collect();

        self.gcx().store.interners.intern_generic_args(resolved)
    }
}

type Cs<'c> = ConstraintSystem<'c>;

struct DefaultParamRefChecker<'a> {
    param_ids: &'a [NodeID],
    param_symbols: &'a [Symbol],
    found: bool,
}

impl<'a> hir::HirVisitor for DefaultParamRefChecker<'a> {
    fn visit_resolved_path(&mut self, node: &hir::ResolvedPath) -> Self::Result {
        if let hir::ResolvedPath::Resolved(path) = node {
            match path.resolution {
                hir::Resolution::LocalVariable(id) => {
                    if self.param_ids.contains(&id) {
                        self.found = true;
                    }
                }
                hir::Resolution::Error => {
                    if path
                        .segments
                        .iter()
                        .any(|segment| self.param_symbols.contains(&segment.identifier.symbol))
                    {
                        self.found = true;
                    }
                }
                _ => {}
            }
        }
        hir::walk_resolved_path(self, node)
    }
}

#[cfg(test)]
mod block_tail_tests {
    #[test]
    fn implicit_unit_tails_discard_values_but_explicit_returns_do_not() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "func single() { 7_i32 }\nfunc block() { var value: int32 = 9; value }\nfunc main() { single(); block() }",
        );
        assert!(errors.is_empty(), "{errors:#?}");
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "func explicit() { return 7_i32 }\nfunc main() {}",
        );
        assert!(!errors.is_empty(), "explicit return must match unit result");
        assert!(
            errors
                .iter()
                .all(|error| !error.message.contains("internal error")),
            "{errors:#?}"
        );
    }

    #[test]
    fn contextual_match_with_a_unit_path_is_not_classified_as_diverging() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "func select(_ flag: bool) -> int32 { loop { match flag { case true => return 7\ncase false => { match flag { case true => {}\ncase false => return 9\n} }\n} } }\nfunc main() {}",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn declared_return_context_coerces_conditional_and_match_arms() {
        for tail in [
            "if flag { first } else { second }",
            "match flag { case true => first\ncase false => second\n}",
        ] {
            let source = format!(
                "interface Read {{ func read() -> int32; }}\nstruct First {{ value: int32 }}\nstruct Second {{ value: int32 }}\nconform First to Read {{ func read() -> int32 {{ self.value }}\n}}\nconform Second to Read {{ func read() -> int32 {{ self.value }}\n}}\nfunc choose(_ flag: bool) -> any Read {{ first := First {{ value: 7 }}; second := Second {{ value: 9 }}; {tail} }}\nfunc main() {{}}"
            );
            let errors = crate::test_support::analyze_script_mir_diagnostics(&source);
            assert!(errors.is_empty(), "{tail}\n{errors:#?}");
        }
    }

    #[test]
    fn regular_block_tails_apply_declared_return_coercions() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "interface Read { func read() -> int32; }\nstruct Value { value: int32 }\nconform Value to Read { func read() -> int32 { self.value }\n}\nfunc boxed() -> any Read { value := Value { value: 7 }; value }\nfunc main() { value := boxed(); observed := value.read() }",
        );
        assert!(errors.is_empty(), "{errors:#?}");
    }

    #[test]
    fn regular_block_tail_mismatches_are_source_diagnostics() {
        let errors = crate::test_support::analyze_script_mir_diagnostics(
            "func wrong() -> int32 { var value: bool = true; value }\nfunc main() {}",
        );
        assert!(!errors.is_empty(), "invalid tail must be rejected");
        assert!(
            errors
                .iter()
                .all(|error| !error.message.contains("internal error")),
            "{errors:#?}"
        );
    }
}
