use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, HirVisitor, NodeID},
    sema::{
        models::{
            Const, ConstKind, ConstValue, GenericArgument, GenericArguments,
            GenericParameterDefinition, GenericParameterDefinitionKind, IntTy, InterfaceReference,
            Ty, TyKind, UIntTy,
        },
        resolve::models::{DefinitionKind, TypeHead, VariantCtorKind},
        tycheck::{
            check::{checker::Checker, gather::GatherLocalsVisitor},
            infer::InferCtx,
            lower::lowerer::TypeLowerer,
            solve::{
                Adjustment, ApplyArgument, ApplyGoalData, AssignOpGoalData, BinOpGoalData,
                BindOverloadGoalData, CompilerCallContext, ConstraintSystem, DerefGoalData,
                DisjunctionBranch, Goal, InferredStaticMemberGoalData, MemberGoalData,
                MethodCallData, StructLiteralField, StructLiteralGoalData, TupleAccessGoalData,
                UnOpGoalData, match_arguments_to_parameters, validate_arity,
            },
            utils::{
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
#[path = "closure.rs"]
mod closure;
#[path = "expr.rs"]
mod expr;
#[path = "path.rs"]
mod path;
#[path = "pattern.rs"]
mod pattern;
#[path = "stmt.rs"]
mod stmt;

#[derive(Clone, Copy, PartialEq, Eq)]
struct ArgumentExpectation<'ctx> {
    ty: Ty<'ctx>,
    expects_async_callable: bool,
}

#[derive(Clone, Copy)]
struct ResolvedCallableBound<'ctx> {
    fn_signature_ty: Ty<'ctx>,
    expects_async_callable: bool,
}

impl<'ctx> Checker<'ctx> {
    pub fn gcx(&self) -> Gcx<'ctx> {
        self.context
    }

    pub fn check_constant(&mut self, id: DefinitionID, node: &hir::Constant) {
        let gcx = self.gcx();
        let expected = gcx.get_type(id);
        let Some(expr) = &node.expr else {
            gcx.dcx().emit_error(
                "constant declarations must have an initializer".into(),
                Some(node.identifier.span),
            );
            return;
        };

        let provided = self.top_level_check(expr, Some(expected));
        if provided.is_error() {
            return;
        }

        let results = self.results.borrow();
        let Some(value) = eval_const_expression_with_type_results(gcx, expr, &results) else {
            return;
        };
        drop(results);

        gcx.cache_const(
            id,
            Const {
                ty: expected,
                kind: ConstKind::Value(value),
            },
        );
    }

    pub fn check_static_variable(&mut self, id: DefinitionID, node: &hir::StaticVariable) {
        let gcx = self.gcx();
        let expected = gcx.get_type(id);

        let provided = self.top_level_check(&node.initializer, Some(expected));
        if provided.is_error() {
            return;
        }

        let value = match self.results.borrow().value_resolution(node.initializer.id) {
            Some(hir::Resolution::Definition(
                ctor_id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
            )) => Some(ConstValue::EnumUnitVariant(ctor_id)),
            _ => {
                let results = self.results.borrow();
                eval_const_expression_with_type_results(gcx, &node.initializer, &results)
            }
        };
        let Some(value) = value else {
            return;
        };

        gcx.cache_static_initializer(
            id,
            Const {
                ty: expected,
                kind: ConstKind::Value(value),
            },
        );
    }

    pub fn check_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        _: hir::FunctionContext,
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

        let body_return_ty = if node.is_async {
            gcx.function_body_output(id)
        } else {
            return_ty
        };

        self.return_ty.set(Some(body_return_ty));

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
                    mutable: false,
                },
            );

            if let Some(expr) = &parameter.default_value {
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

        // Async functions introduce an async context for their body.
        if node.is_async {
            self.async_depth.set(1);
        }

        if let Some(body) = hir::is_expression_bodied(body) {
            // --- single-expression body ---
            self.check_return(Some(body), body.span, None);
        } else {
            // --- regular block body ---
            self.check_block(body, None);
            if matches!(
                body_return_ty.kind(),
                TyKind::Alias {
                    kind: crate::sema::models::AliasKind::Opaque,
                    def_id,
                    ..
                } if def_id == id
            ) && let Some(tail) = body.tail.as_deref()
                && !matches!(tail.kind, hir::ExpressionKind::Return { .. })
                && let Some(ty) = self.results.borrow().try_node_type(tail.id)
            {
                self.opaque_return_candidates.borrow_mut().push(
                    crate::sema::tycheck::check::checker::OpaqueReturnCandidate {
                        ty,
                        infer_cx: None,
                        span: tail.span,
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

        if node.is_async {
            self.async_depth.set(0);
        }
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
                                format!(
                                    "type '{}' does not conform to interface '{}'",
                                    hidden_ty.format(gcx),
                                    interface.format(gcx)
                                ),
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
    fn top_level_check(
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
            cs.solve_all();

            self.commit_constraint_results(&cs);

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
    fn commit_constraint_results(&self, cs: &Cs<'ctx>) {
        for (id, ty) in cs.resolved_expr_types() {
            let ty = cs.infer_cx.resolve_vars_or_error(ty);
            self.results.borrow_mut().record_node_type(id, ty);

            // FIX: Update closure signature with resolved types to ensure codegen sees concrete types
            if let TyKind::Closure { closure_def_id, .. } = ty.kind() {
                self.update_closure_signature(closure_def_id, ty);
            }
        }
        for (id, adjustments) in cs.resolved_adjustments() {
            let adjustments: Vec<_> = adjustments
                .into_iter()
                .map(|adjustment| self.resolve_adjustment(cs, adjustment))
                .collect();
            self.results
                .borrow_mut()
                .record_node_adjustments(id, adjustments);
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
        for (id, info) in cs.resolved_property_writes() {
            self.results.borrow_mut().record_property_write(id, info);
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
        self.finalize_deferred_async_property_surface_checks(cs);
    }

    fn resolve_adjustment(&self, cs: &Cs<'ctx>, adjustment: Adjustment<'ctx>) -> Adjustment<'ctx> {
        match adjustment {
            Adjustment::BoxExistential { from, interfaces } => Adjustment::BoxExistential {
                from: cs.infer_cx.resolve_vars_or_error(from),
                interfaces: self.resolve_interface_refs_for_adjustment(cs, interfaces),
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

fn integer_literal_fits<'ctx>(value: u64, ty: Ty<'ctx>) -> bool {
    let value = value as u128;
    match ty.kind() {
        TyKind::UInt(kind) => value <= unsigned_max_u128(kind),
        TyKind::Int(kind) => value <= signed_nonnegative_max_u128(kind),
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
