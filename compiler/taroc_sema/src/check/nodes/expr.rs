use crate::{
    CommonTypes,
    check::{
        context::func::FnCtx,
        expectation::Expectation,
        gather::GatherLocalsVisitor,
        nodes::apply::{ValidationError, match_arguments_to_parameters, validate_arity},
        solver::{
            BinaryOperatorGoal, DerefGoal, FieldAccessGoal, Goal, MethodCallGoal, Obligation,
            OverloadArgument, OverloadGoal, ReferenceGoal, TupleAccessGoal, UnaryOperatorGoal,
            cast::CastGoal,
        },
    },
    infer::fn_var::FnVarData,
    lower::{LoweringRequest, TypeLowerer},
    ty::{Constraint, GenericArguments, InferTy, Ty, TyKind, VariantDefinition},
    utils::{instantiate_constraint_with_args, instantiate_ty_with_args, labeled_signature_to_ty},
};
use rustc_hash::FxHashMap;
use taroc_hir::{
    BinaryOperator, DefinitionID, DefinitionKind, Mutability, NodeID, Resolution, UnaryOperator,
};
use taroc_span::Span;

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn check_expression(&self, expression: &taroc_hir::Expression) -> Ty<'ctx> {
        self.check_expression_with_expectation(expression, Expectation::None)
    }

    pub fn check_expression_with_expectation(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        self.check_expression_with_expectation_and_arguments(expression, expectation)
    }

    pub fn check_expression_has_type(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Ty<'ctx>,
    ) -> Ty<'ctx> {
        let ty =
            self.check_expression_with_expectation(expression, Expectation::HasType(expectation));
        ty
    }

    pub fn check_expression_coercible_to_type(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Ty<'ctx>,
        _: Option<&taroc_hir::Expression>,
    ) -> Ty<'ctx> {
        let ty = self.check_expression_with_hint(expression, expectation);
        self.add_coercion_constraint(ty, expectation, expression.id, expression.span);
        expectation
    }

    pub fn add_coercion_constraint(
        &self,
        from: Ty<'ctx>,
        to: Ty<'ctx>,
        node: NodeID,
        location: Span,
    ) {
        // break early
        if from == to {
            return;
        }

        let obligation = Obligation {
            location: location,
            goal: Goal::Coerce { from, to, node },
        };
        self.add_obligation(obligation);
    }

    pub fn check_expression_with_hint(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Ty<'ctx>,
    ) -> Ty<'ctx> {
        self.check_expression_with_expectation(expression, Expectation::HasType(expectation))
    }

    pub fn check_expression_with_expectation_and_arguments(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let ty = self.check_expression_kind(expression, expectation);
        // Record the (possibly inferred) type for this expression node
        self.results
            .borrow_mut()
            .node_types
            .insert(expression.id, ty);
        ty
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_expression_kind(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        // self.gcx
        //     .diagnostics
        //     .warn("Checking".into(), expression.span);
        match &expression.kind {
            taroc_hir::ExpressionKind::Literal(literal) => {
                self.check_literal_expression(literal, expectation)
            }
            taroc_hir::ExpressionKind::Path(path) => self.check_path_expression(path, expression),
            taroc_hir::ExpressionKind::Reference(node, mutability) => {
                self.check_reference_expression(node, *mutability, expression.span)
            }
            taroc_hir::ExpressionKind::Dereference(node) => {
                self.check_dereference_expression(node, expression.span)
            }
            taroc_hir::ExpressionKind::Tuple(expressions) => {
                self.check_tuple_expression(&expressions, expectation, expression)
            }
            taroc_hir::ExpressionKind::If(node) => {
                self.check_if_expression(node, expression, expectation)
            }
            taroc_hir::ExpressionKind::Block(block) => {
                self.check_block_expression(block, expectation)
            }
            taroc_hir::ExpressionKind::Await(expression) => {
                self.check_expression_with_expectation(expression, expectation)
            }
            taroc_hir::ExpressionKind::FunctionCall(callee, args) => {
                self.check_function_call_expression(expression, callee, args, expectation)
            }
            taroc_hir::ExpressionKind::Assign(lhs, rhs) => self.check_assign_expression(lhs, rhs),
            taroc_hir::ExpressionKind::StructLiteral(lit) => {
                self.check_struct_expression(lit, expression)
            }
            taroc_hir::ExpressionKind::FieldAccess(target, field) => {
                self.check_field_access_expression(target, field, expression)
            }
            taroc_hir::ExpressionKind::TupleAccess(target, field) => {
                self.check_tuple_access_expression(target, field, expression)
            }
            taroc_hir::ExpressionKind::MethodCall(node) => {
                self.check_method_call_expr(node, expression, expectation)
            }
            taroc_hir::ExpressionKind::Unary(op, expr) => {
                self.check_unary_expression(*op, expr, expression, expectation)
            }
            taroc_hir::ExpressionKind::Binary(op, lhs, rhs) => {
                self.check_binary_expression(*op, lhs, rhs, expression, expectation)
            }
            taroc_hir::ExpressionKind::AssignOp(op, lhs, rhs) => {
                self.check_assign_op_expression(*op, lhs, rhs, expression)
            }
            taroc_hir::ExpressionKind::Subscript(target, arguments) => {
                self.check_subscript_expression(target, arguments, expression, expectation)
            }
            taroc_hir::ExpressionKind::CastAs(target, ty) => {
                self.check_cast_expression(target, ty, expression)
            }
            taroc_hir::ExpressionKind::Match(node) => {
                self.check_match_expression(node, expression.span)
            }
            taroc_hir::ExpressionKind::PatternBinding(_) => {
                todo!("ICE: unimplemented tycheck expression node")
            }
            taroc_hir::ExpressionKind::ArrayLiteral(..) => {
                todo!("ICE: unimplemented tycheck expression node")
            }
            taroc_hir::ExpressionKind::Closure(_) => {
                todo!("ICE: unimplemented tycheck expression node")
            }
            taroc_hir::ExpressionKind::Malformed => {
                unreachable!("ICE: trying to typecheck a malformed expression node")
            }
        }
    }
}
impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn common_types(&self) -> &CommonTypes<'ctx> {
        &self.gcx.store.common_types
    }

    pub fn error_ty(&self) -> Ty<'ctx> {
        self.common_types().error
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_literal_expression(
        &self,
        literal: &taroc_hir::Literal,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        match literal {
            taroc_hir::Literal::Bool(_) => self.common_types().bool,
            taroc_hir::Literal::Rune(_) => self.common_types().rune,
            taroc_hir::Literal::String(_) => self.common_types().string,
            taroc_hir::Literal::Integer(_) => {
                let opt_ty = expectation.to_option().and_then(|ty| match ty.kind() {
                    TyKind::Int(_) | TyKind::UInt(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| self.next_int_var())
            }
            taroc_hir::Literal::Float(_) => {
                let opt_ty = expectation.to_option().and_then(|ty| match ty.kind() {
                    TyKind::Float(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| self.next_float_var())
            }
            taroc_hir::Literal::Nil => {
                todo!("nil coercions");
            }
        }
    }

    fn check_reference_expression(
        &self,
        node: &taroc_hir::Expression,
        mutability: Mutability,
        span: Span,
    ) -> Ty<'ctx> {
        let ty = self.check_expression(node);
        let alpha = self.next_ty_var(span);
        let goal = Goal::Ref(ReferenceGoal {
            ty,
            mutability,
            alpha,
        });

        let obligation = Obligation {
            location: span,
            goal,
        };

        self.add_obligation(obligation);

        alpha
    }

    fn check_dereference_expression(&self, node: &taroc_hir::Expression, span: Span) -> Ty<'ctx> {
        let ty = self.check_expression(node);
        let alpha = self.next_ty_var(span);
        let goal = Goal::Deref(DerefGoal { ty, alpha });

        let obligation = Obligation {
            location: span,
            goal,
        };

        self.add_obligation(obligation);

        alpha
    }

    fn check_tuple_expression(
        &self,
        elements: &[Box<taroc_hir::Expression>],
        expectation: Expectation<'ctx>,
        _: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        // if we have an expected type that is a tuple, get it's elements to check against
        let expected_tys = expectation.only_has_type().and_then(|ty| match ty.kind() {
            TyKind::Tuple(elements) => Some(elements),
            _ => None,
        });

        let tys = elements.iter().enumerate().map(|(index, expression)| {
            // if we have an expectation check coercion, otherwise check without an expectation
            let result = match expected_tys {
                Some(expected_elements) if index < expected_elements.len() => {
                    let expectation = expected_elements[index];
                    self.check_expression_coercible_to_type(expression, expectation, None)
                }
                _ => self.check_expression(expression),
            };
            result
        });

        let tys = self.gcx.store.interners.intern_ty_list(&tys.collect());
        let ty = self.gcx.mk_ty(TyKind::Tuple(tys));

        return ty;
    }

    fn check_block_expression(
        &self,
        block: &taroc_hir::Block,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        for (index, statement) in block.statements.iter().enumerate() {
            let is_last = index == block.statements.len() - 1;

            let resulting_ty =
                self.check_statement(statement, if is_last { Some(expectation) } else { None });

            if is_last && let Some(result) = resulting_ty {
                return result;
            }
        }

        self.common_types().void
    }

    fn check_if_expression(
        &self,
        node: &taroc_hir::IfExpression,
        _: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        // TODO: Coercions
        let _ = self.check_expression_has_type(&node.condition, self.common_types().bool);

        let then_ty = self.check_expression_with_expectation(&node.then_block, expectation);
        if let Some(else_node) = &node.else_block {
            let _ = self.check_expression_with_expectation(else_node, expectation);
        }

        return then_ty;
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_assign_expression(
        &self,
        lhs: &taroc_hir::Expression,
        rhs: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let lhs_ty = self.check_expression(lhs);
        self.check_expression_coercible_to_type(rhs, lhs_ty, None);
        return self.common_types().void;
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn check_function_call_expression(
        &self,
        expression: &taroc_hir::Expression,
        callee: &taroc_hir::Expression,
        args: &[taroc_hir::ExpressionArgument],
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let callee_ty = self.check_expression(callee);

        self.check_function_call_with_type(callee_ty, args, expression, expectation)
    }

    fn check_function_call_with_type(
        &self,
        callee_ty: Ty<'ctx>,
        args: &[taroc_hir::ExpressionArgument],
        call_expr: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let fn_return_ty = match callee_ty.kind() {
            TyKind::Infer(InferTy::FnVar(_) | InferTy::TyVar(_)) => {
                self.check_call_overloaded(callee_ty, args, call_expr, expectation)
            }
            TyKind::FnDef(id, fn_args) => self.check_call_single(id, fn_args, args, call_expr.span),
            _ => {
                if callee_ty.is_error() {
                    return callee_ty;
                }

                self.gcx.diagnostics.error(
                    format!(
                        "cannot invoke non-function type '{}'",
                        callee_ty.format(self.gcx)
                    ),
                    call_expr.span,
                );
                return self.error_ty();
            }
        };

        fn_return_ty
    }

    fn check_call_single(
        &self,
        id: DefinitionID,
        fn_args: GenericArguments<'ctx>,
        call_arguments: &[taroc_hir::ExpressionArgument],
        full_span: Span,
    ) -> Ty<'ctx> {
        let gcx = self.gcx;
        let signature = gcx.fn_signature(id);
        let signature_ty = labeled_signature_to_ty(signature, gcx);
        let signature_ty = instantiate_ty_with_args(gcx, signature_ty, fn_args);

        let (inputs, output) = match signature_ty.kind() {
            TyKind::Function { inputs, output } => (inputs, output),
            _ => unreachable!(),
        };

        let provided_arguments: Vec<OverloadArgument> = call_arguments
            .iter()
            .map(|node| {
                let ty = self.check_expression(&node.expression);
                OverloadArgument {
                    ty,
                    span: node.span,
                    label: node.label.as_ref().map(|n| n.identifier),
                    id: node.expression.id,
                }
            })
            .collect();

        // Arity Check
        match validate_arity(signature, &provided_arguments) {
            Err(err) => {
                gcx.diagnostics.error(format!("{err}"), full_span);
                return self.error_ty();
            }
            _ => {}
        }

        // Label / Positional Check
        let positions = match match_arguments_to_parameters(signature, &provided_arguments) {
            Ok(p) => p,
            Err(err) => {
                gcx.diagnostics.error(format!("{err}"), full_span);
                return self.error_ty();
            }
        };

        for (param_idx, arg_idx) in positions.iter().enumerate() {
            let param_defaults = signature.inputs[param_idx].has_default;
            let param_ty = inputs[param_idx];

            if let Some(arg_idx) = arg_idx {
                let argument = provided_arguments[*arg_idx];
                let arg_ty = argument.ty;
                self.add_coercion_constraint(arg_ty, param_ty, argument.id, argument.span);
            } else if !param_defaults {
                let err = ValidationError::MissingRequiredParameter {
                    param_index: param_idx,
                    param_name: signature.inputs[param_idx].name,
                };
                gcx.diagnostics.error(format!("{err}"), full_span);
                return self.error_ty();
            }
        }

        output
    }

    fn check_call_overloaded(
        &self,
        callee_ty: Ty<'ctx>,
        args: &[taroc_hir::ExpressionArgument],
        call_expr: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let beta: Vec<_> = args
            .iter()
            .map(|arg| {
                let argument = OverloadArgument {
                    ty: self.next_ty_var(arg.span),
                    span: arg.span,
                    label: arg.label.as_ref().map(|l| l.identifier),
                    id: arg.expression.id,
                };

                argument
            })
            .collect();

        let beta = self.gcx.store.interners.intern_slice(&beta);
        let rho = self.next_ty_var(call_expr.span);

        for (arg, beta) in args.iter().zip(beta) {
            let arg_ty = self.check_expression(&arg.expression);
            self.add_obligation(Obligation {
                location: call_expr.span,
                goal: Goal::Constraint(Constraint::TypeEquality(arg_ty, beta.ty)),
            });
        }

        // Obligation for return type
        if let Some(e_ty) = expectation.only_has_type() {
            self.add_obligation(Obligation {
                location: call_expr.span,
                goal: Goal::Coerce {
                    from: rho,
                    to: e_ty,
                    node: call_expr.id,
                },
            });
        }

        let goal = OverloadGoal {
            expr_span: call_expr.span,
            expr_id: call_expr.id,
            callee_id: call_expr.id,
            callee_var: callee_ty,
            result_var: rho,
            expected_result_ty: expectation.only_has_type(),
            arguments: beta,
            callee_span: call_expr.span,
        };

        self.add_obligation(Obligation {
            location: call_expr.span,
            goal: Goal::Apply(goal),
        });

        return rho;
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_path_expression(
        &self,
        path: &taroc_hir::Path,
        expression: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let resolution = self.perform_path_resolution(expression.id, path);

        let ty = match resolution {
            Resolution::Error => {
                // should be pre-reported atp
                self.error_ty()
            }
            Resolution::Definition(_, DefinitionKind::Variant) => {
                unreachable!("ICE: should use Variant constructor instead!")
            }

            Resolution::FunctionSet(candidates) => {
                let data = FnVarData {
                    candidates: candidates.iter().cloned().collect(),
                    maybe_variadic: false,
                    min_required: 0,
                };

                self.next_fn_var(path.span, data)
            }
            _ => self.instantiate_value_path(expression.id, path, resolution),
        };

        ty
    }

    pub fn perform_path_resolution(
        &self,
        id: taroc_hir::NodeID,
        path: &taroc_hir::Path,
    ) -> taroc_hir::Resolution {
        let partial_res = self.gcx.resolution(id);

        if let Some(full) = partial_res.full_resolution() {
            return full;
        }

        let qualified = &path.segments[..path.segments.len() - partial_res.unresolved_segments];
        let qualified_span = qualified
            .first()
            .unwrap()
            .span
            .to(qualified.last().unwrap().span);
        let ast_ty = taroc_hir::Type {
            id: qualified.last().unwrap().id,
            span: qualified_span,
            kind: taroc_hir::TypeKind::Path(taroc_hir::Path {
                span: qualified_span,
                segments: qualified.iter().cloned().collect(),
            }),
        };

        let self_ty = self
            .lowerer()
            .lower_type(&ast_ty, &LoweringRequest::default());

        let unresolved = path.segments.last().unwrap();

        let result = self.resolve_qualified_method_call(unresolved.identifier, self_ty);

        match result {
            Ok(result) => result,
            Err(_) => {
                let msg = format!(
                    "unknown associated symbol named '{}' on type '{}'",
                    unresolved.identifier.symbol,
                    self_ty.format(self.gcx)
                );
                self.gcx.diagnostics.error(msg, unresolved.identifier.span);
                return Resolution::Error;
            }
        }
    }

    pub fn instantiate_value_path(
        &self,
        id: taroc_hir::NodeID,
        path: &taroc_hir::Path,
        resolution: taroc_hir::Resolution,
    ) -> Ty<'ctx> {
        // TODO: Generics Checks

        if let Resolution::Local(id) = resolution {
            return *self
                .locals
                .borrow()
                .get(&id)
                .expect("local must have type stored");
        };

        let def_id = resolution.def_id().unwrap();
        self.rcx
            .results
            .borrow_mut()
            .assoc_resolution
            .insert(id, Ok((def_id, self.gcx.def_kind(def_id))));

        let ty = self.gcx.type_of(def_id);

        let ty = instantiate_ty_with_args(self.gcx, ty, self.fresh_args_for_def(def_id, path.span));
        // TODO: ARGUMENTS
        return ty;
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_struct_expression(
        &self,
        literal: &taroc_hir::StructLiteral,
        expr: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let result = self.check_struct_path(&literal.path, expr.id);

        let (defintion, ty) = match result {
            Ok(result) => result,
            Err(_) => {
                return self.error_ty();
            }
        };

        self.check_struct_fields(ty, defintion, &literal.fields);

        return ty;
    }

    pub fn check_struct_path(
        &self,
        path: &taroc_hir::Path,
        id: NodeID,
    ) -> Result<(&'ctx VariantDefinition<'ctx>, Ty<'ctx>), ()> {
        let (res, ty) = self.resolve_struct_path(path, id);

        let def = match res {
            Resolution::Error => return Err(()),
            Resolution::Definition(_, DefinitionKind::Struct | DefinitionKind::TypeAlias)
            | Resolution::SelfTypeAlias(_)
            | Resolution::InterfaceSelfTypeParameter(_) => match ty.adt_def() {
                Some(adt_def) => {
                    let def = self
                        .gcx
                        .with_session_type_database(|db| db.structs[&adt_def.id]);
                    Some((
                        def.variant,
                        adt_def.id,
                        ty.get_adt_arguments().expect("arguments"),
                    ))
                }
                None => None,
            },
            Resolution::Definition(id, DefinitionKind::Variant) => match ty.adt_def() {
                Some(adt_def) => {
                    let def = self.gcx.with_session_type_database(|db| db.variants[&id]);

                    Some((def, adt_def.id, ty.get_adt_arguments().expect("arguments")))
                }
                None => None,
            },

            _ => {
                unreachable!()
            }
        };

        if let Some(def) = def {
            let (def, id, args) = def;
            let gcx = self.gcx;
            // Check Constraints on Struct
            self.gcx.canon_predicates_of(id).iter().for_each(|spanned| {
                let constraint = instantiate_constraint_with_args(gcx, spanned.value, args);
                let o = Obligation {
                    location: path.span,
                    goal: Goal::Constraint(constraint),
                };
                self.add_obligation(o);
            });
            return Ok((def, ty));
        } else {
            self.gcx.diagnostics.error(
                format!(
                    "expected struct or enum struct variant, found {}",
                    ty.format(self.gcx)
                ),
                path.span,
            );
            return Err(());
        }
    }

    fn resolve_struct_path(&self, path: &taroc_hir::Path, id: NodeID) -> (Resolution, Ty<'ctx>) {
        let partial_resolution = self.gcx.resolution(id);

        if let Some(res) = partial_resolution.full_resolution() {
            let ty = self
                .lowerer()
                .lower_resolved_path(id, path, &LoweringRequest::default());

            return (res, ty);
        }

        todo!();
    }

    fn check_struct_fields(
        &self,
        struct_ty: Ty<'ctx>,
        definition: &VariantDefinition<'ctx>,
        expressions: &[taroc_hir::ExpressionField],
    ) {
        let TyKind::Adt(_, args) = struct_ty.kind() else {
            unreachable!("ICE: non-ADT Type passed to check_struct_fields");
        };

        // field state
        let mut seen = FxHashMap::default();
        let mut remaining: FxHashMap<_, _> = definition
            .fields
            .iter_enumerated()
            .map(|(i, f)| return (f.name, (i, f)))
            .collect();
        for (_, expression) in expressions.iter().enumerate() {
            let name = expression.label.symbol;

            let field_ty = if let Some((_, field_def)) = remaining.remove(&name) {
                self.results
                    .borrow_mut()
                    .field_indices
                    .insert(expression.id, field_def.index);
                seen.insert(name, expression.label.span);
                let field_ty = instantiate_ty_with_args(self.gcx, field_def.ty, args);
                field_ty
            } else {
                if let Some(prev) = seen.get(&name) {
                    let m1 = format!("field {name} is provided multiple times");
                    let m2 = format!("{name} is initially specified here");

                    self.gcx.diagnostics.error(m1, expression.span);
                    self.gcx.diagnostics.info(m2, *prev);
                } else {
                    let msg = format!("unknown field named '{name}'");
                    self.gcx.diagnostics.error(msg, expression.label.span);
                }

                self.error_ty()
            };

            let expr_ty = self.check_expression_with_hint(&expression.expression, field_ty);
            self.add_coercion_constraint(
                expr_ty,
                field_ty,
                expression.expression.id,
                expression.span,
            );
        }
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_field_access_expression(
        &self,
        base: &taroc_hir::Expression,
        segment: &taroc_hir::PathSegment,
        expression: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let base_ty = self.check_expression(base);
        let result_var = self.next_ty_var(segment.span);

        let goal = FieldAccessGoal {
            base_ty,
            base_id: base.id,
            field: segment.identifier,
            result_var,
            field_span: segment.span,
            expr_id: expression.id,
        };

        self.add_obligation(Obligation {
            location: expression.span,
            goal: Goal::FieldAccess(goal),
        });

        result_var
    }

    fn check_tuple_access_expression(
        &self,
        base: &taroc_hir::Expression,
        index: &taroc_hir::AnonConst,
        expr: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let index_value = match &index.value.kind {
            taroc_hir::ExpressionKind::Literal(taroc_hir::Literal::Integer(i)) => *i as usize,
            _ => {
                self.gcx.diagnostics.error(
                    "tuple indices must be integer literals".into(),
                    index.value.span,
                );
                return self.error_ty();
            }
        };

        let base_ty = self.check_expression(base);
        let result_var = self.next_ty_var(index.value.span);

        let goal = TupleAccessGoal {
            base_ty,
            index: index_value,
            result_var,
            index_span: index.value.span,
        };

        self.add_obligation(Obligation {
            location: expr.span,
            goal: Goal::TupleAccess(goal),
        });

        result_var
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_method_call_expr(
        &self,
        node: &taroc_hir::MethodCall,
        expr: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let recv_ty = self.check_expression(&node.receiver);

        let beta: Vec<_> = node
            .arguments
            .iter()
            .map(|arg| OverloadArgument {
                ty: self.next_ty_var(arg.span),
                span: arg.span,
                label: arg.label.as_ref().map(|l| l.identifier),
                id: arg.expression.id,
            })
            .collect();
        let beta = self.gcx.store.interners.intern_slice(&beta);
        let rho = self.next_ty_var(expr.span);

        for (arg, b) in node.arguments.iter().zip(beta) {
            let arg_ty = self.check_expression(&arg.expression);
            self.add_obligation(Obligation {
                location: expr.span,
                goal: Goal::Constraint(Constraint::TypeEquality(arg_ty, b.ty)),
            });
        }

        if let Some(e_ty) = expectation.only_has_type() {
            self.add_obligation(Obligation {
                location: expr.span,
                goal: Goal::Coerce {
                    from: rho,
                    to: e_ty,
                    node: expr.id,
                },
            });
        }

        let goal = MethodCallGoal {
            call_span: expr.span,
            call_expr_id: expr.id,
            reciever_id: node.receiver.id,
            method: node.method.identifier,
            receiver_ty: recv_ty,
            result_var: rho,
            expected_result_ty: expectation.only_has_type(),
            arguments: beta,
            label_agnostic: false,
        };

        self.add_obligation(Obligation {
            location: expr.span,
            goal: Goal::MethodCall(goal),
        });

        rho
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_unary_expression(
        &self,
        op: UnaryOperator,
        rhs: &taroc_hir::Expression,
        expr: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let operand_ty = self.check_expression(rhs);
        let result_var = self.next_ty_var(expr.span);

        let goal = UnaryOperatorGoal {
            operand_ty,
            result_var,
            operator: op,
            span: expr.span,
            expectation: expectation.only_has_type(),
            node_id: expr.id,
            rhs_id: rhs.id,
        };

        self.add_obligation(Obligation {
            location: expr.span,
            goal: Goal::UnaryOperator(goal),
        });

        result_var
    }

    fn check_binary_expression(
        &self,
        op: BinaryOperator,
        lhs: &taroc_hir::Expression,
        rhs: &taroc_hir::Expression,
        expr: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let goal = BinaryOperatorGoal {
            operator: op,
            span: expr.span,
            node_id: expr.id,
            expectation: expectation.only_has_type(),
            lhs: self.check_expression(lhs),
            rhs: self.check_expression(rhs),
            rho: self.next_ty_var(expr.span),
            assigning: false,
            lhs_id: lhs.id,
            rhs_id: rhs.id,
        };

        self.add_obligation(Obligation {
            location: expr.span,
            goal: Goal::BinaryOperator(goal),
        });

        goal.rho
    }

    fn check_assign_op_expression(
        &self,
        op: BinaryOperator,
        lhs: &taroc_hir::Expression,
        rhs: &taroc_hir::Expression,
        expr: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let goal = BinaryOperatorGoal {
            operator: op,
            span: expr.span,
            node_id: expr.id,
            expectation: None,
            lhs: self.check_expression(lhs),
            rhs: self.check_expression(rhs),
            rho: self.common_types().void,
            assigning: true,
            lhs_id: lhs.id,
            rhs_id: rhs.id,
        };

        self.add_obligation(Obligation {
            location: expr.span,
            goal: Goal::BinaryOperator(goal),
        });

        self.common_types().void
    }

    fn check_subscript_expression(
        &self,
        target: &taroc_hir::Expression,
        arguments: &[taroc_hir::ExpressionArgument],
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let lhs = self.check_expression(target);
        let beta: Vec<_> = arguments
            .iter()
            .map(|arg| OverloadArgument {
                ty: self.check_expression(&arg.expression),
                span: arg.span,
                label: arg.label.as_ref().map(|l| l.identifier),
                id: arg.expression.id,
            })
            .collect();
        let rho = self.next_ty_var(expression.span);
        let goal = OverloadGoal {
            expr_span: expression.span,
            expr_id: expression.id,
            callee_id: target.id,
            callee_span: target.span,
            callee_var: lhs,
            result_var: rho,
            expected_result_ty: expectation.only_has_type(),
            arguments: self.gcx.store.interners.intern_slice(&beta),
        };

        self.add_obligation(Obligation {
            location: expression.span,
            goal: Goal::IndexOperator(goal),
        });

        rho
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_cast_expression(
        &self,
        target: &taroc_hir::Expression,
        ast_ty: &taroc_hir::Type,
        expression: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let from_ty = self.check_expression(target);
        let to_ty = self.lower_ty(ast_ty);

        let goal = CastGoal {
            span: expression.span,
            from_ty,
            to_ty,
            optional: false,
        };

        let obligation = Obligation {
            location: goal.span,
            goal: Goal::Cast(goal),
        };

        self.add_obligation(obligation);
        return to_ty;
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_match_expression(&self, node: &taroc_hir::MatchExpression, span: Span) -> Ty<'ctx> {
        let alpha = self.check_expression(&node.value); // type of scrutinee
        let rho = self.next_ty_var(span); // result type of match block

        // Patterns
        for arm in node.arms.iter() {
            // instantiate types for each local variable
            GatherLocalsVisitor::from_match_arm(self, &arm.pattern);
            self.add_shape_obligation(&arm.pattern, alpha);
        }

        // Expressions
        for arm in node.arms.iter() {
            if let Some(guard) = &arm.guard {
                let guard_ty = self.check_expression(&guard);
                self.add_coercion_constraint(
                    guard_ty,
                    self.common_types().bool,
                    guard.id,
                    guard.span,
                );
            }

            let arm_ty = self.check_expression(&arm.body);
            self.add_coercion_constraint(arm_ty, rho, arm.body.id, arm.body.span);
        }

        rho
    }
}
