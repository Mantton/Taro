use crate::{
    CommonTypes,
    check::{
        context::func::FnCtx,
        expectation::Expectation,
        solver::{FieldAccessGoal, Goal, Obligation, OverloadArgument, OverloadGoal},
    },
    infer::fn_var::FnVarData,
    lower::{LoweringRequest, TypeLowerer},
    ty::{Constraint, InferTy, StructDefinition, Ty, TyKind},
    utils::{instantiate_constraint_with_args, instantiate_ty_with_args, labeled_signature_to_ty},
};
use rustc_hash::FxHashMap;
use taroc_hir::{DefinitionKind, NodeID, Resolution};
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
        self.add_coercion_constraint(ty, expectation, expression.span);
        expectation
    }

    pub fn add_coercion_constraint(&self, from: Ty<'ctx>, to: Ty<'ctx>, location: Span) {
        // break early
        if from == to {
            return;
        }

        let obligation = Obligation {
            location: location,
            goal: Goal::Coerce { from, to },
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
                self.check_tuple_access_expression()
            }
            taroc_hir::ExpressionKind::ArrayLiteral(..) => self.error_ty(),
            taroc_hir::ExpressionKind::MethodCall(..) => self.error_ty(),
            taroc_hir::ExpressionKind::Binary(..) => self.error_ty(),
            taroc_hir::ExpressionKind::Unary(..) => self.error_ty(),

            taroc_hir::ExpressionKind::Subscript(..) => self.error_ty(),
            taroc_hir::ExpressionKind::AssignOp(..) => self.error_ty(),
            taroc_hir::ExpressionKind::CastAs(..) => self.error_ty(),
            taroc_hir::ExpressionKind::MatchBinding(_) => self.error_ty(),
            taroc_hir::ExpressionKind::When(..) => self.error_ty(),
            taroc_hir::ExpressionKind::Closure(_) => self.error_ty(),
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
                // TODO: nil coercible
                return self.common_types().error;
            }
        }
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
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        // TODO: Coercions
        let _ = self.check_expression_has_type(&node.condition, self.common_types().bool);

        let then_ty = self.check_expression_with_expectation(&node.then_block, expectation);
        if let Some(else_node) = &node.else_block {
            let else_ty = self.check_expression_with_expectation(else_node, expectation);
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
        let (fn_parameter_tys, fn_return_ty) = match callee_ty.kind() {
            TyKind::Infer(InferTy::FnVar(_) | InferTy::TyVar(_)) => {
                let beta: Vec<_> = args
                    .iter()
                    .map(|arg| {
                        let argument = OverloadArgument {
                            ty: self.next_ty_var(arg.span),
                            span: arg.span,
                            label: arg.label.as_ref().map(|l| l.identifier),
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
                        },
                    });
                }

                let goal = OverloadGoal {
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
            TyKind::FnDef(id, _) => {
                let signature = self.gcx.fn_signature(id);
                let args = self.fresh_args_for_def(id, call_expr.span);
                let signature = labeled_signature_to_ty(signature, self.gcx);
                let signature = instantiate_ty_with_args(self.gcx, signature, args);

                match signature.kind() {
                    TyKind::Function { inputs, output, .. } => (inputs, output),
                    _ => {
                        self.gcx
                            .diagnostics
                            .error("invalid function signature".into(), call_expr.span);
                        return self.error_ty();
                    }
                }
            }

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

        // TODO: Parameters, Defaults, Variadics, Labels
        // check argument count
        if args.len() != fn_parameter_tys.len() {
            self.gcx.diagnostics.error(
                format!(
                    "Expected {} arguments, found {}",
                    fn_parameter_tys.len(),
                    args.len()
                )
                .into(),
                call_expr.span,
            );
            return self.error_ty();
        }

        fn_return_ty
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
            _ => self.instantiate_value_path(path, resolution),
        };

        ty
    }

    fn perform_path_resolution(
        &self,
        id: taroc_hir::NodeID,
        path: &taroc_hir::Path,
    ) -> taroc_hir::Resolution {
        let partial_res = self.gcx.resolution(id);

        if let Some(full) = partial_res.full_resolution() {
            return full;
        }

        todo!("partial res");
        return taroc_hir::Resolution::Error;
    }

    fn instantiate_value_path(
        &self,
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

        let def_id = resolution.def_id();
        let ty = self.gcx.type_of(def_id);
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

    fn check_struct_path(
        &self,
        path: &taroc_hir::Path,
        id: NodeID,
    ) -> Result<(&'ctx StructDefinition<'ctx>, Ty<'ctx>), ()> {
        let (res, ty) = self.resolve_struct_path(path, id);

        let def = match res {
            Resolution::Error => return Err(()),
            Resolution::Definition(_, DefinitionKind::Variant) => {
                todo!("enum variant")
            }
            Resolution::Definition(_, DefinitionKind::Struct | DefinitionKind::TypeAlias)
            | Resolution::SelfTypeAlias(_)
            | Resolution::InterfaceSelfTypeParameter(_) => match ty.adt_def() {
                Some(adt_def) => {
                    let def = self
                        .gcx
                        .with_session_type_database(|db| db.structs[&adt_def.id]);
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
        definition: &StructDefinition<'ctx>,
        expressions: &[taroc_hir::ExpressionField],
    ) {
        let TyKind::Adt(id, args) = struct_ty.kind() else {
            unreachable!("ICE: non-ADT Type passed to check_struct_fields");
        };

        // field state
        let mut seen = FxHashMap::default();
        let mut remaining: FxHashMap<_, _> = definition
            .fields
            .iter_enumerated()
            .map(|(i, f)| return (f.name, (i, f)))
            .collect();
        for (index, expression) in expressions.iter().enumerate() {
            let name = expression.label.symbol;

            let field_ty = if let Some((i, field_def)) = remaining.remove(&name) {
                // TODO: add field index note
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
            self.add_coercion_constraint(expr_ty, field_ty, expression.span);
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
            field: segment.identifier,
            result_var,
            field_span: segment.span,
        };

        self.add_obligation(Obligation {
            location: expression.span,
            goal: Goal::FieldAccess(goal),
        });

        result_var
    }

    fn check_tuple_access_expression(&self) -> Ty<'ctx> {
        return self.error_ty();
        todo!()
    }
}
