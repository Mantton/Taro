use crate::{
    CommonTypes,
    check::{context::func::FnCtx, expectation::Expectation},
    ty::{Ty, TyKind},
    utils::{instantiate_ty_with_args, labeled_signature_to_ty},
};
use taroc_hir::{DefinitionKind, Resolution};

type CallerInfo<'a, 'ctx> = (
    &'a taroc_hir::Expression,
    &'a [taroc_hir::ExpressionArgument],
    Option<Ty<'ctx>>, // expected return type of the call
);

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn check_expression(&self, expression: &taroc_hir::Expression) -> Ty<'ctx> {
        self.check_expression_with_expectation(expression, Expectation::None)
    }

    pub fn check_expression_with_expectation(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        self.check_expression_with_expectation_and_arguments(expression, expectation, None)
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
        self.demand_coercion(expression, ty, expectation)
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
        caller_info: Option<CallerInfo<'_, 'ctx>>,
    ) -> Ty<'ctx> {
        let ty = match &expression.kind {
            taroc_hir::ExpressionKind::Path(path) => {
                self.check_path_expression(path, expression, caller_info)
            }
            _ => self.check_expression_kind(expression, expectation),
        };

        self.gcx.diagnostics.warn(
            format!("Mapping To {}", ty.format(self.gcx)),
            expression.span,
        );

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
            taroc_hir::ExpressionKind::Path(path) => {
                self.check_path_expression(path, expression, None)
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
            taroc_hir::ExpressionKind::StructLiteral(..) => self.error_ty(),
            taroc_hir::ExpressionKind::ArrayLiteral(..) => self.error_ty(),
            taroc_hir::ExpressionKind::MethodCall(..) => self.error_ty(),
            taroc_hir::ExpressionKind::Binary(..) => self.error_ty(),
            taroc_hir::ExpressionKind::Unary(..) => self.error_ty(),
            taroc_hir::ExpressionKind::FieldAccess(..) => self.error_ty(),
            taroc_hir::ExpressionKind::Subscript(..) => self.error_ty(),
            taroc_hir::ExpressionKind::AssignOp(..) => self.error_ty(),
            taroc_hir::ExpressionKind::Assign(..) => self.error_ty(),
            taroc_hir::ExpressionKind::CastAs(..) => self.error_ty(),
            taroc_hir::ExpressionKind::MatchBinding(_) => self.error_ty(),
            taroc_hir::ExpressionKind::TupleAccess(..) => self.error_ty(),
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
                println!("check nil coercible");
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
    pub fn check_function_call_expression(
        &self,
        expression: &taroc_hir::Expression,
        calle: &taroc_hir::Expression,
        args: &[taroc_hir::ExpressionArgument],
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        let callee_ty = match &calle.kind {
            taroc_hir::ExpressionKind::Path(..) => self
                .check_expression_with_expectation_and_arguments(
                    calle,
                    Expectation::None,
                    Some((expression, args, expectation.only_has_type())),
                ),
            _ => self.check_expression(calle),
        };

        self.check_function_call_with_type(callee_ty, args, expectation, expression)
    }

    fn check_function_call_with_type(
        &self,
        callee_ty: Ty<'ctx>,
        args: &[taroc_hir::ExpressionArgument],
        _expectation: Expectation<'ctx>,
        call_expr: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let (fn_parameter_tys, fn_return_ty) = match callee_ty.kind() {
            TyKind::Function { inputs, output, .. } => (inputs, output),
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

                self.gcx
                    .diagnostics
                    .error("cannot call non-function type".into(), call_expr.span);
                return self.error_ty();
            }
        };

        // TODO: Parameters & Labels
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
        caller_info: Option<CallerInfo<'_, 'ctx>>,
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
                if let Some((call_expr, args, expected_return_ty)) = caller_info {
                    // Now we have the expected return type directly!
                    self.resolve_overloaded_function(
                        &candidates.iter().cloned().collect::<Vec<_>>(),
                        args,
                        expected_return_ty,
                        call_expr,
                        true,
                    )
                } else {
                    self.gcx.diagnostics.error(
                        "Cannot determine which overload to use without call context".into(),
                        path.span,
                    );
                    self.error_ty()
                }
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

        // Find all candidates
        self.gcx
            .diagnostics
            .warn("Resolve Assoc Item, Find candidates".into(), path.span);
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
