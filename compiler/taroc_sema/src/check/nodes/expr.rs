use taroc_hir::Resolution;

use crate::{
    CommonTypes,
    check::{context::func::FnCtx, expectation::Expectation},
    ty::{Ty, TyKind},
};

type CallerInfo<'a> = (
    &'a taroc_hir::Expression,
    &'a [taroc_hir::ExpressionArgument],
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
        let mut ty =
            self.check_expression_with_expectation(expression, Expectation::HasType(expectation));
        ty
    }

    pub fn check_expression_coercible_to_type(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Ty<'ctx>,
        node: Option<&taroc_hir::Expression>,
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
        caller_info: Option<CallerInfo>,
    ) -> Ty<'ctx> {
        let ty = self.check_expression_kind(expression, expectation);
        // println!("Resulting Ty: {}", ty2str(ty, self.gcx));
        ty
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_expression_kind(
        &self,
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        match &expression.kind {
            taroc_hir::ExpressionKind::Literal(literal) => {
                self.check_literal_expression(literal, expectation)
            }
            taroc_hir::ExpressionKind::Path(path) => {
                self.check_path_expression(path, expression, None)
            }
            taroc_hir::ExpressionKind::StructLiteral(..) => self.commons().error,
            taroc_hir::ExpressionKind::ArrayLiteral(..) => self.commons().error,
            taroc_hir::ExpressionKind::Tuple(expressions) => {
                self.check_tuple_expression(&expressions, expectation, expression)
            }
            taroc_hir::ExpressionKind::If(node) => {
                self.check_if_expression(node, expression, expectation)
            }
            taroc_hir::ExpressionKind::FunctionCall(..) => self.commons().error,
            taroc_hir::ExpressionKind::MethodCall(..) => self.commons().error,
            taroc_hir::ExpressionKind::Binary(..) => self.commons().error,
            taroc_hir::ExpressionKind::Unary(..) => self.commons().error,
            taroc_hir::ExpressionKind::FieldAccess(..) => self.commons().error,
            taroc_hir::ExpressionKind::Subscript(..) => self.commons().error,
            taroc_hir::ExpressionKind::AssignOp(..) => self.commons().error,
            taroc_hir::ExpressionKind::Assign(..) => self.commons().error,
            taroc_hir::ExpressionKind::CastAs(..) => self.commons().error,
            taroc_hir::ExpressionKind::MatchBinding(_) => self.commons().error,

            taroc_hir::ExpressionKind::TupleAccess(..) => self.commons().error,
            taroc_hir::ExpressionKind::When(..) => self.commons().error,
            taroc_hir::ExpressionKind::Closure(_) => self.commons().error,
            taroc_hir::ExpressionKind::Block(block) => {
                self.check_block_expression(block, expectation)
            }
            taroc_hir::ExpressionKind::Await(expression) => {
                self.check_expression_with_expectation(expression, expectation)
            }
            taroc_hir::ExpressionKind::Malformed => {
                unreachable!("ICE: trying to tycheck a malformed expression node")
            }
        }
    }
}
impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn commons(&self) -> &CommonTypes<'ctx> {
        &self.gcx.store.common_types
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_literal_expression(
        &self,
        literal: &taroc_hir::Literal,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        match literal {
            taroc_hir::Literal::Bool(_) => self.commons().bool,
            taroc_hir::Literal::Rune(_) => self.commons().rune,
            taroc_hir::Literal::String(_) => self.commons().string,
            taroc_hir::Literal::Integer(_) => {
                let opt_ty = expectation.to_option(self).and_then(|ty| match ty.kind() {
                    TyKind::Int(_) | TyKind::UInt(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| self.next_int_var())
            }
            taroc_hir::Literal::Float(_) => {
                let opt_ty = expectation.to_option(self).and_then(|ty| match ty.kind() {
                    TyKind::Float(_) => Some(ty),
                    _ => None,
                });

                opt_ty.unwrap_or_else(|| self.next_float_var())
            }
            taroc_hir::Literal::Nil => self.next_nil_var(),
        }
    }

    fn check_tuple_expression(
        &self,
        elements: &[Box<taroc_hir::Expression>],
        expectation: Expectation<'ctx>,
        _: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        // if we have an expected type that is a tuple, get it's elements to check against
        let expected_tys = expectation
            .only_has_type(self)
            .and_then(|ty| match ty.kind() {
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

        self.commons().void
    }

    fn check_if_expression(
        &self,
        node: &taroc_hir::IfExpression,
        expression: &taroc_hir::Expression,
        expectation: Expectation<'ctx>,
    ) -> Ty<'ctx> {
        // TODO: Coercions
        let _ = self.check_expression_has_type(&node.condition, self.commons().bool);

        let then_ty = self.check_expression_with_expectation(&node.then_block, expectation);
        if let Some(else_node) = &node.else_block {
            let else_ty = self.check_expression_with_expectation(else_node, expectation);
        }

        return then_ty;
    }
}

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    fn check_path_expression(
        &self,
        path: &taroc_hir::Path,
        expression: &taroc_hir::Expression,
        caller_info: Option<CallerInfo>,
    ) -> Ty<'ctx> {
        let resolution = self.perform_path_resolution(expression.id, path);

        let ty = match resolution {
            Resolution::Error => {
                // should be pre-reported atp
                self.commons().error
            }

            _ => self.resolve_type_of_path(path, resolution),
        };

        return ty;
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

        todo!("TODO: Partially resolved path")
    }

    fn resolve_type_of_path(
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

        todo!()
    }
}
