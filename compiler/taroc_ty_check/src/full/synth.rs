use taroc_hir::{BinaryOperator, DefinitionID, Mutability, NodeID, OperatorKind, UnaryOperator};
use taroc_span::{Span, Symbol};
use taroc_ty::{Adjustment, Constraint, GenericArgument, Ty, TyKind};

use crate::{full::FunctionChecker, lower, utils};

impl<'ctx> FunctionChecker<'ctx> {
    pub fn synthesize_statement(&mut self, statement: &taroc_hir::Statement) -> Ty<'ctx> {
        match &statement.kind {
            taroc_hir::StatementKind::Declaration(..) => {}
            taroc_hir::StatementKind::Expression(expression) => {
                return self.synthesize_expression(expression, None);
            }
            taroc_hir::StatementKind::Variable(local) => {
                self.check_local(local);
            }
            taroc_hir::StatementKind::Return(expression) => {
                if let Some(expression) = expression {
                    self.synthesize_expression(expression, None);
                }
            }
            //
            taroc_hir::StatementKind::Loop(..) => {}
            taroc_hir::StatementKind::Defer(..) => {}
            //
            taroc_hir::StatementKind::Break(..) => {}
            taroc_hir::StatementKind::Continue(..) => {}
        }

        return self.context.store.common_types.void;
    }
    pub fn synthesize_expression(
        &mut self,
        expression: &taroc_hir::Expression,
        expectation: Option<Ty<'ctx>>,
    ) -> Ty<'ctx> {
        match &expression.kind {
            taroc_hir::ExpressionKind::Malformed => {
                unreachable!("ICE: malformed expression, should be caught in earlier passes")
            }
            taroc_hir::ExpressionKind::Path(path) => self.synthesize_path_expression(path, None),
            taroc_hir::ExpressionKind::Tuple(expressions) => {
                self.synthesize_tuple_expression(expressions)
            }
            taroc_hir::ExpressionKind::Literal(literal) => {
                self.synthesize_literal_expression(literal)
            }
            taroc_hir::ExpressionKind::Assign(lhs, rhs) => {
                self.synthesize_assign_expression(lhs, rhs)
            }
            taroc_hir::ExpressionKind::FunctionCall(expression, arguments) => {
                self.synthesize_function_call_expression(expression, arguments, expectation)
            }
            taroc_hir::ExpressionKind::Block(block) => self.synthesize_block_expression(block),
            taroc_hir::ExpressionKind::If(node) => self.synthesize_if_expression(node),
            taroc_hir::ExpressionKind::Array(exprs) => self.synthesize_array_expression(exprs),
            taroc_hir::ExpressionKind::TupleAccess(expr, index) => {
                self.synthesize_tuple_access_expression(expr, index)
            }
            taroc_hir::ExpressionKind::Unary(op, expr) => {
                self.synthesize_unary_expression(expr, *op, expectation)
            }
            taroc_hir::ExpressionKind::Binary(op, lhs, rhs) => {
                self.synthesize_binary_expression(lhs, rhs, *op, expectation, expression.span)
            }
            taroc_hir::ExpressionKind::AssignOp(op, lhs, rhs) => {
                self.synthesize_binary_assign_expression(lhs, rhs, *op, expression.span)
            }
            taroc_hir::ExpressionKind::MethodCall(node) => {
                self.synthesize_method_call_expression(node, expectation, expression.span)
            }
            taroc_hir::ExpressionKind::FieldAccess(expr, segment) => {
                self.synthesize_field_access_expression(expr, segment)
            }
            taroc_hir::ExpressionKind::Subscript(..) => todo!("subscript"),
            taroc_hir::ExpressionKind::CastAs(..) => todo!("cast expression"),
            taroc_hir::ExpressionKind::MatchBinding(..) => todo!("match binding expression"),

            // TODO: Later
            taroc_hir::ExpressionKind::Closure(..) => todo!("closure expression"),
            taroc_hir::ExpressionKind::InferMemberPath(..) => todo!("inferred path"),
            taroc_hir::ExpressionKind::Await(..) => todo!("await expressions"),
        }
    }

    fn synthesize_tuple_expression(
        &mut self,
        elements: &Vec<Box<taroc_hir::Expression>>,
    ) -> Ty<'ctx> {
        let mut element_types = Vec::with_capacity(elements.len());

        for element in elements {
            let elem_ty = self.synthesize_expression(element, None);
            element_types.push(elem_ty);
        }

        let tys = self.context.store.interners.intern_ty_list(&element_types);
        let ty = self.context.store.interners.intern_ty(TyKind::Tuple(tys));
        ty
    }

    fn synthesize_path_expression(
        &mut self,
        path: &taroc_hir::Path,
        expectation: Option<Ty<'ctx>>,
    ) -> Ty<'ctx> {
        let id = path.segments.last().unwrap().id;
        let resolution = self.context.resolution(id);

        match resolution {
            taroc_hir::Resolution::FunctionSet(candidates) => {
                // 1. If we're in a *check* position against a fn‐type, pick the overload now
                if let Some(_exp_ty @ TyKind::Function { .. }) = expectation.map(|e| e.kind()) {
                    todo!("checking again function ty, pick overoad now")
                } else {
                    let candidates: Vec<_> = candidates.iter().cloned().collect();
                    let kind = TyKind::OverloadedFn(
                        self.context.store.interners.intern_slice(&candidates),
                        None, // TODO!
                    );
                    return self.mk_ty(kind);
                }
            }

            taroc_hir::Resolution::Definition(_, taroc_hir::DefinitionKind::Variant) => {
                self.context
                    .diagnostics
                    .warn("variant here".into(), path.span);
                todo!("enum variant")
            }

            taroc_hir::Resolution::Definition(id, taroc_hir::DefinitionKind::Struct) => {
                return self.resolve_constructor(id);
            }

            _ => return lower::synthesize_path(path, &mut self.context),
        }
    }

    fn synthesize_literal_expression(&mut self, literal: &taroc_hir::Literal) -> Ty<'ctx> {
        match literal {
            taroc_hir::Literal::Bool(_) => self.context.store.common_types.bool,
            taroc_hir::Literal::Rune(_) => self.context.store.common_types.rune,
            taroc_hir::Literal::Void => self.context.store.common_types.void,
            taroc_hir::Literal::Integer(_) => self.context.fresh_int_var(),
            taroc_hir::Literal::Float(_) => self.context.fresh_float_var(),
            taroc_hir::Literal::Nil => self.context.fresh_nil_var(),
            taroc_hir::Literal::String(_) => self.string_type(), // TODO: Adjustment?
        }
    }

    fn synthesize_assign_expression(
        &mut self,
        lhs: &taroc_hir::Expression,
        rhs: &taroc_hir::Expression,
    ) -> Ty<'ctx> {
        let lhs_ty = self.synthesize_expression(lhs, None);
        let rhs_ty = self.synthesize_expression(rhs, None);

        // TODO: Mutability?
        // Constraint
        let constraint = Constraint::TypeEquality(rhs_ty, lhs_ty);
        self.context.add_constraint(constraint, rhs.id, rhs.span);
        self.context.store.common_types.void
    }

    fn synthesize_function_call_expression(
        &mut self,
        target: &taroc_hir::Expression,
        arguments: &Vec<taroc_hir::ExpressionArgument>,
        expectation: Option<Ty<'ctx>>,
    ) -> Ty<'ctx> {
        // Get Type of Target
        let callee = self.synthesize_expression(target, expectation);
        let callee = self.instantiate(callee);

        // Overload Candidates
        let callee = match callee.kind() {
            TyKind::OverloadedFn(candidates, _) => {
                let mut schemes = vec![];
                candidates.into_iter().for_each(|id| {
                    let signature = self.context.fn_signature(*id);
                    schemes.push(signature);
                });

                let ty = self.resolve_overloads(
                    &schemes,
                    Some(arguments),
                    expectation,
                    target.span,
                    true,
                );
                ty
            }
            _ => callee,
        };

        println!("Trying to call: {callee}");

        // Check Callable
        let (param_tys, ret_ty) = self.expect_callable(callee, arguments.len(), target.span);
        println!("Resolved to call: {param_tys:?} -> {ret_ty}");

        // Unify Each Argument
        for (argument, &parameter_ty) in arguments.iter().zip(param_tys) {
            let argument_ty = self.synthesize_expression(&argument.expression, None);
            let result = self.coerce_or_unify(parameter_ty, argument_ty);

            match result {
                Ok(adjusments) => {
                    self.context
                        .add_adjustments(adjusments, argument.expression.id);
                }
                Err(_) => {
                    let message =
                        format!("type mismatch. expected {parameter_ty}, found {argument_ty}");
                    self.context
                        .diagnostics
                        .error(message, argument.expression.span);
                }
            }
        }

        return ret_ty;
    }

    fn synthesize_block_expression(&mut self, block: &taroc_hir::Block) -> Ty<'ctx> {
        for (index, statement) in block.statements.iter().enumerate() {
            let ty = self.synthesize_statement(statement);

            if index == block.statements.len() - 1 {
                return ty;
            }
        }

        return self.context.store.common_types.void;
    }

    fn synthesize_if_expression(&mut self, node: &taroc_hir::IfExpression) -> Ty<'ctx> {
        // Condition
        let condition = self.synthesize_expression(&node.condition, None);
        let constraint = Constraint::TypeEquality(condition, self.context.store.common_types.bool);
        self.context
            .add_constraint(constraint, node.condition.id, node.condition.span);

        // Then
        let then_ty = self.synthesize_block_expression(&node.then_block);

        // Else
        if let Some(else_block) = &node.else_block {
            let else_ty = self.synthesize_expression(else_block, None);
            let constraint = Constraint::TypeEquality(else_ty, then_ty);
            self.context
                .add_constraint(constraint, else_block.id, else_block.span);
        };

        then_ty
    }

    fn synthesize_array_expression(
        &mut self,
        expressions: &Vec<Box<taroc_hir::Expression>>,
    ) -> Ty<'ctx> {
        let element_ty = self.context.fresh_ty_var();

        for expression in expressions {
            let element = self.synthesize_expression(expression, None);
            let result = self.coerce_or_unify(element_ty, element);

            match result {
                Ok(adjustments) => {
                    self.context.add_adjustments(adjustments, expression.id);
                }
                Err(_) => {
                    self.context
                        .diagnostics
                        .error("TODO: report parameter err".into(), expression.span);
                }
            }
        }

        let array_id = {
            let store = self.context.store.common_types.mappings.foundation.borrow();
            let array_id = store
                .get(&Symbol::with("List"))
                .cloned()
                .expect("Dynamic Array Type");
            array_id
        };

        let list_ty = self.context.type_of(array_id);
        let args = vec![GenericArgument::Type(element_ty)];
        let args = self.context.store.interners.intern_generic_args(&args);
        let subst = utils::create_substitution_map(array_id, args, *self.context);
        let ty = utils::substitute(list_ty, &subst, None, *self.context);

        ty
    }

    fn synthesize_tuple_access_expression(
        &mut self,
        expression: &taroc_hir::Expression,
        index_expression: &taroc_hir::AnonConst,
    ) -> Ty<'ctx> {
        let index = match &index_expression.value.kind {
            taroc_hir::ExpressionKind::Literal(taroc_hir::Literal::Integer(index)) => {
                *index as usize
            }
            _ => unreachable!("ICE: tuple index should be validated as an integer"),
        };

        let ty = self.synthesize_expression(expression, None);

        let elements = match ty.kind() {
            TyKind::Tuple(elements) => elements,
            _ => {
                let message = format!("{ty} is not a tuple type.");
                self.context.diagnostics.error(message, expression.span);
                return self.error_ty();
            }
        };

        if index >= elements.len() {
            self.context.diagnostics.error(
                format!(
                    "tuple index {index} is out of bounds (tuple has {} elements)",
                    elements.len()
                ),
                index_expression.value.span,
            );
            return self.error_ty();
        }

        // ───── 4. return the element type ─────
        elements[index]
    }

    fn synthesize_unary_expression(
        &mut self,
        expression: &taroc_hir::Expression,
        operator: UnaryOperator,
        expectation: Option<Ty<'ctx>>,
    ) -> Ty<'ctx> {
        let operand_ty = self.synthesize_expression(expression, None);
        let operand_type_id = self.context.ty_to_def(operand_ty);

        let op = match operator {
            UnaryOperator::Dereference => match operand_ty.kind() {
                TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => return inner,
                _ => {
                    let message = format!("cannot dereference non-pointer type {operand_ty}");
                    self.context.diagnostics.error(message, expression.span);
                    return self.error_ty();
                }
            },
            UnaryOperator::Reference(mutbl) => {
                let mutbl = if mutbl {
                    Mutability::Mutable
                } else {
                    Mutability::Immutable
                };
                return self.mk_ty(TyKind::Reference(operand_ty, mutbl));
            }
            UnaryOperator::Negate => OperatorKind::Neg,
            UnaryOperator::BitwiseNot => OperatorKind::BitwiseNot,
            UnaryOperator::LogicalNot => OperatorKind::Not,
        };

        // return self.resolve_operator_overload(
        //     operand_type_id,
        //     op,
        //     &[operand_ty],
        //     expectation,
        //     expression.span,
        // );
        return self.error_ty();
    }

    fn synthesize_binary_expression(
        &mut self,
        lhs: &taroc_hir::Expression,
        rhs: &taroc_hir::Expression,
        operator: BinaryOperator,
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        let lhs = self.synthesize_expression(lhs, None);
        let lhs_type_id = self.context.ty_to_def(lhs);

        let rhs = self.synthesize_expression(rhs, None);
        let operand = OperatorKind::from_binary(operator);

        // return self.resolve_operator_overload(
        //     lhs_type_id,
        //     operand,
        //     &[lhs, rhs],
        //     expectation,
        //     span,
        // );
        return self.error_ty();
    }

    fn synthesize_binary_assign_expression(
        &mut self,
        lhs: &taroc_hir::Expression,
        rhs: &taroc_hir::Expression,
        operator: BinaryOperator,
        span: Span,
    ) -> Ty<'ctx> {
        let lhs_id = lhs.id;
        let lhs = self.synthesize_expression(lhs, None);
        let lhs_type_id = self.context.ty_to_def(lhs);
        let lhs = self.mk_ty(TyKind::Reference(lhs, Mutability::Mutable)); // Auto Ref lhs
        let adjustment = Adjustment::AutoMutRef;
        self.context.add_adjustments(vec![adjustment], lhs_id);

        let rhs = self.synthesize_expression(rhs, None);
        let operand = OperatorKind::assign_from_binary(operator).expect("operator");
        // let ty = self.resolve_operator_overload(
        //     lhs_type_id,
        //     operand,
        //     &[lhs, rhs],
        //     Some(self.void_ty()),
        //     span,
        // );
        // TODO
        return self.error_ty();
    }

    fn synthesize_method_call_expression(
        &mut self,
        node: &taroc_hir::MethodCall,
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        // 1. Synthesize the receiver's type
        let receiver_ty = self.synthesize_expression(&node.receiver, None);

        // 2. Synthesize explicit argument types
        let explicit_arg_tys: Vec<Ty<'ctx>> = node
            .arguments
            .iter()
            .map(|arg| self.synthesize_expression(&arg.expression, None))
            .collect();

        // 3. Get the DefinitionID of the receiver type, if possible
        let receiver_def_id = self.context.ty_to_def(receiver_ty); // Assuming this helper exists/can be made

        match receiver_def_id {
            Some(id) => {
                // 4. Resolve using the DefinitionID
                self.resolve_known_method_call(
                    node.receiver.id,
                    id,
                    receiver_ty,
                    &node.method,
                    &explicit_arg_tys,
                    expectation,
                    span,
                )
            }
            None => {
                // Handle cases where the receiver type isn't a simple definition
                // (e.g., inference variable, tuple, function pointer), existential
                self.context.diagnostics.error(
                    format!("cannot call method on unresolved type '{}'", receiver_ty),
                    span,
                );
                self.error_ty()
                // todo!("method call on complex ty or via trait extension")
            }
        }
    }

    fn synthesize_field_access_expression(
        &mut self,
        receiver: &taroc_hir::Expression,
        segment: &taroc_hir::PathSegment,
    ) -> Ty<'ctx> {
        debug_assert!(
            segment.arguments.is_none(),
            "ICE: field access segment must not have arguments"
        );

        let initial_receiver_ty = self.synthesize_expression(receiver, None);

        let mut current_receiver_ty = initial_receiver_ty;
        let mut deref_adjustments: Vec<Adjustment> = Vec::new();
        let max_derefs = 10;

        for _ in 0..max_derefs {
            // Try to resolve field access on the current receiver type
            if let Some(target_def_id) = self.context.ty_to_def(current_receiver_ty) {
                // Try resolving *only struct fields* on this specific DefinitionID
                let resolve_result = self.resolve_known_struct_field(
                    target_def_id,
                    current_receiver_ty, // Pass the potentially dereferenced type
                    segment,
                    receiver.span, // Pass overall span for errors
                );

                match resolve_result {
                    Ok(field_ty) => {
                        // Success! Field found.
                        // Store the deref adjustments found so far.
                        if !deref_adjustments.is_empty() {
                            self.context.add_adjustments(deref_adjustments, receiver.id);
                        }
                        return field_ty; // Return the final instantiated field type
                    }
                    Err(_) => {
                        // Field not found on this type definition.
                        // Proceed to check for Deref below.
                    }
                }
            } else {
                // Not a type with a DefinitionID, cannot have struct fields.
                break;
            }

            // --- Field not found on current type, attempt Auto-Deref ---
            if let Some(deref_target_ty) = self.deref_target(current_receiver_ty) {
                deref_adjustments.push(Adjustment::AutoDeref);
                current_receiver_ty = deref_target_ty;
                // Continue loop
            } else {
                // Cannot dereference further.
                break; // Exit loop
            }
        } // End of auto-deref loop

        // --- If loop finished without finding the field ---
        let field_name = segment.identifier.symbol;
        let message = format!(
            "no field '{}' found for type '{}'",
            field_name, initial_receiver_ty
        );

        self.context
            .diagnostics
            .error(message, segment.identifier.span);
        return self.error_ty();
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    pub fn synthesize_call_arguments(
        &mut self,
        callsite_args: &[taroc_hir::ExpressionArgument],
    ) -> Vec<(Ty<'ctx>, NodeID)> {
        // Return tuple of Type and NodeID
        callsite_args
            .iter()
            .map(|arg| {
                let ty = self.synthesize_expression(&arg.expression, None);
                (ty, arg.expression.id) // Get NodeID from expression Box<Expression>
            })
            .collect()
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    /// Resolves field access *specifically for struct data fields*.
    /// Returns Ok(InstantiatedFieldType) on success,
    /// or Err(()) if the target is not a struct or the field name is not found.
    fn resolve_known_struct_field(
        &mut self,
        target_def_id: DefinitionID, // The DefinitionID of the type (after deref)
        target_concrete_ty: Ty<'ctx>, // The specific type instance (after deref)
        field_segment: &taroc_hir::PathSegment,
        span: Span, // Overall expression span for some errors
    ) -> Result<Ty<'ctx>, ()> {
        // Return Result<Type, ErrorSignal>
        let kind = self.context.def_kind(target_def_id);
        let name = field_segment.identifier.symbol;

        // --- Ensure the target type is actually a struct ---
        if !matches!(kind, taroc_hir::DefinitionKind::Struct) {
            // This type (after deref) is not a struct, so it cannot have the field.
            // Signal failure to the caller loop.
            return Err(());
        }

        // --- Look up the field definition in the struct ---
        let field_ty_opt = self
            .context
            .with_type_database(target_def_id.package(), |db| {
                db.structs
                    .get(&target_def_id)
                    .and_then(|definition| definition.fields.get(&name))
                    .map(|field_info| field_info.ty) // Get Option<Ty>
            });

        let Some(field_ty) = field_ty_opt else {
            // Struct exists, but doesn't have this field name. Signal failure.
            return Err(());
        };

        // --- Instantiate the field type if necessary ---
        if !field_ty.needs_instantiation() {
            // Field type is simple (e.g., i32), no instantiation needed.
            return Ok(field_ty);
        }

        // Field type has generic parameters (e.g., T), need to substitute.
        let parent_args = match target_concrete_ty.get_adt_arguments(target_def_id) {
            Some(args) => args,
            None => {
                // Arguments are needed for instantiation but couldn't be retrieved.
                let type_name = self.context.def_symbol(target_def_id);
                self.context.diagnostics.error(
                    format!("internal: cannot get generic arguments from receiver type '{}' (expected struct '{}') to instantiate field '{}'", target_concrete_ty, type_name, name),
                    span // Use overall expression span
                );
                return Err(()); // Signal failure
            }
        };

        // Create the substitution map
        let subst_map = utils::create_substitution_map(target_def_id, parent_args, *self.context);

        // Substitute into the field's generic type
        let instantiated_ty = utils::substitute(field_ty, &subst_map, None, *self.context);

        Ok(instantiated_ty)
    }
}

impl<'ctx> FunctionChecker<'ctx> {}
