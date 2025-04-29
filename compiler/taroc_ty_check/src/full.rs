use crate::{
    lower,
    models::{InferenceContext, UnificationError},
    utils,
};
use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{BinaryOperator, DefinitionID, Mutability, NodeID, OperatorKind, UnaryOperator};
use taroc_span::{Span, Symbol};
use taroc_ty::{
    Adjustment, Coercion, Constraint, GenericArgs, GenericArgument, GenericParameter, InferTy,
    LabeledFunctionSignature, Ty, TyKind, TyVid,
};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    FullChecker::run(package, context)?;
    context.diagnostics.report()
}

struct FullChecker<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> FullChecker<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> FullChecker<'ctx> {
        FullChecker { context }
    }

    fn run(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let actor = FullChecker::new(context);
        actor.check_module(&package.root);
        context.diagnostics.report()
    }

    fn check_module(&self, module: &taroc_hir::Module) {
        for file in &module.files {
            self.check_file(file);
        }

        for module in &module.submodules {
            self.check_module(module);
        }
    }

    fn check_file(&self, file: &taroc_hir::File) {
        for declaration in &file.declarations {
            self.check_declaration(&declaration);
        }
    }

    fn check_declaration(&self, declaration: &taroc_hir::Declaration) {
        match &declaration.kind {
            taroc_hir::DeclarationKind::Function(node) => {
                self.check_function(node, declaration);
            }
            taroc_hir::DeclarationKind::Constructor(node, _) => {
                self.check_function(node, declaration);
            }
            taroc_hir::DeclarationKind::Operator(_, node) => {
                // self.check_function(node, declaration);
            }
            taroc_hir::DeclarationKind::Variable(..) => {}
            taroc_hir::DeclarationKind::Constant(..) => {}
            taroc_hir::DeclarationKind::Computed(..) => {}
            //
            taroc_hir::DeclarationKind::Namespace(node) => {
                self.check_declaration_list(&node.declarations);
            }
            taroc_hir::DeclarationKind::Extend(node) => {
                self.check_declaration_list(&node.declarations);
            }
            //
            taroc_hir::DeclarationKind::TypeAlias(..) => {}
            //
            taroc_hir::DeclarationKind::Import(..)
            | taroc_hir::DeclarationKind::Export(..)
            | taroc_hir::DeclarationKind::Bridge(..) => {}
            taroc_hir::DeclarationKind::EnumCase(..)
            | taroc_hir::DeclarationKind::AssociatedType(..)
            | taroc_hir::DeclarationKind::DefinedType(..) => {}
            taroc_hir::DeclarationKind::Extern(_) => {}
        }
    }

    fn check_declaration_list(&self, declarations: &Vec<taroc_hir::Declaration>) {
        for declaration in declarations {
            self.check_declaration(declaration);
        }
    }

    fn check_function(&self, function: &taroc_hir::Function, declaration: &taroc_hir::Declaration) {
        let name = declaration.identifier.symbol;
        let def_id = self.context.def_id(declaration.id);
        println!("Checking {name}\n----------------------");
        let checker = FunctionChecker::new(self.context);
        checker.check_function(function, def_id);
        println!()
    }
}

struct FunctionChecker<'ctx> {
    context: InferenceContext<'ctx>,
}

impl<'ctx> FunctionChecker<'ctx> {
    fn new(global: GlobalContext<'ctx>) -> FunctionChecker<'ctx> {
        FunctionChecker {
            context: InferenceContext::new(global),
        }
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn check_function(mut self, function: &taroc_hir::Function, def_id: DefinitionID) {
        // Signature
        let signature = self.context.fn_signature(def_id);
        let signature = utils::convert_labeled_signature_to_signature(&signature, *self.context);
        let signature = self.instantiate(signature);

        let (param_tys, return_ty) = match signature.kind() {
            TyKind::Function { inputs, output, .. } => (inputs, output),
            _ => unreachable!("function signature must be of function pointer type"),
        };

        for (parameter, &parameter_ty) in function.signature.prototype.inputs.iter().zip(param_tys)
        {
            self.context.env.insert(parameter.id, parameter_ty);
        }

        // Block
        //
        let Some(block) = &function.block else { return };
        self.check_function_body(block, return_ty);

        // Constraints
        self.solve_constraints();

        // TODO: Default Unbound Intvar
    }

    fn check_function_body(&mut self, block: &taroc_hir::Block, return_ty: Ty<'ctx>) {
        if let Some(expr) = Self::is_expression_bodied(block) {
            // ---- single-expression body ---------------------------------------
            self.check_expression(expr, return_ty);
        } else {
            // ---- regular block body ------------------------------------------
            for statement in &block.statements {
                self.check_statement(statement, return_ty);
            }
        }
    }

    fn is_expression_bodied(block: &taroc_hir::Block) -> Option<&taroc_hir::Expression> {
        match block.statements.as_slice() {
            [
                taroc_hir::Statement {
                    kind: taroc_hir::StatementKind::Expression(expr),
                    ..
                },
            ] => {
                Some(expr) // exactly one expression stmt → expr-bodied
            }
            _ => None, // otherwise treat as regular block
        }
    }

    fn check_statement(&mut self, statement: &taroc_hir::Statement, return_ty: Ty<'ctx>) {
        match &statement.kind {
            taroc_hir::StatementKind::Declaration(..) => {}
            taroc_hir::StatementKind::Expression(expression) => {
                self.synthesize_expression(expression, None);
            }
            taroc_hir::StatementKind::Variable(local) => {
                self.check_local(local);
            }
            taroc_hir::StatementKind::Return(expression) => {
                let ty = if let Some(expression) = expression {
                    self.synthesize_expression(expression, Some(return_ty))
                } else {
                    self.context.store.common_types.void
                };

                let constraint = Constraint::TypeEquality(ty, return_ty);
                self.context.add_constraint(
                    constraint,
                    expression
                        .as_ref()
                        .map(|p| p.span)
                        .unwrap_or(statement.span),
                );
            }

            //
            taroc_hir::StatementKind::Loop(..) => {}
            taroc_hir::StatementKind::Defer(..) => {}
            //
            taroc_hir::StatementKind::Break(..) => {}
            taroc_hir::StatementKind::Continue(..) => {}
        }
    }

    fn check_local(&mut self, local: &taroc_hir::Local) {
        let ty = if let Some(initializer) = &local.initializer {
            if let Some(annotation) = &local.ty {
                let annotation = lower::lower_type(annotation, &mut self.context);
                self.check_expression(initializer, annotation);
                annotation
            } else {
                let provided = self.synthesize_expression(initializer, None);
                provided
            }
        } else if let Some(annotation) = &local.ty {
            let annotation = lower::lower_type(annotation, &mut self.context);
            annotation
        } else {
            unreachable!("ICE: cannot infer local variable without type annotation or initializer")
        };

        self.bind_pattern(&local.pattern, ty);
    }

    fn bind_pattern(&mut self, pattern: &taroc_hir::BindingPattern, ty: Ty<'ctx>) {
        match &pattern.kind {
            taroc_hir::BindingPatternKind::Wildcard => {}
            taroc_hir::BindingPatternKind::Identifier(ident) => {
                let id = pattern.id;
                self.context.env.insert(id, ty);
                println!("Bound {} to {}", ident.symbol, ty)
            }
            taroc_hir::BindingPatternKind::Tuple(patterns) => {
                // Only tuple types can be destructured
                if let TyKind::Tuple(elements) = ty.kind() {
                    // Arity mismatch
                    if elements.len() != patterns.len() {
                        let message = format!(
                            "mismatched tuple length: expected `{}`, found `{}`",
                            elements.len(),
                            patterns.len()
                        );
                        self.context.diagnostics.error(message, pattern.span);
                    } else {
                        // Recurse into each sub-pattern
                        for (pattern, &ty) in patterns.iter().zip(elements.iter()) {
                            self.bind_pattern(pattern, ty);
                        }
                    }
                } else {
                    // Cannot destruct non-tuple
                    let message = format!("cannot destructure non-tuple type `{}`", ty);
                    self.context.diagnostics.error(message, pattern.span);
                }
            }
        }
    }
}
impl<'ctx> FunctionChecker<'ctx> {
    fn check_expression(&mut self, expression: &taroc_hir::Expression, expected: Ty<'ctx>) {
        let actual = self.synthesize_expression(expression, Some(expected));
        let constraint = Constraint::TypeEquality(actual, expected);
        self.context.add_constraint(constraint, expression.span);
    }
}
impl<'ctx> FunctionChecker<'ctx> {
    fn synthesize_statement(&mut self, statement: &taroc_hir::Statement) -> Ty<'ctx> {
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
    fn synthesize_expression(
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
            taroc_hir::ExpressionKind::FieldAccess(..) => todo!("field access expression"),
            taroc_hir::ExpressionKind::Subscript(..) => todo!("subscript"),
            taroc_hir::ExpressionKind::CastAs(..) => todo!("cast expression"),
            taroc_hir::ExpressionKind::MatchBinding(..) => todo!("match binding expression"),
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
            taroc_hir::Literal::String(_) => todo!("string type"),
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
        self.context.add_constraint(constraint, rhs.span);
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

        match callee.kind() {
            TyKind::OverloadedFn(candidates) => {
                let mut schemes = vec![];
                candidates.into_iter().for_each(|id| {
                    let signature = self.context.fn_signature(*id);
                    schemes.push(signature);
                });

                let mut arg_tys = vec![];

                for argument in arguments.iter() {
                    arg_tys.push(self.synthesize_expression(&argument.expression, None));
                }

                let ty = self.resolve_overloads(&schemes, Some(&arg_tys), expectation, target.span);
                return ty;
            }
            _ => {
                // Check Callable
                let (param_tys, ret_ty) =
                    self.expect_callable(callee, arguments.len(), target.span);

                // Unify Each Argument
                for (argument, &parameter_ty) in arguments.iter().zip(param_tys) {
                    let argument_ty = self.synthesize_expression(&argument.expression, None);
                    let result =
                        self.coerce_or_unify(argument.expression.id, parameter_ty, argument_ty);

                    match result {
                        Err(message) => {
                            let message = format!(
                                "type mismatch. expected {parameter_ty}, found {argument_ty}"
                            );
                            self.context
                                .diagnostics
                                .error(message, argument.expression.span);
                        }
                        _ => {}
                    }
                }

                return ret_ty;
            }
        }
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
        self.context.add_constraint(constraint, node.condition.span);

        // Then
        let then_ty = self.synthesize_block_expression(&node.then_block);

        // Else
        if let Some(else_block) = &node.else_block {
            let else_ty = self.synthesize_expression(else_block, None);
            let constraint = Constraint::TypeEquality(else_ty, then_ty);
            self.context.add_constraint(constraint, else_block.span);
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
            let result = self.coerce_or_unify(expression.id, element_ty, element);
            if let Err(err) = result {
                self.context
                    .diagnostics
                    .error("TODO: report parameter err".into(), expression.span);
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

        return self.resolve_operator_overload(
            operand_type_id,
            op,
            &[operand_ty],
            expectation,
            expression.span,
        );
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

        return self.resolve_operator_overload(
            lhs_type_id,
            operand,
            &[lhs, rhs],
            expectation,
            span,
        );
    }

    fn synthesize_binary_assign_expression(
        &mut self,
        lhs: &taroc_hir::Expression,
        rhs: &taroc_hir::Expression,
        operator: BinaryOperator,
        span: Span,
    ) -> Ty<'ctx> {
        let lhs = self.synthesize_expression(lhs, None);
        let lhs_type_id = self.context.ty_to_def(lhs);
        let lhs = self.mk_ty(TyKind::Reference(lhs, Mutability::Mutable)); // Auto Ref lhs
        let _ = Adjustment::AutoMutRef; // TODO

        let rhs = self.synthesize_expression(rhs, None);
        let operand = OperatorKind::assign_from_binary(operator).expect("operator");
        let ty = self.resolve_operator_overload(
            lhs_type_id,
            operand,
            &[lhs, rhs],
            Some(self.void_ty()),
            span,
        );

        ty
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
}
impl<'ctx> FunctionChecker<'ctx> {
    fn instantiate(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        if !ty.needs_instantiation() {
            return ty;
        }

        // Mapping `GenericParameter.index -> fresh TyVar`
        type Subst<'ctx> = FxHashMap<GenericParameter, Ty<'ctx>>;
        let mut subst: Subst<'ctx> = FxHashMap::default();
        fn fold<'ctx>(
            this: &mut FunctionChecker<'ctx>,
            ty: Ty<'ctx>,
            subst: &mut Subst<'ctx>,
        ) -> Ty<'ctx> {
            match ty.kind() {
                TyKind::Parameter(param) => *subst
                    .entry(param)
                    .or_insert_with(|| this.context.fresh_ty_var()),

                TyKind::Pointer(inner, mutbl) => {
                    let inner = fold(this, inner, subst);
                    this.mk_ty(TyKind::Pointer(inner, mutbl))
                }
                TyKind::Reference(inner, mutbl) => {
                    let inner = fold(this, inner, subst);
                    this.mk_ty(TyKind::Reference(inner, mutbl))
                }
                TyKind::Array(inner, len) => {
                    let inner = fold(this, inner, subst);
                    this.mk_ty(TyKind::Array(inner, len))
                }
                TyKind::Tuple(elems) => {
                    let new_elems: Vec<Ty<'ctx>> =
                        elems.iter().map(|t| fold(this, *t, subst)).collect();
                    let new_elems = this.mk_ty_list(&new_elems);
                    this.mk_ty(TyKind::Tuple(new_elems))
                }
                TyKind::FnDef(id, args) => {
                    let args: Vec<GenericArgument<'ctx>> = args
                        .iter()
                        .map(|ga| match ga {
                            GenericArgument::Type(t) => {
                                GenericArgument::Type(fold(this, *t, subst))
                            }
                            other => *other,
                        })
                        .collect();
                    let args = this.context.store.interners.intern_generic_args(&args);
                    this.mk_ty(TyKind::FnDef(id, args))
                }
                TyKind::Function {
                    inputs,
                    output,
                    is_async,
                } => {
                    let inputs: Vec<Ty<'ctx>> =
                        inputs.iter().map(|t| fold(this, *t, subst)).collect();
                    let inputs = this.mk_ty_list(&inputs);

                    let output = fold(this, output, subst);
                    this.mk_ty(TyKind::Function {
                        inputs,
                        output,
                        is_async,
                    })
                }
                TyKind::Adt(def, args, parent) => {
                    let args: Vec<GenericArgument<'ctx>> = args
                        .iter()
                        .map(|ga| match ga {
                            GenericArgument::Type(t) => {
                                GenericArgument::Type(fold(this, *t, subst))
                            }
                            other => *other,
                        })
                        .collect();
                    let args = this.context.store.interners.intern_generic_args(&args);
                    let parent = parent.map(|t| fold(this, t, subst));
                    this.mk_ty(TyKind::Adt(def, args, parent))
                }

                // Primitive, infer, existential, etc.
                _ => ty,
            }
        }

        fold(self, ty, &mut subst)
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn solve_constraints(&mut self) {
        let constraints = self.context.take_constraints();

        for (constraint, span) in constraints {
            self.solve_constraint(constraint, span);
        }
    }

    fn solve_constraint(&mut self, constraint: Constraint<'ctx>, span: Span) {
        match constraint {
            Constraint::Bound { ty, interface } => {
                println!(
                    "Check: {ty}: {}{}",
                    self.context.def_symbol(interface.id),
                    GenericArgs(interface.arguments)
                )
                // println!("Interface Constraint: {constraint:?}");
            }
            Constraint::TypeEquality(lhs, rhs) => {
                println!("Check: {} == {}", lhs, rhs);
                let result = self.coerce_or_unify(NodeID::from_raw(0), lhs, rhs);

                match result {
                    Err(err) => match err {
                        UnificationError::OccursCheckFailed => {
                            todo!("ICE: report occurs check failure")
                        }
                        UnificationError::TypeMismatch => {
                            let message = format!("type mismatch. expected {rhs}, found {lhs}");
                            self.context.diagnostics.error(message, span);
                        }
                    },
                    _ => {}
                }
            }
        }
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn unify(&mut self, lhs: Ty<'ctx>, rhs: Ty<'ctx>) -> Result<(), UnificationError> {
        if lhs == rhs {
            return Ok(());
        };

        match (lhs.kind(), rhs.kind()) {
            (TyKind::Parameter(_), _) => self.unify_var(lhs, rhs),
            (_, TyKind::Parameter(_)) => self.unify_var(rhs, lhs),
            (TyKind::Infer(_), _) => self.unify_var(lhs, rhs),
            (_, TyKind::Infer(_)) => self.unify_var(rhs, lhs),

            // Structural types
            (TyKind::Tuple(lhs_e), TyKind::Tuple(rhs_e)) if lhs_e.len() == rhs_e.len() => {
                for (a, b) in lhs_e.iter().zip(rhs_e.iter()) {
                    self.unify(*a, *b)?;
                }
                Ok(())
            }

            (
                TyKind::Function {
                    inputs: lhs_i,
                    output: lhs_o,
                    is_async: lhs_is_async,
                },
                TyKind::Function {
                    inputs: rhs_i,
                    output: rhs_o,
                    is_async: rhs_is_async,
                },
            ) if lhs_i.len() == rhs_i.len() && lhs_is_async == rhs_is_async => {
                // inputs
                for (lhs_i, rhs_i) in lhs_i.iter().zip(rhs_i.iter()) {
                    self.unify(*lhs_i, *rhs_i)?;
                }

                // outputs
                self.unify(lhs_o, rhs_o)?;

                return Ok(());
            }

            (
                TyKind::Adt(lhs_id, lhs_args, lhs_parent),
                TyKind::Adt(rhs_id, rhs_args, rhs_parent),
            ) if lhs_id == rhs_id && lhs_args.len() == rhs_args.len() => {
                // Parent
                match (lhs_parent, rhs_parent) {
                    (Some(s1), Some(s2)) => self.unify(s1, s2)?,
                    (None, None) => {}
                    _ => unreachable!("ICE: ADT subtype presence mismatch"),
                };

                // Arguments
                for (a1, a2) in lhs_args.iter().zip(rhs_args.iter()) {
                    match (a1, a2) {
                        (GenericArgument::Type(t1), GenericArgument::Type(t2)) => {
                            self.unify(*t1, *t2)?;
                        }
                        (GenericArgument::Const(c1), GenericArgument::Const(c2)) => {
                            if c1 != c2 {
                                unreachable!("mismatch const generic argument");
                            }
                        }
                        _ => {
                            unreachable!(
                                "ICE: cannot have mismatched generic argument kind (type vs const)"
                            );
                        }
                    }
                }
                return Ok(());
            }
            _ => {
                return Err(UnificationError::TypeMismatch);
            }
        }
    }

    fn unify_var(&mut self, lhs: Ty<'ctx>, rhs: Ty<'ctx>) -> Result<(), UnificationError> {
        match lhs.kind() {
            TyKind::Infer(InferTy::TyVar(id)) => {
                let root = self.context.find_tyvar(id);

                // already bound  ⇒  delegate
                if let Some(bound) = self.context.tyvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }

                // TyVar ↔ TyVar  ⇒  merge
                if let TyKind::Infer(InferTy::TyVar(rid)) = rhs.kind() {
                    let rhs_root = self.context.find_tyvar(rid);
                    if root == rhs_root {
                        return Ok(());
                    }

                    // pick the representative that already has a concrete type
                    let (rep, other) = if self.context.tyvar_bindings[root].bound_ty.is_some() {
                        (root, rhs_root)
                    } else {
                        (rhs_root, root)
                    };

                    // *move* the binding so the representative keeps it
                    if let Some(t) = self.context.tyvar_bindings[other].bound_ty {
                        self.context.tyvar_bindings[rep].bound_ty = Some(t);
                    }

                    self.context.tyvar_bindings[other].parent = Some(rep);
                    return Ok(());
                }

                // occurs-check to avoid α = List<α>
                if self.occurs_in_ty(root, rhs) {
                    return Err(UnificationError::OccursCheckFailed);
                }

                // bind var → rhs
                self.context.tyvar_bindings[root].bound_ty = Some(rhs);
                Ok(())
            }

            TyKind::Infer(InferTy::IntVar(id)) => {
                let root = self.context.find_intvar(id);

                if let TyKind::Infer(InferTy::IntVar(rhs_id)) = rhs.kind() {
                    let rhs_root = self.context.find_intvar(rhs_id);
                    if root == rhs_root {
                        return Ok(());
                    }

                    self.context.intvar_bindings[root].parent = Some(rhs_root);
                    return Ok(());
                }

                if let Some(bound) = self.context.intvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }

                // If `rhs` is a concrete integer type, bind var → that type
                if matches!(rhs.kind(), TyKind::Int(..) | TyKind::UInt(..)) {
                    self.context.intvar_bindings[root].bound_ty = Some(rhs);
                    return Ok(());
                }

                return Err(UnificationError::TypeMismatch);
            }
            TyKind::Infer(InferTy::FloatVar(id)) => {
                let root = self.context.find_floatvar(id);
                if let TyKind::Infer(InferTy::FloatVar(rid)) = rhs.kind() {
                    let rhs_root = self.context.find_floatvar(rid);
                    if root != rhs_root {
                        self.context.floatvar_bindings[root].parent = Some(rhs_root);
                    }
                    return Ok(());
                }
                if let Some(bound) = self.context.floatvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }
                if matches!(rhs.kind(), TyKind::Float(..)) {
                    self.context.floatvar_bindings[root].bound_ty = Some(rhs);
                    return Ok(());
                }
                return Err(UnificationError::TypeMismatch);
            }

            TyKind::Infer(InferTy::NilVar(id)) => {
                let root = self.context.find_nilvar(id);
                if let TyKind::Infer(InferTy::NilVar(rid)) = rhs.kind() {
                    let rhs_root = self.context.find_nilvar(rid);
                    if root != rhs_root {
                        self.context.nilvar_bindings[root].parent = Some(rhs_root);
                    }
                    return Ok(());
                }
                if let Some(bound) = self.context.nilvar_bindings[root].bound_ty {
                    return self.unify(bound, rhs);
                }
                if self.is_nil_compatible(rhs.kind()) {
                    self.context.nilvar_bindings[root].bound_ty = Some(rhs);
                    return Ok(());
                }
                return Err(UnificationError::TypeMismatch);
            }
            _ => unreachable!("ICE: `unify_var` called for non inferred type {lhs}"),
        }
    }

    fn is_nil_compatible(&self, kind: TyKind<'ctx>) -> bool {
        match kind {
            TyKind::Pointer(..) => true,
            TyKind::Adt(def, ..) => def.id == self.optional_def_id(), // TODO: isOption type
            _ => false,
        }
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    /// Ensure `callee_ty` behaves like `fn(param₀, …, paramₙ) -> ret`
    pub fn expect_callable(
        &mut self,
        callee_ty: Ty<'ctx>,
        arity: usize,
        span: Span,
    ) -> (&'ctx [Ty<'ctx>], Ty<'ctx>) {
        match callee_ty.kind() {
            TyKind::Function { inputs, output, .. } => {
                // Check Arity
                if inputs.len() != arity {
                    let message = format!(
                        "expected {arity} argument{}, but function takes {}",
                        if arity == 1 { "" } else { "s" },
                        inputs.len()
                    );

                    self.context.diagnostics.error(message, span);
                }
                (inputs, output)
            }

            TyKind::FnDef(id, _) => {
                let mono = self.instantiate(callee_ty);
                let arguments = match mono.kind() {
                    TyKind::FnDef(_, arguments) => arguments,
                    _ => unreachable!(),
                };

                let signature = self.context.fn_signature(id);
                let signature =
                    utils::convert_labeled_signature_to_signature(&signature, *self.context);

                let subst = utils::create_substitution_map(id, arguments, *self.context);
                let signature = utils::substitute(signature, &subst, None, *self.context);

                self.context
                    .instantiate_definition_constraints(id, arguments);

                return self.expect_callable(signature, arity, span);
            }

            // Unbound TyVar —> bind it to a *synthetic* fn type
            TyKind::Infer(InferTy::TyVar(vid)) => {
                let root = self.context.find_tyvar(vid);

                // Re-use an earlier synthetic fn if we already forced one
                if let Some(bound) = self.context.tyvar_bindings[root].bound_ty {
                    if let TyKind::Function { inputs, output, .. } = bound.kind() {
                        return (inputs, output);
                    }
                }

                // Otherwise invent  fn(β0,…,βₙ) -> βr
                let mut params = Vec::with_capacity(arity);
                for _ in 0..arity {
                    params.push(self.context.fresh_ty_var());
                }
                let params_slice = self.mk_ty_list(&params);
                let ret = self.context.fresh_ty_var();
                let fn_ty = self.mk_ty(TyKind::Function {
                    inputs: params_slice,
                    output: ret,
                    is_async: false,
                });

                self.context.tyvar_bindings[root].bound_ty = Some(fn_ty);
                (params_slice, ret)
            }

            // Every other kind is “not callable”
            _ => {
                let message = format!("value of type `{}` is not callable", callee_ty);
                self.context.diagnostics.error(message, span);
                (
                    &[],
                    self.error_ty(), // propagate error so checking continues
                )
            }
        }
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn mk_ty(&mut self, kind: TyKind<'ctx>) -> Ty<'ctx> {
        self.context.store.interners.intern_ty(kind)
    }

    fn mk_ty_list(&mut self, tys: &Vec<Ty<'ctx>>) -> &'ctx [Ty<'ctx>] {
        self.context.store.interners.intern_ty_list(tys)
    }

    /// Does the TyVar with canonical *root* id appear syntactically inside `ty`?
    /// We call `find_tyvar` on every Infer-TyVar we encounter so the test
    /// remains valid even after several union-find merges.
    fn occurs_in_ty(&mut self, root: TyVid, ty: Ty<'ctx>) -> bool {
        match ty.kind() {
            // If we see *any* TyVar, compare its current root with the one we test
            TyKind::Infer(InferTy::TyVar(id)) => self.context.find_tyvar(id) == root,

            // Walk composite structures ---------------------------------------------------
            TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) => {
                self.occurs_in_ty(root, inner)
            }

            TyKind::Array(elem, _) => self.occurs_in_ty(root, elem),

            TyKind::Tuple(elems) => elems.iter().any(|t| self.occurs_in_ty(root, *t)),

            TyKind::Function { inputs, output, .. } => {
                inputs.iter().any(|t| self.occurs_in_ty(root, *t))
                    || self.occurs_in_ty(root, output)
            }

            TyKind::Adt(_, args, self_ty) => {
                args.iter()
                    .filter_map(|ga| ga.ty())
                    .any(|t| self.occurs_in_ty(root, t))
                    || self_ty.map_or(false, |t| self.occurs_in_ty(root, t))
            }

            // Existential, associated, primitives, IntVar, FloatVar, NilVar, etc.
            // cannot contain a *TyVar* inside their structure, so return false.
            _ => false,
        }
    }

    fn optional_def_id(&self) -> DefinitionID {
        let store = self.context.store.common_types.mappings.foundation.borrow();
        let optional_id = store.get(&Symbol::with("Option"));
        optional_id.cloned().expect("Optional Type")
    }

    fn error_ty(&self) -> Ty<'ctx> {
        self.context.store.common_types.error
    }

    fn void_ty(&self) -> Ty<'ctx> {
        self.context.store.common_types.void
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn try_coerce(
        &mut self,
        provided: Ty<'ctx>,
        expected: Ty<'ctx>,
    ) -> Result<Option<Coercion>, UnificationError> {
        println!("Try Coerce: {} -> {}", provided, expected);
        match (provided.kind(), expected.kind()) {
            // &mut T -> &T
            (
                TyKind::Reference(t1, Mutability::Mutable),
                TyKind::Reference(t2, Mutability::Immutable),
            ) => {
                self.unify(t1, t2)?; // unify inside!
                return Ok(Some(Coercion {
                    ty: expected,
                    adjustments: vec![Adjustment::MutRefConstCast],
                }));
            }
            // *mut T -> *T
            (
                TyKind::Pointer(t1, Mutability::Mutable),
                TyKind::Pointer(t2, Mutability::Immutable),
            ) => {
                self.unify(t1, t2)?; // unify inside!
                return Ok(Some(Coercion {
                    ty: expected,
                    adjustments: vec![Adjustment::MutPtrConstCast],
                }));
            }

            // nil -> Option<T>
            (TyKind::Infer(InferTy::NilVar(_)), TyKind::Adt(def, ..))
                if def.id == self.optional_def_id() =>
            {
                self.unify(provided, expected)?;
                return Ok(Some(Coercion {
                    ty: expected,
                    adjustments: vec![Adjustment::WrapNilToOptionalNone],
                }));
            }
            // T -> Option<T>
            (_, TyKind::Adt(def, &[arg], _)) if def.id == self.optional_def_id() => {
                self.unify(provided, arg.ty().unwrap())?; // unify inside!
                return Ok(Some(Coercion {
                    ty: expected,
                    adjustments: vec![Adjustment::WrapOptional],
                }));
            }

            _ => return Ok(None),
        }
    }

    fn coerce_or_unify(
        &mut self,
        node: NodeID,
        provided: Ty<'ctx>,
        expected: Ty<'ctx>,
    ) -> Result<(), UnificationError> {
        if let Some(adjustment) = self.try_coerce(provided, expected)? {
            // TODO: Insert Adjustments
            return Ok(());
        }

        self.unify(provided, expected)?;
        return Ok(());
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn resolve_overloads(
        &mut self,
        schemes: &Vec<LabeledFunctionSignature<'ctx>>,
        arg_tys: Option<&[Ty<'ctx>]>,
        return_ty: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        // Collect (score, return_type, adjustments) for each viable candidate
        // let mut candidates: Vec<(DefinitionID, usize, Ty<'ctx>, Vec<Adjustment>)> = Vec::new();
        let mut candidates = vec![];
        const LIMIT: usize = 128;

        // Quick Filter

        for scheme in schemes.into_iter().take(LIMIT) {
            let constraints = self.context.take_constraints();
            let result = self.evaluate_overload_candidate(&scheme, arg_tys, return_ty);
            self.context.set_constraints(constraints);
            if result.is_some() {
                candidates.push(result.unwrap());
            }
        }

        // pick the best
        candidates.sort_by_key(|(score, _)| *score);
        if candidates.is_empty() {
            self.context
                .diagnostics
                .error("type error: no matching overloads".into(), span);
            return self.error_ty();
        }

        if candidates.len() > 1 && candidates[0].0 == candidates[1].0 {
            let id = schemes.first().unwrap().id;
            let symbol = self.context.def_symbol(id);
            let message = format!("type error: ambigious call to function '{}'", symbol);
            self.context.diagnostics.error(message, span);
            return self.error_ty();
        }

        let (_score, ret) = candidates.remove(0);
        ret
    }

    fn evaluate_overload_candidate(
        &mut self,
        scheme: &LabeledFunctionSignature<'ctx>,
        expected_arg_tys: Option<&[Ty<'ctx>]>,
        expected_return_ty: Option<Ty<'ctx>>,
    ) -> Option<(usize, Ty<'ctx>)> {
        let signature = utils::convert_labeled_signature_to_signature(&scheme, *self.context);
        let signature = self.instantiate(signature);
        let (candidate_parameter_tys, candidate_return_ty) = match signature.kind() {
            TyKind::Function { inputs, output, .. } => (inputs, output),
            _ => unreachable!("must be function sig kin"),
        };

        // Arguments Provided
        if let Some(expected_arg_tys) = expected_arg_tys {
            // arity filter
            if candidate_parameter_tys.len() != expected_arg_tys.len() {
                return None;
            }

            // parameter unification/coercion
            for (&param_ty, &arg_ty) in candidate_parameter_tys.iter().zip(expected_arg_tys.iter())
            {
                let result = self.coerce_or_unify(NodeID::from_usize(0), arg_ty, param_ty);
                if result.is_err() {
                    return None;
                }
            }
        }

        // Return Type Provided
        if let Some(expected_return_ty) = expected_return_ty {
            let result = self.coerce_or_unify(
                NodeID::from_usize(0),
                expected_return_ty,
                candidate_return_ty,
            );
            if result.is_err() {
                return None;
            }
        }

        // Solve Constraints
        // TODO: solve constraints
        self.solve_constraints();

        // specificity score (exact < generic < existential < conversion)
        let score = match expected_arg_tys {
            Some(arg_tys) => {
                self.rank_specificity(&candidate_parameter_tys, arg_tys, candidate_return_ty)
            }
            None => 0, // no args yet, only use expected return type
        };

        return Some((score, candidate_return_ty));
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    /// Compute a specificity score:
    ///  - exact matches              → +0
    ///  - generic binds (type var)   → +1
    ///  - boxing to existential      → +3
    ///  - other conversions (e.g. numeric widens) → +4
    ///
    /// Lower total score = more specific candidate.
    pub fn rank_specificity(
        &self,
        param_tys: &[Ty<'ctx>],
        arg_tys: &[Ty<'ctx>],
        ret_ty: Ty<'ctx>,
    ) -> usize {
        assert_eq!(param_tys.len(), arg_tys.len());

        param_tys
            .iter()
            .zip(arg_tys.iter())
            .map(|(p, a)| {
                // Apply the substitution to the parameter
                let p_ty = *p;

                if p_ty == *a {
                    // exact match
                    0
                } else if let TyKind::Infer(InferTy::TyVar(_)) = p_ty.kind() {
                    // a generic parameter that got bound to `a`
                    1
                } else if let TyKind::Existential(_) = p_ty.kind() {
                    // a protocol/existential type requires boxing
                    3
                } else {
                    // any other allowed conversion (numeric widen, mutability cast, etc.)
                    4
                }
            })
            .sum::<usize>()
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn resolve_operator_overload(
        &mut self,
        id: Option<DefinitionID>,
        op: OperatorKind,
        args: &[Ty<'ctx>],
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        match id {
            Some(id) => {
                self.resolve_known_definition_operator_overload(id, op, args, expectation, span)
            }
            _ => todo!("operator overload on complex ty"),
        }
    }

    fn resolve_known_definition_operator_overload(
        &mut self,
        id: DefinitionID,
        op: OperatorKind,
        args: &[Ty<'ctx>],
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        let functions = self.context.with_type_database(id.package(), |db| {
            db.def_to_functions
                .entry(id)
                .or_insert(Default::default())
                .clone()
        });

        let functions = functions.borrow();
        let functions = functions.operators.get(&op);

        let Some(functions) = functions else {
            let message = format!("no viable overloads available!");
            self.context.diagnostics.error(message, span);
            return self.error_ty();
        };

        let ty = self.resolve_overloads(functions, Some(args), expectation, span);

        return ty;
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn resolve_constructor(&mut self, id: DefinitionID) -> Ty<'ctx> {
        let functions = self.context.with_type_database(id.package(), |db| {
            db.def_to_functions
                .entry(id)
                .or_insert(Default::default())
                .clone()
        });

        let functions = functions.borrow();
        let candidates: Vec<_> = functions
            .constructors
            .iter()
            .clone()
            .map(|v| v.id)
            .collect();

        let kind = TyKind::OverloadedFn(self.context.store.interners.intern_slice(&candidates));
        return self.mk_ty(kind);
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn resolve_known_method_call(
        &mut self,
        receiver_def_id: DefinitionID,
        receiver_ty: Ty<'ctx>, // Added: The actual type of the receiver expression
        method_segment: &taroc_hir::PathSegment,
        explicit_arg_tys: &[Ty<'ctx>], // Explicit arguments only
        expectation: Option<Ty<'ctx>>,
        span: Span,
    ) -> Ty<'ctx> {
        let name = method_segment.identifier.symbol;
        let functions = self
            .context
            .with_type_database(receiver_def_id.package(), |db| {
                db.def_to_functions
                    .entry(receiver_def_id)
                    .or_insert(Default::default())
                    .clone()
            });

        let functions = functions.borrow();
        let functions = functions.methods.get(&name);

        let Some(candidates) = functions else {
            let message = format!("no method named {}", name);
            self.context
                .diagnostics
                .error(message, method_segment.identifier.span);
            return self.error_ty();
        };

        // --- Resolve Using Method-Specific Logic ---
        // Pass receiver type and explicit args separately
        self.resolve_method_overloads(
            &candidates,
            receiver_ty,
            explicit_arg_tys,
            expectation,
            name,
            span,
        )
    }

    /// Resolves method overloading, handling `self`, `&self`, `&mut self` receivers.
    fn resolve_method_overloads(
        &mut self,
        schemes: &Vec<LabeledFunctionSignature<'ctx>>,
        receiver_ty: Ty<'ctx>,
        explicit_arg_tys: &[Ty<'ctx>],
        return_ty_expectation: Option<Ty<'ctx>>,
        method_name: Symbol,
        span: Span,
    ) -> Ty<'ctx> {
        let mut candidates = vec![];
        const LIMIT: usize = 128;

        for scheme in schemes.iter().take(LIMIT) {
            // Use a sandbox for constraints generated during this candidate check
            let constraints_snapshot = self.context.take_constraints();

            let result = self.evaluate_method_candidate(
                scheme,
                receiver_ty,
                explicit_arg_tys,
                return_ty_expectation,
            );

            // Restore constraints regardless of success/failure
            self.context.set_constraints(constraints_snapshot);

            if let Some(viable_candidate) = result {
                candidates.push(viable_candidate);
            }
        }

        // --- Pick the best candidate ---
        // TODO: Refine sorting/ambiguity check if needed
        candidates.sort_by_key(|(score, _, _)| *score);

        if candidates.is_empty() {
            // TODO: Improve this error message - perhaps list candidates considered and why they failed?
            let message = format!(
                "no matching method overload for '{}' found with receiver type '{}' and argument types ({})",
                method_name, // Use actual method name if available
                receiver_ty,
                explicit_arg_tys
                    .iter()
                    .map(|t| format!("{}", t))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            self.context.diagnostics.error(message, span);
            return self.error_ty();
        }

        if candidates.len() > 1 && candidates[0].0 == candidates[1].0 {
            let method_name = schemes
                .first()
                .map(|s| self.context.def_symbol(s.id))
                .unwrap_or_else(|| Symbol::intern("?"));
            let message = format!(
                "ambiguous method call for '{}': multiple candidates match equally well",
                method_name // Use actual method name
            );
            // TODO: List ambiguous candidates
            self.context.diagnostics.error(message, span);
            return self.error_ty();
        }

        // Success!
        let (_score, ret_ty, _adjustments) = candidates.remove(0); // TODO: Store adjustments
        // We need to store the adjustments (for receiver and args) somewhere!
        // E.g., self.context.insert_adjustments(call_expr_id, adjustments);
        ret_ty
    }

    /// Evaluates a single method candidate against the receiver and arguments.
    /// Returns (score, return_type, adjustments) if viable.
    fn evaluate_method_candidate(
        &mut self,
        scheme: &LabeledFunctionSignature<'ctx>,
        receiver_ty: Ty<'ctx>,
        explicit_arg_tys: &[Ty<'ctx>],
        return_ty_expectation: Option<Ty<'ctx>>,
    ) -> Option<(usize, Ty<'ctx>, Vec<Adjustment>)> {
        // Added Adjustments Vec

        // 1. Instantiate the signature (replaces generics with InferTy variables)
        let signature = utils::convert_labeled_signature_to_signature(&scheme, *self.context);
        let signature = self.instantiate(signature);
        let (candidate_parameter_tys, candidate_return_ty) = match signature.kind() {
            // Expecting fn(SelfParam, ExplicitParam1, ...) -> Ret
            TyKind::Function { inputs, output, .. } => (inputs, output),
            _ => unreachable!("method signature must be a function type after instantiation"),
        };

        // 2. Check Arity (must have at least 1 param for receiver, plus explicit args)
        if candidate_parameter_tys.len() != explicit_arg_tys.len() + 1 {
            //println!("Arity mismatch: Candidate {} params, Explicit {} args", candidate_parameter_tys.len(), explicit_arg_tys.len());
            return None; // Arity mismatch (receiver + explicit args vs candidate params)
        }

        let self_param_ty = candidate_parameter_tys[0];
        let candidate_explicit_param_tys = &candidate_parameter_tys[1..];

        let mut adjustments = Vec::new(); // Collect adjustments here
        let mut score = 0;

        // --- 3. Check Receiver Type ---
        // This is the core difference: match receiver_ty against self_param_ty with auto-ref/deref.
        // We check if receiver_ty *can be coerced or unified* with self_param_ty, potentially
        // applying auto-(mut)-ref.
        let receiver_match_result = self.try_match_receiver(receiver_ty, self_param_ty);

        let Ok((receiver_score, receiver_adjustment)) = receiver_match_result else {
            //println!("Receiver mismatch: Receiver {}, Expected Self {}", receiver_ty, self_param_ty);
            return None; // Receiver doesn't match required self type
        };
        score += receiver_score;
        if let Some(adj) = receiver_adjustment {
            adjustments.push(adj); // TODO: Store adjustment properly keyed to receiver expr
        }

        // --- 4. Check Explicit Argument Types ---
        for (_, (&candidate_param, &provided_arg)) in candidate_explicit_param_tys
            .iter()
            .zip(explicit_arg_tys.iter())
            .enumerate()
        {
            // Use coerce_or_unify for explicit args
            // We need the NodeID of the argument expression here ideally
            let arg_node_id = NodeID::from_usize(0); // Placeholder! Pass real ID down
            match self.try_coerce_or_unify_with_score(arg_node_id, provided_arg, candidate_param) {
                Ok((arg_score, arg_adjustment)) => {
                    score += arg_score;
                    if let Some(adj) = arg_adjustment {
                        adjustments.push(adj); // TODO: Store adjustment keyed to specific arg expr
                    }
                }
                Err(_) => {
                    //println!("Arg {} mismatch: Provided {}, Expected {}", i, provided_arg, candidate_param);
                    return None; // Argument type mismatch
                }
            }
        }

        // --- 5. Check Return Type ---
        if let Some(expected_ret_ty) = return_ty_expectation {
            // Use coerce_or_unify for return type check
            let ret_node_id = NodeID::from_usize(0); // Placeholder! Use call expr span/id
            match self.try_coerce_or_unify_with_score(
                ret_node_id,
                candidate_return_ty,
                expected_ret_ty,
            ) {
                Ok((ret_score, ret_adjustment)) => {
                    score += ret_score; // Add score for return type coercion? Maybe not.
                    if let Some(_) = ret_adjustment {
                        // TODO
                        // Adjustments on the *result* of the call are less common to track this way
                        // adjustments.push(adj);
                    }
                }
                Err(_) => {
                    //println!("Return mismatch: Actual {}, Expected {}", candidate_return_ty, expected_ret_ty);
                    return None; // Return type mismatch
                }
            }
        }

        // --- 6. Solve Constraints ---
        // Constraints might have been generated during unification steps above.
        // TODO: This needs to handle potential failures from constraint solving!
        self.solve_constraints(); // Assume this reports errors via diagnostics if it fails hard

        // TODO: Check if any errors were reported by solve_constraints?

        // If we got here, the candidate is viable
        Some((score, candidate_return_ty, adjustments))
    }

    /// Tries to match the receiver type against the expected self parameter type,
    /// considering auto-ref/deref rules. Returns (score, Option<Adjustment>) on success.
    fn try_match_receiver(
        &mut self,
        receiver_ty: Ty<'ctx>,
        self_param_ty: Ty<'ctx>,
    ) -> Result<(usize, Option<Adjustment>), UnificationError> {
        // Most exact match: Unify directly
        if self.unify(receiver_ty, self_param_ty).is_ok() {
            return Ok((0, None)); // Exact match or unification works
        }

        // Try matching &self
        if let TyKind::Reference(self_inner_ty, Mutability::Immutable) = self_param_ty.kind() {
            // Try auto-ref: Can receiver_ty unify with self_inner_ty?
            if self.unify(receiver_ty, self_inner_ty).is_ok() {
                // Check if receiver is addressable, etc. (might be implicit for now)
                return Ok((1, Some(Adjustment::AutoRef))); // Matched via &
            }
            // TODO: Add check for auto-deref then ref? &self method
        }

        // Try matching &mut self
        if let TyKind::Reference(self_inner_ty, Mutability::Mutable) = self_param_ty.kind() {
            // Try auto-mut-ref: Can receiver_ty unify with self_inner_ty?
            if self.unify(receiver_ty, self_inner_ty).is_ok() {
                // !!! Crucially, we also need to check if the original receiver expression
                // !!! corresponds to a mutable place. This check needs context beyond types.
                // For now, we assume it's possible if types unify.
                return Ok((1, Some(Adjustment::AutoMutRef))); // Matched via &mut
            }
            // TODO: Add check for auto-deref then mut ref?
        }

        // TODO: Try matching `self` by value via auto-deref?
        // if let TyKind::Pointer(inner, _) | TyKind::Reference(inner, _) = receiver_ty.kind() {
        //     // If self_param_ty isn't a ref/ptr, try unifying self_param_ty with inner
        //     if !matches!(self_param_ty.kind(), TyKind::Reference(..) | TyKind::Pointer(..)) {
        //          if self.unify(inner, self_param_ty).is_ok() {
        //              // Requires Deref/DerefMut trait typically
        //              return Ok((2, Some(Adjustment::AutoDeref)));
        //          }
        //     }
        // }

        // If none of the above worked
        Err(UnificationError::TypeMismatch)
    }

    /// Like coerce_or_unify, but returns a score and adjustment info.
    /// Placeholder NodeID needed.
    fn try_coerce_or_unify_with_score(
        &mut self,
        node: NodeID, // Placeholder node ID
        provided: Ty<'ctx>,
        expected: Ty<'ctx>,
    ) -> Result<(usize, Option<Adjustment>), UnificationError> {
        // Try exact match / unification first
        if self.unify(provided, expected).is_ok() {
            return Ok((0, None)); // Score 0 for exact match/unification
        }

        // Then try coercions (add score > 0 for coercions)
        match self.try_coerce(provided, expected) {
            // Assuming try_coerce returns Result<Option<Coercion>, UnificationError>
            Ok(Some(coercion)) => {
                // Assign a score based on the *kind* of coercion if needed, otherwise a flat score.
                let score = match coercion.adjustments.first() {
                    // Simple heuristic
                    Some(Adjustment::MutRefConstCast | Adjustment::MutPtrConstCast) => 3,
                    Some(Adjustment::WrapNilToOptionalNone | Adjustment::WrapOptional) => 2,
                    _ => 4, // Other coercions
                };
                // Return only the *first* adjustment for simplicity here?
                // A single coercion might involve multiple steps in Adjustment enum later.
                Ok((score, coercion.adjustments.into_iter().next()))
            }
            Ok(None) => Err(UnificationError::TypeMismatch), // No coercion applied, and unify failed
            Err(e) => Err(e), // Coercion attempt itself failed unification internally
        }
    }
}
