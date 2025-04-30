mod overload;
mod solve;
mod synth;
mod unify;

use crate::{
    lower,
    models::{InferenceContext, SubstitutionMap, TaggedAdjustments, UnificationError},
    utils,
};
use rustc_hash::FxHashMap;
use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{DefinitionID, Mutability, NodeID, OperatorKind};
use taroc_span::{Span, Symbol};
use taroc_ty::{
    Adjustment, Coercion, Constraint, GenericArgument, GenericParameter, InferTy,
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
                self.check_function(node, declaration);
            }
            taroc_hir::DeclarationKind::Variable(..) => {}
            taroc_hir::DeclarationKind::Constant(..) => {}
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

pub struct FunctionChecker<'ctx> {
    pub context: InferenceContext<'ctx>,
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
                let (node_id, span, ty) = if let Some(expression) = expression {
                    (
                        expression.id,
                        expression.span,
                        self.synthesize_expression(expression, Some(return_ty)),
                    )
                } else {
                    (
                        statement.id,
                        statement.span,
                        self.context.store.common_types.void,
                    )
                };

                let constraint = Constraint::TypeEquality(ty, return_ty);
                self.context.add_constraint(constraint, node_id, span);
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
        self.context
            .add_constraint(constraint, expression.id, expression.span);
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn instantiate(&mut self, ty: Ty<'ctx>) -> Ty<'ctx> {
        if !ty.needs_instantiation() {
            return ty;
        }

        let mut map = SubstitutionMap::new();
        return self.instantiate_with_map(ty, &mut map);
    }

    fn instantiate_with_map(&mut self, ty: Ty<'ctx>, map: &mut SubstitutionMap<'ctx>) -> Ty<'ctx> {
        fn fold<'ctx>(
            this: &mut FunctionChecker<'ctx>,
            ty: Ty<'ctx>,
            subst: &mut SubstitutionMap<'ctx>,
        ) -> Ty<'ctx> {
            match ty.kind() {
                TyKind::Parameter(param) => {
                    if let Some(x) = subst.get(&param) {
                        if let Some(ty) = x.ty() {
                            return ty;
                        } else {
                            todo!("const param")
                        }
                    } else {
                        return this.context.fresh_ty_var();
                    }
                }

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

        fold(self, ty, map)
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
                println!("Mono'd as {mono}");
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
                let signature = self.instantiate(signature);
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

    pub fn error_ty(&self) -> Ty<'ctx> {
        self.context.store.common_types.error
    }

    pub fn void_ty(&self) -> Ty<'ctx> {
        self.context.store.common_types.void
    }

    pub fn string_type(&self) -> Ty<'ctx> {
        let store = self.context.store.common_types.mappings.foundation.borrow();
        let id = store
            .get(&Symbol::with("String"))
            .cloned()
            .expect("Foundational String Type");

        return self.context.type_of(id);
    }

    fn deref_target(&self, ty: Ty<'ctx>) -> Option<Ty<'ctx>> {
        match ty.kind() {
            // Handle built-in reference types
            TyKind::Reference(inner_ty, _) => Some(inner_ty),
            // Handle built-in raw pointer types
            TyKind::Pointer(inner_ty, _) => Some(inner_ty),
            _ => None,
        }
    }
}

impl<'ctx> FunctionChecker<'ctx> {
    fn try_coerce(
        &mut self,
        provided: Ty<'ctx>,
        expected: Ty<'ctx>,
    ) -> Result<Option<Coercion<'ctx>>, UnificationError> {
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

    pub fn coerce_or_unify(
        &mut self,
        provided: Ty<'ctx>,
        expected: Ty<'ctx>,
    ) -> Result<Vec<Adjustment>, UnificationError> {
        if let Some(coercion) = self.try_coerce(provided, expected)? {
            return Ok(coercion.adjustments);
        }

        self.unify(provided, expected)?;
        return Ok(vec![]);
    }
}
