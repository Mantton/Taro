use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::{self, DefinitionID, HirVisitor},
    sema::tycheck::{lower::TypeLowerer, results::TypeCheckResults},
};
use std::{cell::RefCell, rc::Rc};

mod checker;
mod convenience;
mod dynamic_self;
mod gather;
mod node;

pub fn run<'ctx>(
    package: &hir::Package,
    context: Gcx<'ctx>,
) -> CompileResult<TypeCheckResults<'ctx>> {
    let mut actor = Actor::new(context);
    hir::walk_package(&mut actor, package);
    context.dcx().ok()?;
    // Type headers can consume a constant before extension constraints are
    // available. Check these reads in their original declaration environment.
    let uses = std::mem::take(&mut *context.store.constant_member_uses.borrow_mut());
    let mut uses: Vec<_> = uses.into_iter().collect();
    uses.sort_by_key(|(id, _)| *id);
    for (id, entry) in uses {
        if actor.results.borrow().try_node_type(id).is_none() {
            checker::Checker::new(context, entry.owner, actor.results.clone())
                .top_level_check(entry.expression, entry.expected);
        }
        if let Some(expected) = entry.header_witness
            && !context.dcx().has_error()
        {
            let actual = super::utils::const_eval::checked_static_resolution(
                context,
                entry.expression,
                &actor.results.borrow(),
            );
            if actual.and_then(|resolution| resolution.definition_id()) != Some(expected) {
                context.dcx().emit_error(
                    "constant implementation changed while resolving declaration header".into(),
                    Some(entry.expression.span),
                );
            }
        }
    }
    context.dcx().ok()?;
    let mut results = actor.results.borrow_mut();
    hir::walk_package(
        &mut LiteralValidator {
            context,
            results: &mut results,
        },
        package,
    );
    context.dcx().ok()?;
    convenience::validate(package, context, &results);
    context.dcx().ok()?;
    drop(results);
    dynamic_self::run(package, context, &mut actor.results.borrow_mut());
    context.dcx().ok()?;
    if !actor.pending_mir_consts.is_empty() {
        let results_snapshot = Rc::new(actor.results.borrow().clone());
        crate::mir::const_eval::eval_package_const_items(
            package,
            context,
            results_snapshot,
            &actor.pending_mir_consts,
        );
        context.dcx().ok()?;
    }
    Ok(std::mem::take(&mut *actor.results.borrow_mut()))
}

pub(crate) fn check_const_expr_on_demand<'ctx>(
    context: Gcx<'ctx>,
    owner_id: DefinitionID,
    expr: &hir::Expression,
    expected: Option<crate::sema::models::Ty<'ctx>>,
    results: Rc<RefCell<TypeCheckResults<'ctx>>>,
) -> crate::sema::models::Ty<'ctx> {
    let checker = checker::Checker::new(context, owner_id, results);
    checker.top_level_check(expr, expected)
}

pub(crate) fn check_const_fn_on_demand<'ctx>(
    context: Gcx<'ctx>,
    id: DefinitionID,
    node: &hir::Function,
    fn_ctx: hir::FunctionContext,
    results: Rc<RefCell<TypeCheckResults<'ctx>>>,
) {
    let mut checker = checker::Checker::new(context, id, results);
    checker.check_function(id, node, fn_ctx);
}

// Expectations are optional during inference. Validate every literal once its
// final type is known, including values constrained by a later use.
struct LiteralValidator<'a, 'ctx> {
    context: Gcx<'ctx>,
    results: &'a mut TypeCheckResults<'ctx>,
}

impl<'ctx> LiteralValidator<'_, 'ctx> {
    fn check(
        &self,
        literal: &hir::Literal,
        id: hir::NodeID,
        span: crate::span::Span,
        pattern: bool,
    ) {
        if let hir::Literal::Integer { value, .. } = literal
            && let Some(ty) = self.results.try_node_type(id)
            && !(if pattern {
                super::utils::literal::integer_literal_fits(
                    *value,
                    ty,
                    self.context.store.target_facts.pointer_bits(),
                )
            } else {
                super::utils::literal::integer_expression_literal_fits(
                    *value,
                    ty,
                    self.context.store.target_facts.pointer_bits(),
                )
            })
        {
            self.context.dcx().emit_error(
                format!(
                    "integer literal '{}' is out of range for type '{}'",
                    value,
                    ty.format(self.context)
                ),
                Some(span),
            );
        }
    }

    fn check_range(
        &mut self,
        pattern: &hir::Pattern,
        start: &hir::Expression,
        end: &hir::Expression,
        inclusive: bool,
        ty: crate::sema::models::Ty<'ctx>,
    ) {
        use super::utils::const_eval::integer_layout;
        use crate::sema::models::TyKind;
        let gcx = self.context;
        let ty = super::utils::normalize_aliases(gcx, ty);
        if !matches!(ty.kind(), TyKind::Rune) && integer_layout(gcx, ty).is_none() {
            gcx.dcx().emit_error(
                "range patterns require integers or runes".into(), Some(pattern.span),
            );
            return;
        }
        if let (Some(lo), Some(hi)) = (self.range_bound(start), self.range_bound(end)) {
            let range = lo..=if inclusive { hi } else { hi - 1 };
            if range.is_empty() {
                gcx.dcx().emit_error("range pattern is empty".into(), Some(pattern.span));
            } else {
                self.results.pattern_ranges.insert(pattern.id, range);
            }
        }
    }

    fn range_bound(&self, expr: &hir::Expression) -> Option<i128> {
        use super::utils::const_eval::eval_const_expression_with_type_results;
        use crate::sema::models::ConstValue;
        let gcx = self.context;
        if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &expr.kind
            && matches!(path.resolution, hir::Resolution::LocalVariable(_)
                | hir::Resolution::Definition(_, hir::DefinitionKind::ModuleVariable))
        {
            gcx.dcx().emit_error(
                "a range pattern bound must be a compile-time constant".into(), Some(expr.span),
            );
            return None;
        }
        match eval_const_expression_with_type_results(gcx, expr, self.results)? {
            ConstValue::Integer(i) => Some(i),
            ConstValue::Rune(r) => Some(r as i128),
            _ => {
                gcx.dcx().emit_error(
                    "range pattern bounds must be integer or rune constants".into(), Some(expr.span),
                );
                None
            }
        }
    }
}

impl HirVisitor for LiteralValidator<'_, '_> {
    fn visit_statement(&mut self, statement: &hir::Statement) {
        if matches!(
            statement.kind,
            hir::StatementKind::ComptimeFor { .. } | hir::StatementKind::ComptimeIf { .. }
        ) {
            if let Some(blocks) = self.results.comptime_expansions.get(&statement.id).cloned() {
                for block in &blocks {
                    hir::walk_block(self, block);
                }
            }
            return;
        }
        hir::walk_statement(self, statement);
    }

    fn visit_expression(&mut self, expression: &hir::Expression) {
        if let hir::ExpressionKind::Literal(literal) = &expression.kind {
            self.check(literal, expression.id, expression.span, false);
        }
        hir::walk_expression(self, expression);
    }

    fn visit_pattern(&mut self, pattern: &hir::Pattern) {
        if let hir::PatternKind::Literal { value } = &pattern.kind {
            self.check(value, pattern.id, pattern.span, true);
        }
        if let hir::PatternKind::Range { start, end, inclusive } = &pattern.kind
            && let Some(ty) = self.results.try_node_type(pattern.id)
        {
            self.check_range(pattern, start, end, *inclusive, ty);
        }
        hir::walk_pattern(self, pattern);
    }
}

struct Actor<'ctx> {
    context: Gcx<'ctx>,
    results: Rc<RefCell<TypeCheckResults<'ctx>>>,
    pending_mir_consts: Vec<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: Gcx<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            results: Rc::new(RefCell::new(TypeCheckResults::default())),
            pending_mir_consts: Vec::new(),
        }
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_declaration(&mut self, declaration: &hir::Declaration) -> Self::Result {
        match &declaration.kind {
            hir::DeclarationKind::Constant(node) => {
                self.check_constant(declaration.id, node);
                return;
            }
            hir::DeclarationKind::StaticVariable(node) => {
                self.check_static_variable(declaration.id, node);
                return;
            }
            _ => {}
        }
        hir::walk_declaration(self, declaration);
    }

    fn visit_assoc_declaration(
        &mut self,
        decl: &hir::AssociatedDeclaration,
        context: hir::AssocContext,
    ) {
        if let hir::AssociatedDeclarationKind::Constant(node) = &decl.kind {
            if node.expr.is_some() {
                self.check_constant(decl.id, node);
            }
            return;
        }
        hir::walk_assoc_declaration(self, decl, context);
    }

    fn visit_field_definition(&mut self, field: &hir::FieldDefinition) {
        if let Some(expression) = &field.default_value {
            let checker = checker::Checker::new(self.context, field.def_id, self.results.clone());
            let ty = super::lower::DefTyLoweringCtx::new(field.def_id, self.context)
                .lowerer()
                .lower_type(&field.ty);
            checker.top_level_check(expression, Some(ty));
        }
    }

    fn visit_function(
        &mut self,
        id: hir::DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        self.check_function(id, node, fn_ctx);
    }
}

impl<'ctx> Actor<'ctx> {
    fn check_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) {
        self.context.dcx().cancellation_point();
        let mut checker = checker::Checker::new(self.context, id, self.results.clone());
        checker.check_function(id, node, fn_ctx);
    }

    fn check_constant(&mut self, id: DefinitionID, node: &hir::Constant) {
        let mut checker = checker::Checker::new(self.context, id, self.results.clone());
        if checker.check_constant(id, node) {
            self.pending_mir_consts.push(id);
        }
    }

    fn check_static_variable(&mut self, id: DefinitionID, node: &hir::StaticVariable) {
        let mut checker = checker::Checker::new(self.context, id, self.results.clone());
        checker.check_static_variable(id, node);
    }
}
