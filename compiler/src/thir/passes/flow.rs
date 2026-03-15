//! Control-flow and definite-initialization checks over THIR.
use crate::{
    compile::context::GlobalContext,
    diagnostics::{Diagnostic, DiagnosticLevel},
    error::CompileResult,
    hir::{DefinitionID, NodeID},
    sema::models::{Ty, TyKind},
    span::{Span, Symbol},
    thir::{
        self, ArmId, BlockId, ExprId, ExprKind, Pattern, PatternKind, StmtId, StmtKind,
        ThirFunction, ThirPackage,
    },
};
use rustc_hash::{FxHashMap, FxHashSet};

type InitSet = FxHashSet<NodeID>;
type DiagnosticKey = (Span, String);

pub fn run<'ctx>(package: &mut ThirPackage<'ctx>, gcx: GlobalContext<'ctx>) -> CompileResult<()> {
    let mut pass = FlowPass::new(gcx);
    pass.check_package(package);
    Ok(())
}

struct FlowPass<'ctx> {
    gcx: GlobalContext<'ctx>,
    synthetic_definitions: FxHashSet<DefinitionID>,
    default_providers: FxHashSet<DefinitionID>,
}

impl<'ctx> FlowPass<'ctx> {
    fn new(gcx: GlobalContext<'ctx>) -> Self {
        let synthetic_definitions = gcx
            .store
            .synthetic_definitions
            .borrow()
            .keys()
            .copied()
            .collect();
        let default_providers = gcx
            .store
            .default_value_exprs
            .borrow()
            .keys()
            .copied()
            .collect();

        Self {
            gcx,
            synthetic_definitions,
            default_providers,
        }
    }

    fn check_package(&mut self, package: &ThirPackage<'ctx>) {
        let mut function_ids: Vec<_> = package.functions.keys().copied().collect();
        function_ids.sort();

        for function_id in function_ids {
            if self.synthetic_definitions.contains(&function_id)
                || self.default_providers.contains(&function_id)
            {
                continue;
            }

            let Some(function) = package.functions.get(&function_id) else {
                continue;
            };
            self.check_function(function);
        }
    }

    fn check_function(&mut self, function: &ThirFunction<'ctx>) {
        let Some(body) = function.body else {
            return;
        };

        let mut analyzer = FunctionAnalyzer::new(self.gcx, function);
        let initial = analyzer.initialized_params();
        let result = analyzer.analyze_block(body, &initial, 0, true);
        analyzer.check_function_completion(body, result);
    }
}

#[derive(Clone, Copy)]
struct LocalInfo {
    name: Symbol,
}

#[derive(Clone, Default)]
struct FlowResult {
    normal: Option<InitSet>,
    returns: Option<InitSet>,
    breaks: Option<InitSet>,
    continues: Option<InitSet>,
    poisoned: bool,
}

impl FlowResult {
    fn normal(initialized: InitSet) -> Self {
        Self {
            normal: Some(initialized),
            ..Default::default()
        }
    }

    fn terminated(poisoned: bool) -> Self {
        Self {
            poisoned,
            ..Default::default()
        }
    }

    fn with_break(initialized: InitSet) -> Self {
        Self {
            breaks: Some(initialized),
            ..Default::default()
        }
    }

    fn with_continue(initialized: InitSet) -> Self {
        Self {
            continues: Some(initialized),
            ..Default::default()
        }
    }
}

struct FunctionAnalyzer<'ctx, 'func> {
    gcx: GlobalContext<'ctx>,
    func: &'func ThirFunction<'ctx>,
    output_ty: Ty<'ctx>,
    local_infos: FxHashMap<NodeID, LocalInfo>,
    emitted_errors: FxHashSet<DiagnosticKey>,
    emitted_warnings: FxHashSet<DiagnosticKey>,
}

impl<'ctx, 'func> FunctionAnalyzer<'ctx, 'func> {
    fn new(gcx: GlobalContext<'ctx>, func: &'func ThirFunction<'ctx>) -> Self {
        let mut local_infos = FxHashMap::default();
        for param in &func.params {
            local_infos.insert(param.id, LocalInfo { name: param.name });
        }

        Self {
            gcx,
            func,
            output_ty: gcx.get_signature(func.id).output,
            local_infos,
            emitted_errors: FxHashSet::default(),
            emitted_warnings: FxHashSet::default(),
        }
    }

    fn initialized_params(&self) -> InitSet {
        self.func.params.iter().map(|param| param.id).collect()
    }

    fn check_function_completion(&mut self, body: BlockId, result: FlowResult) {
        if self.output_ty.is_error() || self.output_ty.is_infer() {
            return;
        }

        if matches!(self.output_ty.kind(), TyKind::Never) {
            if result.normal.is_some() {
                self.emit_error(
                    "function returning `!` cannot complete normally".to_string(),
                    self.func.span,
                );
            }
            return;
        }

        if self.output_ty != self.gcx.types.void
            && result.normal.is_some()
            && self.func.blocks[body].expr.is_none()
        {
            self.emit_error(
                format!(
                    "function with return type `{}` can complete without returning a value",
                    self.output_ty.format(self.gcx)
                ),
                self.func.span,
            );
        }
    }

    fn analyze_block(
        &mut self,
        block_id: BlockId,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let block = self.func.blocks[block_id].clone();
        let mut current = Some(initialized.clone());
        let mut result = FlowResult::default();
        let mut cleanups = Vec::new();

        for stmt_id in block.stmts {
            match current.clone() {
                Some(state) => {
                    let stmt = self.func.stmts[stmt_id].clone();
                    if let StmtKind::Defer(cleanup) = stmt.kind {
                        cleanups.push(cleanup);
                        continue;
                    }

                    let stmt_result =
                        self.analyze_stmt(stmt_id, &state, loop_depth, check_initialization);
                    self.merge_child_into(&mut result, stmt_result, &mut current);
                }
                None => {
                    if !result.poisoned {
                        self.warn_unreachable_stmt(stmt_id);
                    }
                }
            }
        }

        if let Some(expr_id) = block.expr {
            match current.clone() {
                Some(state) => {
                    let expr_result =
                        self.analyze_expr(expr_id, &state, loop_depth, check_initialization);
                    self.merge_child_into(&mut result, expr_result, &mut current);
                }
                None => {
                    if !result.poisoned {
                        self.warn_unreachable_expr(expr_id);
                    }
                }
            }
        }

        result.normal = current;
        self.apply_block_cleanups(result, &cleanups)
    }

    fn merge_child_into(
        &self,
        aggregate: &mut FlowResult,
        child: FlowResult,
        current: &mut Option<InitSet>,
    ) {
        aggregate.returns = merge_exit_states(aggregate.returns.take(), child.returns);
        aggregate.breaks = merge_exit_states(aggregate.breaks.take(), child.breaks);
        aggregate.continues = merge_exit_states(aggregate.continues.take(), child.continues);
        aggregate.poisoned |= child.poisoned;
        *current = child.normal;
    }

    fn apply_block_cleanups(&mut self, mut result: FlowResult, cleanups: &[BlockId]) -> FlowResult {
        for &cleanup in cleanups.iter().rev() {
            result.normal =
                self.apply_cleanup_to_exit(result.normal.take(), cleanup, &mut result.poisoned);
            result.returns =
                self.apply_cleanup_to_exit(result.returns.take(), cleanup, &mut result.poisoned);
            result.breaks =
                self.apply_cleanup_to_exit(result.breaks.take(), cleanup, &mut result.poisoned);
            result.continues =
                self.apply_cleanup_to_exit(result.continues.take(), cleanup, &mut result.poisoned);
        }
        result
    }

    fn apply_cleanup_to_exit(
        &mut self,
        state: Option<InitSet>,
        cleanup: BlockId,
        poisoned: &mut bool,
    ) -> Option<InitSet> {
        let Some(state) = state else {
            return None;
        };

        let cleanup_result = self.analyze_block(cleanup, &state, 0, true);
        *poisoned |= cleanup_result.poisoned;

        if cleanup_result.returns.is_some()
            || cleanup_result.breaks.is_some()
            || cleanup_result.continues.is_some()
        {
            *poisoned = true;
        }

        cleanup_result.normal
    }

    fn analyze_stmt(
        &mut self,
        stmt_id: StmtId,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let stmt = self.func.stmts[stmt_id].clone();

        match stmt.kind {
            StmtKind::Let { pattern, expr, .. } => {
                let binding_ids = self.pattern_binding_ids(&pattern);

                if let Some(expr_id) = expr {
                    let mut result =
                        self.analyze_expr(expr_id, initialized, loop_depth, check_initialization);
                    if let Some(normal) = result.normal.as_mut() {
                        for binding_id in binding_ids {
                            normal.insert(binding_id);
                        }
                    }
                    return result;
                }

                if Self::pattern_requires_initializer(&pattern) {
                    self.emit_error(
                        "destructuring declaration requires an initializer".to_string(),
                        pattern.span,
                    );
                }

                FlowResult::normal(initialized.clone())
            }
            StmtKind::Return { value } => self.analyze_return(
                value,
                stmt.span,
                initialized,
                loop_depth,
                check_initialization,
            ),
            StmtKind::Break => {
                if loop_depth == 0 {
                    FlowResult::terminated(true)
                } else {
                    FlowResult::with_break(initialized.clone())
                }
            }
            StmtKind::Continue => {
                if loop_depth == 0 {
                    FlowResult::terminated(true)
                } else {
                    FlowResult::with_continue(initialized.clone())
                }
            }
            StmtKind::Defer(..) => FlowResult::normal(initialized.clone()),
            StmtKind::Loop { block } => {
                self.analyze_loop(block, initialized, loop_depth, check_initialization)
            }
            StmtKind::Expr(expr_id) => {
                self.analyze_expr(expr_id, initialized, loop_depth, check_initialization)
            }
        }
    }

    fn analyze_loop(
        &mut self,
        block: BlockId,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let mut entry_state = initialized.clone();

        loop {
            let body_result =
                self.analyze_block(block, &entry_state, loop_depth + 1, check_initialization);
            let backedge_state =
                merge_exit_states(body_result.normal.clone(), body_result.continues.clone());
            let next_entry = merge_exit_states(Some(initialized.clone()), backedge_state)
                .expect("loop entry state should always include the initial entry");

            if next_entry == entry_state {
                return FlowResult {
                    normal: body_result.breaks,
                    returns: body_result.returns,
                    breaks: None,
                    continues: None,
                    poisoned: body_result.poisoned,
                };
            }

            entry_state = next_entry;
        }
    }

    fn analyze_return(
        &mut self,
        value: Option<ExprId>,
        span: Span,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        if value.is_none() && self.return_value_required() {
            self.emit_error(
                "`return` without a value is only allowed in functions returning `()`".to_string(),
                span,
            );
        }

        let result = if let Some(value) = value {
            self.analyze_expr(value, initialized, loop_depth, check_initialization)
        } else {
            FlowResult::normal(initialized.clone())
        };

        let returns = merge_exit_states(result.returns, result.normal);

        FlowResult {
            normal: None,
            returns,
            breaks: result.breaks,
            continues: result.continues,
            poisoned: result.poisoned,
        }
    }

    fn analyze_expr(
        &mut self,
        expr_id: ExprId,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let expr = self.func.exprs[expr_id].clone();

        match expr.kind {
            ExprKind::Local(id) => {
                if check_initialization && !initialized.contains(&id) {
                    self.emit_error(self.uninitialized_local_message(id), expr.span);
                }
                FlowResult::normal(initialized.clone())
            }
            ExprKind::Reference { expr, .. } => {
                self.analyze_expr(expr, initialized, loop_depth, check_initialization)
            }
            ExprKind::Deref(expr)
            | ExprKind::Unary { operand: expr, .. }
            | ExprKind::Cast { value: expr }
            | ExprKind::ExistentialTryCast { value: expr, .. }
            | ExprKind::ExistentialTypeIs { value: expr, .. }
            | ExprKind::BoxExistential { value: expr, .. }
            | ExprKind::ExistentialUpcast { value: expr, .. }
            | ExprKind::Make { value: expr }
            | ExprKind::Field { lhs: expr, .. }
            | ExprKind::ClosureToFnPointer { closure: expr, .. } => {
                self.analyze_expr(expr, initialized, loop_depth, check_initialization)
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => self.analyze_if(
                cond,
                then_expr,
                else_expr,
                initialized,
                loop_depth,
                check_initialization,
            ),
            ExprKind::Return { value } => self.analyze_return(
                value,
                expr.span,
                initialized,
                loop_depth,
                check_initialization,
            ),
            ExprKind::Break => {
                if loop_depth == 0 {
                    FlowResult::terminated(true)
                } else {
                    FlowResult::with_break(initialized.clone())
                }
            }
            ExprKind::Continue => {
                if loop_depth == 0 {
                    FlowResult::terminated(true)
                } else {
                    FlowResult::with_continue(initialized.clone())
                }
            }
            ExprKind::Assign { target, value } => {
                self.analyze_assign(target, value, initialized, loop_depth, check_initialization)
            }
            ExprKind::AssignOp { target, value, .. } => self.analyze_expr_sequence(
                [target, value],
                initialized,
                loop_depth,
                check_initialization,
            ),
            ExprKind::Literal(..) | ExprKind::Zst { .. } | ExprKind::Upvar { .. } => {
                FlowResult::normal(initialized.clone())
            }
            ExprKind::Array { elements }
            | ExprKind::ListLiteral { elements, .. }
            | ExprKind::Tuple { fields: elements } => {
                self.analyze_expr_sequence(elements, initialized, loop_depth, check_initialization)
            }
            ExprKind::Repeat { element, .. } => {
                self.analyze_expr(element, initialized, loop_depth, check_initialization)
            }
            ExprKind::Binary { lhs, rhs, .. } => self.analyze_expr_sequence(
                [lhs, rhs],
                initialized,
                loop_depth,
                check_initialization,
            ),
            ExprKind::Logical { lhs, rhs, .. } => {
                self.analyze_logical(lhs, rhs, initialized, loop_depth, check_initialization)
            }
            ExprKind::Call { callee, args } => {
                self.analyze_call(callee, args, initialized, loop_depth, check_initialization)
            }
            ExprKind::Block(block) => {
                self.analyze_block(block, initialized, loop_depth, check_initialization)
            }
            ExprKind::Adt(adt) => self.analyze_expr_sequence(
                adt.fields.into_iter().map(|field| field.expression),
                initialized,
                loop_depth,
                check_initialization,
            ),
            ExprKind::Match {
                scrutinee, arms, ..
            } => self.analyze_match(
                scrutinee,
                arms,
                initialized,
                loop_depth,
                check_initialization,
            ),
            ExprKind::Closure { captures, .. } => self.analyze_expr_sequence(
                captures.into_iter().map(|capture| capture.capture_expr),
                initialized,
                loop_depth,
                check_initialization,
            ),
        }
    }

    fn analyze_if(
        &mut self,
        cond: ExprId,
        then_expr: ExprId,
        else_expr: Option<ExprId>,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let cond_result = self.analyze_expr(cond, initialized, loop_depth, check_initialization);
        let mut result = FlowResult {
            returns: cond_result.returns,
            breaks: cond_result.breaks,
            continues: cond_result.continues,
            poisoned: cond_result.poisoned,
            ..Default::default()
        };

        let Some(cond_state) = cond_result.normal else {
            if !result.poisoned {
                self.warn_unreachable_expr(then_expr);
                if let Some(else_expr) = else_expr {
                    self.warn_unreachable_expr(else_expr);
                }
            }
            return result;
        };

        let then_state = self
            .pattern_binding_then_state(cond, &cond_state)
            .unwrap_or_else(|| cond_state.clone());
        let then_result =
            self.analyze_expr(then_expr, &then_state, loop_depth, check_initialization);
        let else_result = if let Some(else_expr) = else_expr {
            self.analyze_expr(else_expr, &cond_state, loop_depth, check_initialization)
        } else {
            FlowResult::normal(cond_state)
        };

        let branch_result = merge_results(then_result, else_result);
        result.normal = branch_result.normal;
        result.returns = merge_exit_states(result.returns.take(), branch_result.returns);
        result.breaks = merge_exit_states(result.breaks.take(), branch_result.breaks);
        result.continues = merge_exit_states(result.continues.take(), branch_result.continues);
        result.poisoned |= branch_result.poisoned;
        result
    }

    fn analyze_assign(
        &mut self,
        target: ExprId,
        value: ExprId,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let target_local = match self.func.exprs[target].kind {
            ExprKind::Local(id) => Some(id),
            _ => None,
        };

        let mut result = FlowResult::default();
        let value_input = if target_local.is_some() {
            initialized.clone()
        } else {
            let target_result =
                self.analyze_expr(target, initialized, loop_depth, check_initialization);
            result.returns = target_result.returns;
            result.breaks = target_result.breaks;
            result.continues = target_result.continues;
            result.poisoned = target_result.poisoned;

            let Some(target_state) = target_result.normal else {
                if !result.poisoned {
                    self.warn_unreachable_expr(value);
                }
                return result;
            };

            target_state
        };

        let value_result = self.analyze_expr(value, &value_input, loop_depth, check_initialization);
        result.returns = merge_exit_states(result.returns.take(), value_result.returns);
        result.breaks = merge_exit_states(result.breaks.take(), value_result.breaks);
        result.continues = merge_exit_states(result.continues.take(), value_result.continues);
        result.poisoned |= value_result.poisoned;
        result.normal = value_result.normal.map(|mut state| {
            if let Some(local) = target_local {
                state.insert(local);
            }
            state
        });
        result
    }

    fn analyze_logical(
        &mut self,
        lhs: ExprId,
        rhs: ExprId,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let lhs_result = self.analyze_expr(lhs, initialized, loop_depth, check_initialization);
        let mut result = FlowResult {
            returns: lhs_result.returns,
            breaks: lhs_result.breaks,
            continues: lhs_result.continues,
            poisoned: lhs_result.poisoned,
            ..Default::default()
        };

        let Some(lhs_state) = lhs_result.normal else {
            if !result.poisoned {
                self.warn_unreachable_expr(rhs);
            }
            return result;
        };

        let rhs_result = self.analyze_expr(rhs, &lhs_state, loop_depth, check_initialization);
        let branch_result = merge_results(FlowResult::normal(lhs_state), rhs_result);

        result.normal = branch_result.normal;
        result.returns = merge_exit_states(result.returns.take(), branch_result.returns);
        result.breaks = merge_exit_states(result.breaks.take(), branch_result.breaks);
        result.continues = merge_exit_states(result.continues.take(), branch_result.continues);
        result.poisoned |= branch_result.poisoned;
        result
    }

    fn analyze_call(
        &mut self,
        callee: ExprId,
        args: Vec<ExprId>,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let sequence = std::iter::once(callee).chain(args.iter().copied());
        let mut result =
            self.analyze_expr_sequence(sequence, initialized, loop_depth, check_initialization);
        if result.normal.is_some() && self.call_output_is_never(callee) {
            result.normal = None;
        }
        result
    }

    fn analyze_match(
        &mut self,
        scrutinee: ExprId,
        arms: Vec<ArmId>,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult {
        let scrutinee_result =
            self.analyze_expr(scrutinee, initialized, loop_depth, check_initialization);
        let mut result = FlowResult {
            returns: scrutinee_result.returns,
            breaks: scrutinee_result.breaks,
            continues: scrutinee_result.continues,
            poisoned: scrutinee_result.poisoned,
            ..Default::default()
        };

        let Some(scrutinee_state) = scrutinee_result.normal else {
            return result;
        };

        let mut reachable_arms: Option<FxHashSet<ArmId>> = None;
        let mut missing = false;
        let scrutinee_ty = self.func.exprs[scrutinee].ty;
        let arms_have_type_errors = arms.iter().any(|arm_id| {
            matches!(
                self.func.arms[*arm_id].pattern.ty.kind(),
                TyKind::Error | TyKind::Infer(_)
            )
        });

        if !matches!(scrutinee_ty.kind(), TyKind::Error | TyKind::Infer(_))
            && !arms_have_type_errors
        {
            let report = thir::match_tree::compile_match(self.gcx, self.func, scrutinee, &arms);
            missing = report.diagnostics.missing;
            reachable_arms = Some(report.diagnostics.reachable.into_iter().collect());
        }

        let mut arm_result = FlowResult::default();

        for arm_id in arms {
            if let Some(reachable) = &reachable_arms
                && !reachable.contains(&arm_id)
            {
                continue;
            }

            let arm = self.func.arms[arm_id].clone();
            let mut arm_state = scrutinee_state.clone();
            for binding_id in self.pattern_binding_ids(&arm.pattern) {
                arm_state.insert(binding_id);
            }

            let body_input = if let Some(guard) = arm.guard {
                let guard_result =
                    self.analyze_expr(guard, &arm_state, loop_depth, check_initialization);
                arm_result = merge_results(
                    arm_result,
                    FlowResult {
                        normal: None,
                        returns: guard_result.returns.clone(),
                        breaks: guard_result.breaks.clone(),
                        continues: guard_result.continues.clone(),
                        poisoned: guard_result.poisoned,
                    },
                );

                match guard_result.normal {
                    Some(guard_state) => guard_state,
                    None => {
                        if !guard_result.poisoned {
                            self.warn_unreachable_expr(arm.body);
                        }
                        continue;
                    }
                }
            } else {
                arm_state
            };

            let body_result =
                self.analyze_expr(arm.body, &body_input, loop_depth, check_initialization);
            arm_result = merge_results(arm_result, body_result);
        }

        if missing {
            result.poisoned = true;
            return result;
        }

        result.normal = arm_result.normal;
        result.returns = merge_exit_states(result.returns.take(), arm_result.returns);
        result.breaks = merge_exit_states(result.breaks.take(), arm_result.breaks);
        result.continues = merge_exit_states(result.continues.take(), arm_result.continues);
        result.poisoned |= arm_result.poisoned;
        result
    }

    fn analyze_expr_sequence<I>(
        &mut self,
        exprs: I,
        initialized: &InitSet,
        loop_depth: usize,
        check_initialization: bool,
    ) -> FlowResult
    where
        I: IntoIterator<Item = ExprId>,
    {
        let mut current = Some(initialized.clone());
        let mut result = FlowResult::default();

        for expr_id in exprs {
            match current.clone() {
                Some(state) => {
                    let expr_result =
                        self.analyze_expr(expr_id, &state, loop_depth, check_initialization);
                    self.merge_child_into(&mut result, expr_result, &mut current);
                }
                None => {
                    if !result.poisoned {
                        self.warn_unreachable_expr(expr_id);
                    }
                }
            }
        }

        result.normal = current;
        result
    }

    fn pattern_binding_ids(&mut self, pattern: &Pattern<'ctx>) -> Vec<NodeID> {
        let mut binding_ids = Vec::new();
        let mut seen = FxHashSet::default();
        self.collect_pattern_bindings(pattern, &mut binding_ids, &mut seen);
        binding_ids
    }

    fn collect_pattern_bindings(
        &mut self,
        pattern: &Pattern<'ctx>,
        binding_ids: &mut Vec<NodeID>,
        seen: &mut FxHashSet<NodeID>,
    ) {
        match &pattern.kind {
            PatternKind::Wild | PatternKind::Constant { .. } => {}
            PatternKind::Binding { name, local, .. } => {
                self.local_infos
                    .entry(*local)
                    .or_insert(LocalInfo { name: *name });
                if seen.insert(*local) {
                    binding_ids.push(*local);
                }
            }
            PatternKind::Deref { pattern } => {
                self.collect_pattern_bindings(pattern, binding_ids, seen);
            }
            PatternKind::Leaf { subpatterns } | PatternKind::Variant { subpatterns, .. } => {
                for field in subpatterns {
                    self.collect_pattern_bindings(&field.pattern, binding_ids, seen);
                }
            }
            PatternKind::Or(patterns) => {
                for pattern in patterns {
                    self.collect_pattern_bindings(pattern, binding_ids, seen);
                }
            }
        }
    }

    fn call_output_is_never(&self, callee: ExprId) -> bool {
        self.call_output_ty(callee)
            .is_some_and(|output| matches!(output.kind(), TyKind::Never))
    }

    fn pattern_binding_then_state(
        &mut self,
        cond: ExprId,
        initialized: &InitSet,
    ) -> Option<InitSet> {
        let ExprKind::Match {
            arms,
            binding_condition: true,
            ..
        } = &self.func.exprs[cond].kind
        else {
            return None;
        };

        let success_arm = arms.iter().copied().find(|arm_id| {
            let body = self.func.arms[*arm_id].body;
            matches!(
                self.func.exprs[body].kind,
                ExprKind::Literal(crate::thir::Constant {
                    value: crate::thir::ConstantKind::Bool(true),
                    ..
                })
            )
        })?;

        let mut then_state = initialized.clone();
        for binding_id in self.pattern_binding_ids(&self.func.arms[success_arm].pattern) {
            then_state.insert(binding_id);
        }
        Some(then_state)
    }

    fn call_output_ty(&self, callee: ExprId) -> Option<Ty<'ctx>> {
        let expr = &self.func.exprs[callee];

        match &expr.kind {
            ExprKind::Zst { id, .. } => Some(self.gcx.get_signature(*id).output),
            ExprKind::Closure { def_id, .. } => Some(self.gcx.get_signature(*def_id).output),
            ExprKind::ClosureToFnPointer { closure_def_id, .. } => {
                Some(self.gcx.get_signature(*closure_def_id).output)
            }
            _ => match expr.ty.kind() {
                TyKind::FnPointer { output, .. } | TyKind::Closure { output, .. } => Some(output),
                _ => None,
            },
        }
    }

    fn return_value_required(&self) -> bool {
        self.output_ty != self.gcx.types.void
            && !matches!(self.output_ty.kind(), TyKind::Error | TyKind::Infer(_))
    }

    fn uninitialized_local_message(&self, id: NodeID) -> String {
        if let Some(info) = self.local_infos.get(&id) {
            return format!(
                "use of uninitialized local '{}'",
                self.gcx.symbol_text(info.name)
            );
        }

        "use of uninitialized local".to_string()
    }

    fn emit_error(&mut self, message: String, span: Span) {
        let key = (span, message.clone());
        if !self.emitted_errors.insert(key) {
            return;
        }

        self.gcx
            .dcx()
            .emit(Diagnostic::new(message, Some(span), DiagnosticLevel::Error));
    }

    fn warn_unreachable_stmt(&mut self, stmt_id: StmtId) {
        let span = self.func.stmts[stmt_id].span;
        self.emit_warning_once("unreachable statement".to_string(), span);
    }

    fn warn_unreachable_expr(&mut self, expr_id: ExprId) {
        let span = self.func.exprs[expr_id].span;
        self.emit_warning_once("unreachable expression".to_string(), span);
    }

    fn emit_warning_once(&mut self, message: String, span: Span) {
        let key = (span, message.clone());
        if !self.emitted_warnings.insert(key) {
            return;
        }

        self.gcx
            .dcx()
            .emit(Diagnostic::new(message, Some(span), DiagnosticLevel::Warn));
    }

    fn pattern_requires_initializer(pattern: &Pattern<'ctx>) -> bool {
        !matches!(
            pattern.kind,
            PatternKind::Wild | PatternKind::Binding { .. }
        )
    }
}

fn merge_results(lhs: FlowResult, rhs: FlowResult) -> FlowResult {
    FlowResult {
        normal: merge_exit_states(lhs.normal, rhs.normal),
        returns: merge_exit_states(lhs.returns, rhs.returns),
        breaks: merge_exit_states(lhs.breaks, rhs.breaks),
        continues: merge_exit_states(lhs.continues, rhs.continues),
        poisoned: lhs.poisoned || rhs.poisoned,
    }
}

fn merge_exit_states(lhs: Option<InitSet>, rhs: Option<InitSet>) -> Option<InitSet> {
    match (lhs, rhs) {
        (Some(lhs), Some(rhs)) => Some(intersect_pair(lhs, rhs)),
        (Some(lhs), None) => Some(lhs),
        (None, Some(rhs)) => Some(rhs),
        (None, None) => None,
    }
}

fn intersect_pair(lhs: InitSet, rhs: InitSet) -> InitSet {
    let mut intersection = lhs;
    intersection.retain(|local| rhs.contains(local));
    intersection
}
