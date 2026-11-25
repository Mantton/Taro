//! Restricted MIR interpreter for compile-time evaluation of `const` items and
//! `const func` calls (TAR-50).
//!
//! Supports scalar and fixed-size array values, local mutation, bounded loops,
//! checked integer arithmetic, bitwise/logical/comparison operations, numeric
//! casts, nested `const func` calls, and fixed-size array indexing (`[]`, `at`,
//! `set`, `len`). Enforces a deterministic step limit and call-depth limit, and
//! emits source-level diagnostics naming any unsupported operation or non-const
//! call.

use crate::{
    compile::context::Gcx,
    error::{CompileResult, ReportedError},
    hir::{self, DefinitionID, HirVisitor},
    mir::{
        AggregateKind, BinaryOperator, Body, CastKind, ConstantKind, LocalId, Operand, Place,
        PlaceElem, Rvalue, StatementKind, TerminatorKind, UnaryOperator, builder::MirBuilder,
    },
    sema::{
        models::{Const, ConstKind, ConstValue, FloatTy, Ty, TyKind},
        tycheck::{
            results::TypeCheckResults,
            utils::{
                const_eval::{IntegerLayout, integer_layout},
                normalize_aliases,
            },
        },
    },
    span::{InternedBytes, Span, Symbol},
};
use rustc_hash::{FxHashMap, FxHashSet};
use std::{cell::RefCell, rc::Rc};

/// Maximum number of MIR statements + terminators executed during a single
/// compile-time constant evaluation before diagnosing possible nontermination.
pub const CONST_EVAL_STEP_LIMIT: usize = 500_000;

/// Maximum nested call depth during compile-time evaluation.
pub const CONST_EVAL_CALL_DEPTH_LIMIT: usize = 64;

#[derive(Debug, Clone)]
enum InterpProj {
    Field(usize),
    Index(usize),
}

#[derive(Debug, Clone)]
enum InterpVal {
    Uninit,
    Unit,
    Bool(bool),
    Rune(char),
    Int(i128),
    Float(f64),
    String(Symbol),
    Bytes(InternedBytes),
    Array(Vec<InterpVal>),
    Tuple(Vec<InterpVal>),
    Adt {
        variant: Option<usize>,
        fields: Vec<InterpVal>,
    },
    EnumUnitVariant(DefinitionID),
    Ref {
        frame: usize,
        local: LocalId,
        path: Vec<InterpProj>,
    },
}

struct Frame {
    locals: Vec<InterpVal>,
}

struct PackageConstIndex<'hir> {
    functions: FxHashMap<DefinitionID, (&'hir hir::Function, hir::FunctionContext)>,
    constants: FxHashMap<DefinitionID, &'hir hir::Constant>,
}

impl<'hir> PackageConstIndex<'hir> {
    fn empty() -> Self {
        Self {
            functions: FxHashMap::default(),
            constants: FxHashMap::default(),
        }
    }

    fn build(package: &'hir hir::Package) -> Self {
        let mut index = Self {
            functions: FxHashMap::default(),
            constants: FxHashMap::default(),
        };
        index.visit_module(&package.root);
        index
    }

    fn visit_module(&mut self, module: &'hir hir::Module) {
        for decl in &module.declarations {
            match &decl.kind {
                hir::DeclarationKind::Function(func) => {
                    self.functions
                        .insert(decl.id, (func, hir::FunctionContext::Free));
                }
                hir::DeclarationKind::Constant(c) => {
                    self.constants.insert(decl.id, c);
                }
                hir::DeclarationKind::Namespace(ns) => {
                    for sub in &ns.declarations {
                        self.visit_decl(sub);
                    }
                }
                hir::DeclarationKind::Impl(imp) => {
                    for assoc in &imp.declarations {
                        match &assoc.kind {
                            hir::AssociatedDeclarationKind::Function(func) => {
                                self.functions.insert(
                                    assoc.id,
                                    (
                                        func,
                                        hir::FunctionContext::Assoc(hir::AssocContext::Impl(
                                            decl.id,
                                        )),
                                    ),
                                );
                            }
                            hir::AssociatedDeclarationKind::Constant(c) => {
                                self.constants.insert(assoc.id, c);
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
        for sub in &module.submodules {
            self.visit_module(sub);
        }
    }

    fn visit_decl(&mut self, decl: &'hir hir::Declaration) {
        match &decl.kind {
            hir::DeclarationKind::Function(func) => {
                self.functions
                    .insert(decl.id, (func, hir::FunctionContext::Free));
            }
            hir::DeclarationKind::Constant(c) => {
                self.constants.insert(decl.id, c);
            }
            hir::DeclarationKind::Namespace(ns) => {
                for sub in &ns.declarations {
                    self.visit_decl(sub);
                }
            }
            hir::DeclarationKind::Impl(imp) => {
                for assoc in &imp.declarations {
                    match &assoc.kind {
                        hir::AssociatedDeclarationKind::Function(func) => {
                            self.functions.insert(
                                assoc.id,
                                (
                                    func,
                                    hir::FunctionContext::Assoc(hir::AssocContext::Impl(decl.id)),
                                ),
                            );
                        }
                        hir::AssociatedDeclarationKind::Constant(c) => {
                            self.constants.insert(assoc.id, c);
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
    }
}

/// Evaluate all deferred constant items in `package` whose initializers require
/// MIR-level compile-time evaluation (calls to `const func`, array literals,
/// indexing, blocks, etc.).
pub fn eval_package_const_items<'ctx>(
    package: &hir::Package,
    gcx: Gcx<'ctx>,
    results: Rc<TypeCheckResults<'ctx>>,
    const_ids: &[DefinitionID],
) {
    if const_ids.is_empty() {
        return;
    }
    let index = PackageConstIndex::build(package);
    let mut evaluator = ConstMirEvaluator {
        gcx,
        results: Rc::new(RefCell::new((*results).clone())),
        index,
        on_demand: false,
        checked_fns: FxHashSet::default(),
        fn_mir_cache: FxHashMap::default(),
        evaluating_consts: FxHashSet::default(),
        failed_consts: FxHashSet::default(),
    };
    for &id in const_ids {
        let _ = evaluator.eval_const_item(id);
    }
}

/// Evaluate a single constant expression on demand during type lowering or early
/// constant evaluation (for example `[T; size()]`, const generic arguments, or
/// `const N: usize = size()` used as an array length).
pub fn eval_const_expr_on_demand<'ctx>(
    gcx: Gcx<'ctx>,
    owner_id: DefinitionID,
    expr: &hir::Expression,
    expected: Option<Ty<'ctx>>,
) -> Option<ConstValue> {
    let results = Rc::new(RefCell::new(TypeCheckResults::default()));
    let errors_before = gcx.dcx().error_count();
    let provided = crate::sema::tycheck::check_const_expr_on_demand(
        gcx,
        owner_id,
        expr,
        expected,
        results.clone(),
    );
    if provided.is_error() || gcx.dcx().error_count() > errors_before {
        return None;
    }
    let target_ty = expected.unwrap_or(provided);
    let mut evaluator = ConstMirEvaluator {
        gcx,
        results,
        index: PackageConstIndex::empty(),
        on_demand: true,
        checked_fns: FxHashSet::default(),
        fn_mir_cache: FxHashMap::default(),
        evaluating_consts: FxHashSet::default(),
        failed_consts: FxHashSet::default(),
    };
    evaluator.eval_referenced_consts(expr);
    let results_snapshot = Rc::new(evaluator.results.borrow().clone());
    let thir_fn = crate::thir::package::lower_const_initializer(
        gcx,
        results_snapshot,
        owner_id,
        expr,
        target_ty,
    )
    .ok()?;
    let mir_body = MirBuilder::build_const_initializer(gcx, &thir_fn, target_ty);
    let mut machine = InterpMachine {
        evaluator: &mut evaluator,
        frames: Vec::new(),
        steps: 0,
        root_span: expr.span,
    };
    let evaluated = machine.eval_body(&mir_body, Vec::new(), expr.span).ok()?;
    evaluator
        .interp_to_const_value(&evaluated, target_ty, expr.span)
        .ok()
}

/// Returns `true` if `expr` uses constructs that should be evaluated by the
/// post-typecheck restricted MIR interpreter rather than the early scalar HIR
/// evaluator.
pub fn hir_expr_needs_mir_const_eval(expr: &hir::Expression) -> bool {
    struct Detector {
        needs: bool,
    }
    impl HirVisitor for Detector {
        fn visit_expression(&mut self, expr: &hir::Expression) {
            if self.needs {
                return;
            }
            match &expr.kind {
                hir::ExpressionKind::Call { callee, .. } => {
                    let is_function_call = matches!(
                        &callee.kind,
                        hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                            if matches!(
                                path.resolution,
                                hir::Resolution::Definition(
                                    _,
                                    hir::DefinitionKind::Function
                                        | hir::DefinitionKind::AssociatedFunction
                                )
                            )
                    );
                    if is_function_call {
                        self.needs = true;
                    }
                }
                hir::ExpressionKind::MethodCall { .. }
                | hir::ExpressionKind::Index { .. }
                | hir::ExpressionKind::Array(_)
                | hir::ExpressionKind::Repeat { .. }
                | hir::ExpressionKind::Loop { .. }
                | hir::ExpressionKind::Match(_)
                | hir::ExpressionKind::Assign(..)
                | hir::ExpressionKind::AssignOp(..) => {
                    self.needs = true;
                }
                hir::ExpressionKind::Block(block) => {
                    if !block.statements.is_empty() {
                        self.needs = true;
                    } else if let Some(tail) = &block.tail {
                        self.visit_expression(tail);
                    }
                }
                _ => hir::walk_expression(self, expr),
            }
        }
    }
    let mut detector = Detector { needs: false };
    detector.visit_expression(expr);
    detector.needs
}

struct ConstMirEvaluator<'hir, 'ctx> {
    gcx: Gcx<'ctx>,
    results: Rc<RefCell<TypeCheckResults<'ctx>>>,
    index: PackageConstIndex<'hir>,
    on_demand: bool,
    checked_fns: FxHashSet<DefinitionID>,
    fn_mir_cache: FxHashMap<DefinitionID, Rc<Body<'ctx>>>,
    evaluating_consts: FxHashSet<DefinitionID>,
    failed_consts: FxHashSet<DefinitionID>,
}

impl<'hir, 'ctx> ConstMirEvaluator<'hir, 'ctx> {
    fn eval_const_item(&mut self, id: DefinitionID) -> Option<ConstValue> {
        if let Some(cached) = self.gcx.try_get_const(id) {
            return match cached.kind {
                ConstKind::Value(v) => Some(v),
                _ => None,
            };
        }
        if let Some(crate::compile::context::ConstEvaluationState::Evaluated(v)) =
            self.gcx.const_evaluation_state(id)
        {
            let expected = self.gcx.get_type(id);
            self.gcx.cache_const(
                id,
                Const {
                    ty: expected,
                    kind: ConstKind::Value(v),
                },
            );
            return Some(v);
        }
        if self.failed_consts.contains(&id) {
            return None;
        }
        let node = self
            .index
            .constants
            .get(&id)
            .copied()
            .or_else(|| self.gcx.const_definition(id))?;
        let Some(expr) = node.expr.as_deref() else {
            return None;
        };
        if !self.evaluating_consts.insert(id) {
            let name = self.gcx.symbol_text(self.gcx.definition_ident(id).symbol);
            self.gcx.dcx().emit_error(
                format!("circular constant dependency involving '{name}'"),
                Some(expr.span),
            );
            self.failed_consts.insert(id);
            return None;
        }

        // First ensure any other pending package constants referenced by this
        // expression are evaluated before lowering to THIR/MIR.
        self.eval_referenced_consts(expr);

        let expected = self.gcx.get_type(id);
        if self.on_demand {
            let errors_before = self.gcx.dcx().error_count();
            let provided = crate::sema::tycheck::check_const_expr_on_demand(
                self.gcx,
                id,
                expr,
                Some(expected),
                self.results.clone(),
            );
            if provided.is_error() || self.gcx.dcx().error_count() > errors_before {
                self.evaluating_consts.remove(&id);
                self.failed_consts.insert(id);
                return None;
            }
        }
        let results_snapshot = Rc::new(self.results.borrow().clone());
        let Ok(thir_fn) = crate::thir::package::lower_const_initializer(
            self.gcx,
            results_snapshot,
            id,
            expr,
            expected,
        ) else {
            self.evaluating_consts.remove(&id);
            self.failed_consts.insert(id);
            return None;
        };
        let mir_body = MirBuilder::build_const_initializer(self.gcx, &thir_fn, expected);

        let mut machine = InterpMachine {
            evaluator: self,
            frames: Vec::new(),
            steps: 0,
            root_span: expr.span,
        };
        let evaluated = machine.eval_body(&mir_body, Vec::new(), expr.span);
        self.evaluating_consts.remove(&id);

        match evaluated {
            Ok(interp_val) => {
                match self.interp_to_const_value(&interp_val, expected, expr.span) {
                    Ok(const_val) => {
                        self.gcx.cache_const(
                            id,
                            Const {
                                ty: expected,
                                kind: ConstKind::Value(const_val),
                            },
                        );
                        Some(const_val)
                    }
                    Err(ReportedError) => {
                        self.failed_consts.insert(id);
                        None
                    }
                }
            }
            Err(ReportedError) => {
                self.failed_consts.insert(id);
                None
            }
        }
    }

    fn eval_referenced_consts(&mut self, expr: &hir::Expression) {
        struct Collector {
            defs: Vec<DefinitionID>,
        }
        impl HirVisitor for Collector {
            fn visit_expression(&mut self, expr: &hir::Expression) {
                if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &expr.kind
                    && let hir::Resolution::Definition(
                        id,
                        hir::DefinitionKind::Constant | hir::DefinitionKind::AssociatedConstant,
                    ) = path.resolution
                {
                    self.defs.push(id);
                }
                hir::walk_expression(self, expr);
            }
        }
        let mut collector = Collector { defs: Vec::new() };
        collector.visit_expression(expr);
        for def_id in collector.defs {
            if self.gcx.try_get_const(def_id).is_none()
                && (self.index.constants.contains_key(&def_id)
                    || self.gcx.const_definition(def_id).is_some())
            {
                let _ = self.eval_const_item(def_id);
            }
        }
    }

    fn get_or_build_const_fn_mir(
        &mut self,
        id: DefinitionID,
    ) -> CompileResult<Option<Rc<Body<'ctx>>>> {
        if let Some(cached) = self.fn_mir_cache.get(&id) {
            return Ok(Some(cached.clone()));
        }
        if id.package() != self.gcx.package_index() {
            let Some(body) = self
                .gcx
                .store
                .inline_mir_packages
                .borrow()
                .get(&id.package())
                .and_then(|pkg| pkg.functions.get(&id).copied())
                .or_else(|| {
                    self.gcx
                        .store
                        .mir_packages
                        .borrow()
                        .get(&id.package())
                        .and_then(|pkg| pkg.functions.get(&id).copied())
                })
            else {
                return Ok(None);
            };
            let body = Rc::new((*body).clone());
            self.fn_mir_cache.insert(id, body.clone());
            return Ok(Some(body));
        }
        let Some((func, fn_ctx)) = self
            .index
            .functions
            .get(&id)
            .copied()
            .or_else(|| self.gcx.const_fn_definition(id))
        else {
            return Ok(None);
        };
        if self.on_demand && self.checked_fns.insert(id) {
            if self.gcx.try_get_signature(id).is_none() {
                return Ok(None);
            }
            let errors_before = self.gcx.dcx().error_count();
            crate::sema::tycheck::check_const_fn_on_demand(
                self.gcx,
                id,
                func,
                fn_ctx,
                self.results.clone(),
            );
            if self.gcx.dcx().error_count() > errors_before {
                return Err(ReportedError);
            }
        }
        // Evaluate any pending constants referenced inside the const function body first.
        if let Some(block) = &func.block {
            struct BlockConstCollector {
                defs: Vec<DefinitionID>,
            }
            impl HirVisitor for BlockConstCollector {
                fn visit_expression(&mut self, expr: &hir::Expression) {
                    if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &expr.kind
                        && let hir::Resolution::Definition(
                            id,
                            hir::DefinitionKind::Constant | hir::DefinitionKind::AssociatedConstant,
                        ) = path.resolution
                    {
                        self.defs.push(id);
                    }
                    hir::walk_expression(self, expr);
                }
            }
            let mut collector = BlockConstCollector { defs: Vec::new() };
            hir::walk_block(&mut collector, block);
            for def_id in collector.defs {
                if self.gcx.try_get_const(def_id).is_none()
                    && (self.index.constants.contains_key(&def_id)
                        || self.gcx.const_definition(def_id).is_some())
                {
                    let _ = self.eval_const_item(def_id);
                }
            }
        }
        let results_snapshot = Rc::new(self.results.borrow().clone());
        let thir_fn = crate::thir::package::lower_const_function(
            self.gcx,
            results_snapshot,
            id,
            func,
            fn_ctx,
        )?;
        let body = Rc::new(MirBuilder::build_function(self.gcx, &thir_fn));
        self.fn_mir_cache.insert(id, body.clone());
        Ok(Some(body))
    }

    fn interp_to_const_value(
        &self,
        val: &InterpVal,
        ty: Ty<'ctx>,
        span: Span,
    ) -> CompileResult<ConstValue> {
        let ty = normalize_aliases(self.gcx, ty);
        match (val, ty.kind()) {
            (InterpVal::Unit, _) => Ok(ConstValue::Unit),
            (InterpVal::Bool(b), _) => Ok(ConstValue::Bool(*b)),
            (InterpVal::Rune(r), _) => Ok(ConstValue::Rune(*r)),
            (InterpVal::Int(i), _) => Ok(ConstValue::Integer(*i)),
            (InterpVal::Float(f), _) => Ok(ConstValue::Float(*f)),
            (InterpVal::String(s), _) => Ok(ConstValue::String(*s)),
            (InterpVal::Bytes(b), _) => Ok(ConstValue::Bytes(*b)),
            (InterpVal::EnumUnitVariant(id), _) => Ok(ConstValue::EnumUnitVariant(*id)),
            (InterpVal::Adt { variant: Some(idx), fields }, TyKind::Adt(adt_def, _))
                if fields.is_empty() && adt_def.kind == crate::sema::models::AdtKind::Enum =>
            {
                let enum_def = self.gcx.get_enum_definition(adt_def.id);
                let Some(variant) = enum_def.variants.get(*idx) else {
                    self.gcx.dcx().emit_error(
                        "invalid enum variant index during constant evaluation".into(),
                        Some(span),
                    );
                    return Err(ReportedError);
                };
                Ok(ConstValue::EnumUnitVariant(variant.ctor_def_id))
            }
            (InterpVal::Array(elems), TyKind::Array { element, .. }) => {
                let mut out = Vec::with_capacity(elems.len());
                for elem in elems {
                    out.push(self.interp_to_const_value(elem, element, span)?);
                }
                Ok(ConstValue::Array(self.gcx.interner().intern_const_array(out)))
            }
            _ => {
                self.gcx.dcx().emit_error(
                    format!(
                        "unsupported compile-time constant result of type '{}'",
                        ty.format(self.gcx)
                    ),
                    Some(span),
                );
                Err(ReportedError)
            }
        }
    }
}

struct InterpMachine<'a, 'hir, 'ctx> {
    evaluator: &'a mut ConstMirEvaluator<'hir, 'ctx>,
    frames: Vec<Frame>,
    steps: usize,
    root_span: Span,
}

impl<'a, 'hir, 'ctx> InterpMachine<'a, 'hir, 'ctx> {
    fn gcx(&self) -> Gcx<'ctx> {
        self.evaluator.gcx
    }

    fn emit_err(&self, msg: impl Into<String>, span: Span) -> ReportedError {
        self.gcx().dcx().emit_error(msg.into(), Some(span));
        ReportedError
    }

    fn tick(&mut self, _span: Span) -> CompileResult<()> {
        self.steps += 1;
        if self.steps > CONST_EVAL_STEP_LIMIT {
            return Err(self.emit_err(
                format!(
                    "constant evaluation exceeded the step limit of {CONST_EVAL_STEP_LIMIT} steps (possible infinite loop)"
                ),
                self.root_span,
            ));
        }
        Ok(())
    }

    fn eval_body(
        &mut self,
        body: &Body<'ctx>,
        args: Vec<InterpVal>,
        call_span: Span,
    ) -> CompileResult<InterpVal> {
        if self.frames.len() >= CONST_EVAL_CALL_DEPTH_LIMIT {
            return Err(self.emit_err(
                format!(
                    "constant evaluation exceeded maximum call depth of {CONST_EVAL_CALL_DEPTH_LIMIT}"
                ),
                call_span,
            ));
        }

        let mut locals = vec![InterpVal::Uninit; body.locals.len()];
        let mut arg_iter = args.into_iter();
        for (local_id, decl) in body.locals.iter_enumerated() {
            if matches!(decl.kind, crate::mir::LocalKind::Param) {
                let val = arg_iter.next().unwrap_or(InterpVal::Unit);
                locals[local_id.index()] = val;
            }
        }
        let frame_idx = self.frames.len();
        self.frames.push(Frame { locals });

        let mut current_block = body.start_block;
        let result = loop {
            let block = &body.basic_blocks[current_block];
            let mut stmt_err = None;
            for stmt in &block.statements {
                if let Err(e) = self.tick(stmt.span) {
                    stmt_err = Some(e);
                    break;
                }
                if let Err(e) = self.exec_statement(frame_idx, body, stmt) {
                    stmt_err = Some(e);
                    break;
                }
            }
            if let Some(e) = stmt_err {
                break Err(e);
            }

            let Some(term) = &block.terminator else {
                break Err(self.emit_err(
                    "incomplete control flow during constant evaluation",
                    call_span,
                ));
            };
            if let Err(e) = self.tick(term.span) {
                break Err(e);
            }

            match &term.kind {
                TerminatorKind::Goto { target } => {
                    current_block = *target;
                }
                TerminatorKind::SwitchInt {
                    discr,
                    targets,
                    otherwise,
                } => {
                    let val = match self.eval_operand(frame_idx, body, discr, term.span) {
                        Ok(v) => v,
                        Err(e) => break Err(e),
                    };
                    let bits = match val {
                        InterpVal::Bool(b) => b as u128,
                        InterpVal::Int(i) => {
                            let discr_ty = normalize_aliases(self.gcx(), body.operand_ty(self.gcx(), discr));
                            mask_int_to_u128(self.gcx(), i, discr_ty)
                        }
                        InterpVal::Rune(r) => r as u32 as u128,
                        _ => {
                            break Err(self.emit_err(
                                "unsupported branch discriminant during constant evaluation",
                                term.span,
                            ));
                        }
                    };
                    current_block = targets
                        .iter()
                        .find_map(|&(pat, bb)| (pat == bits).then_some(bb))
                        .unwrap_or(*otherwise);
                }
                TerminatorKind::Return => {
                    let ret = self.frames[frame_idx].locals[body.return_local.index()].clone();
                    break Ok(ret);
                }
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    target,
                    ..
                } => {
                    let res = self.eval_call(frame_idx, body, func, args, destination, term.span);
                    match res {
                        Ok(()) => current_block = *target,
                        Err(e) => break Err(e),
                    }
                }
                TerminatorKind::Yield { .. } => {
                    break Err(self.emit_err(
                        "`await` is not supported during constant evaluation",
                        term.span,
                    ));
                }
                TerminatorKind::GeneratorYield { .. } => {
                    break Err(self.emit_err(
                        "`yield` is not supported during constant evaluation",
                        term.span,
                    ));
                }
                TerminatorKind::ResumeUnwind => {
                    break Err(self.emit_err(
                        "unwinding is not supported during constant evaluation",
                        term.span,
                    ));
                }
                TerminatorKind::Unreachable | TerminatorKind::UnresolvedGoto => {
                    break Err(self.emit_err(
                        "entered unreachable code during constant evaluation",
                        term.span,
                    ));
                }
            }
        };

        self.frames.pop();
        result
    }

    fn exec_statement(
        &mut self,
        frame_idx: usize,
        body: &Body<'ctx>,
        stmt: &crate::mir::Statement<'ctx>,
    ) -> CompileResult<()> {
        match &stmt.kind {
            StatementKind::Assign(dest, rvalue) => {
                let value = self.eval_rvalue(frame_idx, body, rvalue, stmt.span)?;
                self.write_place(frame_idx, dest, value, stmt.span)?;
            }
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                let target = self.resolve_place_mut(frame_idx, place, stmt.span)?;
                match target {
                    InterpVal::Adt { variant, .. } => *variant = Some(variant_index.index()),
                    other => {
                        *other = InterpVal::Adt {
                            variant: Some(variant_index.index()),
                            fields: Vec::new(),
                        };
                    }
                }
            }
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::SetInitialized(_)
            | StatementKind::SourceScope(_)
            | StatementKind::KeepAlive(_)
            | StatementKind::GcSafepoint(_)
            | StatementKind::Nop => {}
        }
        Ok(())
    }

    fn eval_rvalue(
        &mut self,
        frame_idx: usize,
        body: &Body<'ctx>,
        rvalue: &Rvalue<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        match rvalue {
            Rvalue::Use(op) => self.eval_operand(frame_idx, body, op, span),
            Rvalue::CopyValue { source } => self.read_place(frame_idx, source, span),
            Rvalue::UnaryOp { op, operand } => {
                let ty = normalize_aliases(self.gcx(), body.operand_ty(self.gcx(), operand));
                let val = self.eval_operand(frame_idx, body, operand, span)?;
                self.eval_unary(*op, val, ty, span)
            }
            Rvalue::BinaryOp { op, lhs, rhs } => {
                let lhs_ty = normalize_aliases(self.gcx(), body.operand_ty(self.gcx(), lhs));
                let lhs_val = self.eval_operand(frame_idx, body, lhs, span)?;
                let rhs_val = self.eval_operand(frame_idx, body, rhs, span)?;
                self.eval_binary(*op, lhs_val, rhs_val, lhs_ty, span)
            }
            Rvalue::Cast { operand, ty, kind } => {
                let src_ty = normalize_aliases(self.gcx(), body.operand_ty(self.gcx(), operand));
                let dst_ty = normalize_aliases(self.gcx(), *ty);
                let val = self.eval_operand(frame_idx, body, operand, span)?;
                match kind {
                    CastKind::Numeric => self.eval_numeric_cast(val, src_ty, dst_ty, span),
                    _ => Err(self.emit_err(
                        format!(
                            "unsupported cast kind `{kind:?}` during constant evaluation"
                        ),
                        span,
                    )),
                }
            }
            Rvalue::Ref { place } => self.make_ref(frame_idx, place, span),
            Rvalue::Discriminant { place } => {
                let val = self.read_place(frame_idx, place, span)?;
                match val {
                    InterpVal::Adt {
                        variant: Some(idx), ..
                    } => Ok(InterpVal::Int(idx as i128)),
                    InterpVal::EnumUnitVariant(variant_def_id) => {
                        let Some(idx) = enum_unit_variant_index(self.gcx(), variant_def_id) else {
                            return Err(self.emit_err(
                                "cannot resolve enum variant discriminant during constant evaluation",
                                span,
                            ));
                        };
                        Ok(InterpVal::Int(idx as i128))
                    }
                    _ => Err(self.emit_err(
                        "cannot read discriminant of non-enum value during constant evaluation",
                        span,
                    )),
                }
            }
            Rvalue::Zeroed { ty } => Ok(self.zero_value(*ty)),
            Rvalue::Repeat { operand, count, .. } => {
                let elem = self.eval_operand(frame_idx, body, operand, span)?;
                Ok(InterpVal::Array(vec![elem; *count]))
            }
            Rvalue::Aggregate { kind, fields } => {
                let mut vals = Vec::with_capacity(fields.len());
                for f in fields {
                    vals.push(self.eval_operand(frame_idx, body, f, span)?);
                }
                match kind {
                    AggregateKind::Array { .. } => Ok(InterpVal::Array(vals)),
                    AggregateKind::Tuple => Ok(InterpVal::Tuple(vals)),
                    AggregateKind::Adt { variant_index, .. } => Ok(InterpVal::Adt {
                        variant: variant_index.map(|v| v.index()),
                        fields: vals,
                    }),
                    AggregateKind::Closure { .. } => Err(self.emit_err(
                        "closures are not supported during constant evaluation",
                        span,
                    )),
                }
            }
            Rvalue::Alloc { .. } => Err(self.emit_err(
                "heap allocation is not supported during constant evaluation",
                span,
            )),
            Rvalue::CleanupAddress { .. } => Err(self.emit_err(
                "cleanup address operation is not supported during constant evaluation",
                span,
            )),
        }
    }

    fn zero_value(&self, ty: Ty<'ctx>) -> InterpVal {
        let ty = normalize_aliases(self.gcx(), ty);
        match ty.kind() {
            TyKind::Bool => InterpVal::Bool(false),
            TyKind::Rune => InterpVal::Rune('\0'),
            TyKind::Int(_) | TyKind::UInt(_) => InterpVal::Int(0),
            TyKind::Float(_) => InterpVal::Float(0.0),
            TyKind::Tuple(items) if items.is_empty() => InterpVal::Unit,
            TyKind::Tuple(items) => {
                InterpVal::Tuple(items.iter().map(|t| self.zero_value(*t)).collect())
            }
            TyKind::Array { element, len } => {
                let n = match len.kind {
                    ConstKind::Value(ConstValue::Integer(n)) if n >= 0 => n as usize,
                    _ => 0,
                };
                InterpVal::Array(vec![self.zero_value(element); n])
            }
            _ => InterpVal::Uninit,
        }
    }

    fn eval_operand(
        &mut self,
        frame_idx: usize,
        _body: &Body<'ctx>,
        operand: &Operand<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        match operand {
            Operand::Copy(place) | Operand::CopyWith(place, _) => {
                self.read_place(frame_idx, place, span)
            }
            Operand::Constant(c) => {
                let ty = normalize_aliases(self.gcx(), c.ty);
                self.eval_constant(ty, &c.value, span)
            }
        }
    }

    fn eval_constant(
        &self,
        ty: Ty<'ctx>,
        kind: &ConstantKind<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        match kind {
            ConstantKind::Unit => Ok(InterpVal::Unit),
            ConstantKind::Bool(b) => Ok(InterpVal::Bool(*b)),
            ConstantKind::Rune(r) => Ok(InterpVal::Rune(*r)),
            ConstantKind::String(s) => Ok(InterpVal::String(*s)),
            ConstantKind::Bytes(b) => Ok(InterpVal::Bytes(*b)),
            ConstantKind::Float(f) => Ok(InterpVal::Float(*f)),
            ConstantKind::Integer(bits) => {
                let val = if let Some(layout) = integer_layout(self.gcx(), ty)
                    && layout.signed
                {
                    sign_extend(*bits, layout.bits)
                } else {
                    *bits as i128
                };
                Ok(InterpVal::Int(val))
            }
            ConstantKind::ConstArray(arr) => {
                let elem_ty = match ty.kind() {
                    TyKind::Array { element, .. } => normalize_aliases(self.gcx(), element),
                    _ => self.gcx().types.error,
                };
                let elems = self.gcx().interner().const_elements(*arr);
                let mut out = Vec::with_capacity(elems.len());
                for &e in elems.iter() {
                    out.push(self.const_value_to_interp(e, elem_ty, span)?);
                }
                Ok(InterpVal::Array(out))
            }
            ConstantKind::Function(..) => Ok(InterpVal::Unit),
            ConstantKind::GlobalVariableAddress(id) => {
                let name = self.gcx().symbol_text(self.gcx().definition_ident(*id).symbol);
                Err(self.emit_err(
                    format!("cannot read mutable static variable '{name}' during constant evaluation"),
                    span,
                ))
            }
            ConstantKind::ConstParam(_) | ConstantKind::InterfaceConstant(..) => Err(self.emit_err(
                "unresolved generic constant cannot be evaluated here",
                span,
            )),
        }
    }

    fn const_value_to_interp(
        &self,
        value: ConstValue,
        ty: Ty<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        match value {
            ConstValue::Unit => Ok(InterpVal::Unit),
            ConstValue::Bool(b) => Ok(InterpVal::Bool(b)),
            ConstValue::Rune(r) => Ok(InterpVal::Rune(r)),
            ConstValue::Integer(i) => Ok(InterpVal::Int(i)),
            ConstValue::Float(f) => Ok(InterpVal::Float(f)),
            ConstValue::String(s) => Ok(InterpVal::String(s)),
            ConstValue::Bytes(b) => Ok(InterpVal::Bytes(b)),
            ConstValue::EnumUnitVariant(id) => Ok(InterpVal::EnumUnitVariant(id)),
            ConstValue::Array(arr) => {
                let elem_ty = match ty.kind() {
                    TyKind::Array { element, .. } => normalize_aliases(self.gcx(), element),
                    _ => self.gcx().types.error,
                };
                let elems = self.gcx().interner().const_elements(arr);
                let mut out = Vec::with_capacity(elems.len());
                for &elem in elems.iter() {
                    out.push(self.const_value_to_interp(elem, elem_ty, span)?);
                }
                Ok(InterpVal::Array(out))
            }
        }
    }

    fn resolve_target(
        &self,
        mut frame_idx: usize,
        place: &Place<'ctx>,
        span: Span,
    ) -> CompileResult<(usize, LocalId, Vec<InterpProj>)> {
        let mut local = place.local;
        let mut path = Vec::new();
        for elem in &place.projection {
            match elem {
                PlaceElem::Deref => {
                    let val = self.read_by_path(frame_idx, local, &path, span)?;
                    match val {
                        InterpVal::Ref {
                            frame: f,
                            local: l,
                            path: p,
                        } => {
                            frame_idx = *f;
                            local = *l;
                            path = p.clone();
                        }
                        _ => {
                            return Err(self.emit_err(
                                "raw pointer dereference is not supported during constant evaluation",
                                span,
                            ));
                        }
                    }
                }
                PlaceElem::Field(idx, _) => {
                    path.push(InterpProj::Field(idx.index()));
                }
                PlaceElem::VariantDowncast { .. } => {}
            }
        }
        Ok((frame_idx, local, path))
    }

    fn make_ref(
        &self,
        frame_idx: usize,
        place: &Place<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        let (frame, local, path) = self.resolve_target(frame_idx, place, span)?;
        Ok(InterpVal::Ref { frame, local, path })
    }

    fn read_by_path<'b>(
        &'b self,
        frame_idx: usize,
        local: LocalId,
        path: &[InterpProj],
        span: Span,
    ) -> CompileResult<&'b InterpVal> {
        let mut cur = &self.frames[frame_idx].locals[local.index()];
        for proj in path {
            cur = match (cur, proj) {
                (InterpVal::Tuple(fields), InterpProj::Field(i))
                | (InterpVal::Adt { fields, .. }, InterpProj::Field(i)) => {
                    fields.get(*i).ok_or_else(|| {
                        self.emit_err("field index out of bounds during constant evaluation", span)
                    })?
                }
                (InterpVal::Array(elems), InterpProj::Index(i)) => elems.get(*i).ok_or_else(|| {
                    self.emit_err(
                        format!(
                            "array index out of bounds during constant evaluation: index {i} >= length {}",
                            elems.len()
                        ),
                        span,
                    )
                })?,
                _ => {
                    return Err(self.emit_err(
                        "unsupported place projection during constant evaluation",
                        span,
                    ));
                }
            };
        }
        Ok(cur)
    }

    fn resolve_place_mut<'b>(
        &'b mut self,
        frame_idx: usize,
        place: &Place<'ctx>,
        span: Span,
    ) -> CompileResult<&'b mut InterpVal> {
        let gcx = self.gcx();
        let (target_frame, target_local, path) = self.resolve_target(frame_idx, place, span)?;
        let mut cur = &mut self.frames[target_frame].locals[target_local.index()];
        for proj in path {
            cur = match (cur, proj) {
                (InterpVal::Tuple(fields), InterpProj::Field(i))
                | (InterpVal::Adt { fields, .. }, InterpProj::Field(i)) => {
                    if i >= fields.len() {
                        gcx.dcx().emit_error(
                            "field index out of bounds during constant evaluation".into(),
                            Some(span),
                        );
                        return Err(ReportedError);
                    }
                    &mut fields[i]
                }
                (InterpVal::Array(elems), InterpProj::Index(i)) => {
                    let len = elems.len();
                    if i >= len {
                        gcx.dcx().emit_error(
                            format!(
                                "array index out of bounds during constant evaluation: index {i} >= length {len}"
                            ),
                            Some(span),
                        );
                        return Err(ReportedError);
                    }
                    &mut elems[i]
                }
                _ => {
                    gcx.dcx().emit_error(
                        "unsupported place write during constant evaluation".into(),
                        Some(span),
                    );
                    return Err(ReportedError);
                }
            };
        }
        Ok(cur)
    }

    fn read_place(
        &self,
        frame_idx: usize,
        place: &Place<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        let (target_frame, target_local, path) = self.resolve_target(frame_idx, place, span)?;
        let val = self.read_by_path(target_frame, target_local, &path, span)?;
        if matches!(val, InterpVal::Uninit) {
            return Err(self.emit_err(
                "read of uninitialized local during constant evaluation",
                span,
            ));
        }
        Ok(val.clone())
    }

    fn write_place(
        &mut self,
        frame_idx: usize,
        place: &Place<'ctx>,
        value: InterpVal,
        span: Span,
    ) -> CompileResult<()> {
        let slot = self.resolve_place_mut(frame_idx, place, span)?;
        *slot = value;
        Ok(())
    }

    fn eval_unary(
        &self,
        op: UnaryOperator,
        val: InterpVal,
        ty: Ty<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        match (op, val) {
            (UnaryOperator::LogicalNot, InterpVal::Bool(b)) => Ok(InterpVal::Bool(!b)),
            (UnaryOperator::Negate, InterpVal::Int(i)) => {
                let res = i.checked_neg().ok_or_else(|| {
                    self.emit_err("integer overflow during constant negation", span)
                })?;
                check_int_range(self.gcx(), res, ty, span)?;
                Ok(InterpVal::Int(res))
            }
            (UnaryOperator::Negate, InterpVal::Float(f)) => Ok(InterpVal::Float(-f)),
            (UnaryOperator::BitwiseNot, InterpVal::Int(i)) => {
                let Some(IntegerLayout { bits, signed }) = integer_layout(self.gcx(), ty) else {
                    return Err(self.emit_err(
                        "unsupported bitwise not operand during constant evaluation",
                        span,
                    ));
                };
                let res = if signed {
                    !i
                } else {
                    let mask = if bits == 128 {
                        u128::MAX
                    } else {
                        (1u128 << bits) - 1
                    };
                    ((!(i as u128)) & mask) as i128
                };
                Ok(InterpVal::Int(res))
            }
            _ => Err(self.emit_err(
                "unsupported unary operation during constant evaluation",
                span,
            )),
        }
    }

    fn eval_binary(
        &self,
        op: BinaryOperator,
        lhs: InterpVal,
        rhs: InterpVal,
        ty: Ty<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        match op {
            BinaryOperator::Eql => Ok(InterpVal::Bool(interp_eq(self.gcx(), &lhs, &rhs)?)),
            BinaryOperator::Neq => Ok(InterpVal::Bool(!interp_eq(self.gcx(), &lhs, &rhs)?)),
            BinaryOperator::Lt => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => Ok(InterpVal::Bool(a < b)),
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Bool(a < b)),
                (InterpVal::Rune(a), InterpVal::Rune(b)) => Ok(InterpVal::Bool(a < b)),
                _ => Err(self.emit_err("unsupported `<` operands during constant evaluation", span)),
            },
            BinaryOperator::Leq => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => Ok(InterpVal::Bool(a <= b)),
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Bool(a <= b)),
                (InterpVal::Rune(a), InterpVal::Rune(b)) => Ok(InterpVal::Bool(a <= b)),
                _ => Err(self.emit_err("unsupported `<=` operands during constant evaluation", span)),
            },
            BinaryOperator::Gt => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => Ok(InterpVal::Bool(a > b)),
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Bool(a > b)),
                (InterpVal::Rune(a), InterpVal::Rune(b)) => Ok(InterpVal::Bool(a > b)),
                _ => Err(self.emit_err("unsupported `>` operands during constant evaluation", span)),
            },
            BinaryOperator::Geq => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => Ok(InterpVal::Bool(a >= b)),
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Bool(a >= b)),
                (InterpVal::Rune(a), InterpVal::Rune(b)) => Ok(InterpVal::Bool(a >= b)),
                _ => Err(self.emit_err("unsupported `>=` operands during constant evaluation", span)),
            },
            BinaryOperator::Add => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => {
                    let res = a.checked_add(b).ok_or_else(|| {
                        self.emit_err("integer overflow during constant addition", span)
                    })?;
                    check_int_range(self.gcx(), res, ty, span)?;
                    Ok(InterpVal::Int(res))
                }
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Float(a + b)),
                _ => Err(self.emit_err("unsupported `+` operands during constant evaluation", span)),
            },
            BinaryOperator::Sub => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => {
                    let res = a.checked_sub(b).ok_or_else(|| {
                        self.emit_err("integer overflow during constant subtraction", span)
                    })?;
                    check_int_range(self.gcx(), res, ty, span)?;
                    Ok(InterpVal::Int(res))
                }
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Float(a - b)),
                _ => Err(self.emit_err("unsupported `-` operands during constant evaluation", span)),
            },
            BinaryOperator::Mul => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => {
                    let res = a.checked_mul(b).ok_or_else(|| {
                        self.emit_err("integer overflow during constant multiplication", span)
                    })?;
                    check_int_range(self.gcx(), res, ty, span)?;
                    Ok(InterpVal::Int(res))
                }
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Float(a * b)),
                _ => Err(self.emit_err("unsupported `*` operands during constant evaluation", span)),
            },
            BinaryOperator::Div => match (lhs, rhs) {
                (InterpVal::Int(_), InterpVal::Int(0)) => {
                    Err(self.emit_err("division by zero during constant evaluation", span))
                }
                (InterpVal::Int(a), InterpVal::Int(b)) => {
                    let res = a.checked_div(b).ok_or_else(|| {
                        self.emit_err("integer overflow during constant division", span)
                    })?;
                    check_int_range(self.gcx(), res, ty, span)?;
                    Ok(InterpVal::Int(res))
                }
                (InterpVal::Float(_), InterpVal::Float(b)) if b == 0.0 => {
                    Err(self.emit_err("division by zero during constant evaluation", span))
                }
                (InterpVal::Float(a), InterpVal::Float(b)) => Ok(InterpVal::Float(a / b)),
                _ => Err(self.emit_err("unsupported `/` operands during constant evaluation", span)),
            },
            BinaryOperator::Rem => match (lhs, rhs) {
                (InterpVal::Int(_), InterpVal::Int(0)) => {
                    Err(self.emit_err("remainder by zero during constant evaluation", span))
                }
                (InterpVal::Int(a), InterpVal::Int(b)) => {
                    let res = a.checked_rem(b).ok_or_else(|| {
                        self.emit_err("integer overflow during constant remainder", span)
                    })?;
                    check_int_range(self.gcx(), res, ty, span)?;
                    Ok(InterpVal::Int(res))
                }
                _ => Err(self.emit_err("unsupported `%` operands during constant evaluation", span)),
            },
            BinaryOperator::BitAnd => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => Ok(InterpVal::Int(a & b)),
                _ => Err(self.emit_err("unsupported `&` operands during constant evaluation", span)),
            },
            BinaryOperator::BitOr => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => Ok(InterpVal::Int(a | b)),
                _ => Err(self.emit_err("unsupported `|` operands during constant evaluation", span)),
            },
            BinaryOperator::BitXor => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => Ok(InterpVal::Int(a ^ b)),
                _ => Err(self.emit_err("unsupported `^` operands during constant evaluation", span)),
            },
            BinaryOperator::BitShl => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => {
                    let Some(IntegerLayout { bits, signed }) = integer_layout(self.gcx(), ty) else {
                        return Err(self.emit_err("unsupported `<<` type during constant evaluation", span));
                    };
                    if b < 0 || b >= i128::from(bits) {
                        return Err(self.emit_err(
                            format!("shift count {b} out of range for {bits}-bit integer during constant evaluation"),
                            span,
                        ));
                    }
                    let shift = b as u32;
                    let mask = if bits == 128 {
                        u128::MAX
                    } else {
                        (1u128 << bits) - 1
                    };
                    let shifted = ((a as u128) << shift) & mask;
                    let res = if signed {
                        sign_extend(shifted as u64, bits)
                    } else {
                        shifted as i128
                    };
                    Ok(InterpVal::Int(res))
                }
                _ => Err(self.emit_err("unsupported `<<` operands during constant evaluation", span)),
            },
            BinaryOperator::BitShr => match (lhs, rhs) {
                (InterpVal::Int(a), InterpVal::Int(b)) => {
                    let Some(IntegerLayout { bits, signed }) = integer_layout(self.gcx(), ty) else {
                        return Err(self.emit_err("unsupported `>>` type during constant evaluation", span));
                    };
                    if b < 0 || b >= i128::from(bits) {
                        return Err(self.emit_err(
                            format!("shift count {b} out of range for {bits}-bit integer during constant evaluation"),
                            span,
                        ));
                    }
                    let shift = b as u32;
                    let res = if signed {
                        a >> shift
                    } else {
                        let mask = if bits == 128 {
                            u128::MAX
                        } else {
                            (1u128 << bits) - 1
                        };
                        (((a as u128) & mask) >> shift) as i128
                    };
                    Ok(InterpVal::Int(res))
                }
                _ => Err(self.emit_err("unsupported `>>` operands during constant evaluation", span)),
            },
        }
    }

    fn eval_numeric_cast(
        &self,
        val: InterpVal,
        _src_ty: Ty<'ctx>,
        dst_ty: Ty<'ctx>,
        span: Span,
    ) -> CompileResult<InterpVal> {
        let gcx = self.gcx();
        match (val, dst_ty.kind()) {
            (InterpVal::Int(v), TyKind::Int(_) | TyKind::UInt(_)) => {
                let Some(IntegerLayout { bits, signed }) = integer_layout(gcx, dst_ty) else {
                    return Err(self.emit_err("unsupported integer cast during constant evaluation", span));
                };
                let mask = if bits == 128 {
                    u128::MAX
                } else {
                    (1u128 << bits) - 1
                };
                let raw = (v as u128) & mask;
                let res = if signed {
                    sign_extend(raw as u64, bits)
                } else {
                    raw as i128
                };
                Ok(InterpVal::Int(res))
            }
            (InterpVal::Int(v), TyKind::Float(FloatTy::F32)) => {
                Ok(InterpVal::Float((v as f32) as f64))
            }
            (InterpVal::Int(v), TyKind::Float(FloatTy::F64)) => Ok(InterpVal::Float(v as f64)),
            (InterpVal::Bool(b), TyKind::Int(_) | TyKind::UInt(_)) => {
                Ok(InterpVal::Int(b as i128))
            }
            (InterpVal::Rune(r), TyKind::Int(_) | TyKind::UInt(_)) => {
                Ok(InterpVal::Int(r as u32 as i128))
            }
            (InterpVal::Float(f), TyKind::Float(FloatTy::F32)) => {
                Ok(InterpVal::Float((f as f32) as f64))
            }
            (InterpVal::Float(f), TyKind::Float(FloatTy::F64)) => Ok(InterpVal::Float(f)),
            (InterpVal::Float(f), TyKind::Int(_) | TyKind::UInt(_)) => {
                Ok(InterpVal::Int(f as i128))
            }
            _ => Err(self.emit_err(
                format!(
                    "unsupported cast to '{}' during constant evaluation",
                    dst_ty.format(gcx)
                ),
                span,
            )),
        }
    }

    fn eval_call(
        &mut self,
        frame_idx: usize,
        body: &Body<'ctx>,
        func: &Operand<'ctx>,
        args: &[Operand<'ctx>],
        destination: &Place<'ctx>,
        span: Span,
    ) -> CompileResult<()> {
        let Operand::Constant(c) = func else {
            return Err(self.emit_err(
                "indirect function calls are not supported during constant evaluation",
                span,
            ));
        };
        let ConstantKind::Function(callee_id, _, _) = c.value else {
            return Err(self.emit_err(
                "unsupported call target during constant evaluation",
                span,
            ));
        };

        let mut arg_vals = Vec::with_capacity(args.len());
        let mut arg_tys = Vec::with_capacity(args.len());
        for arg in args {
            arg_tys.push(normalize_aliases(
                self.gcx(),
                body.operand_ty(self.gcx(), arg),
            ));
            arg_vals.push(self.eval_operand(frame_idx, body, arg, span)?);
        }

        let name = self
            .gcx()
            .symbol_text(self.gcx().definition_symbol_or_fallback(callee_id))
            .to_string();

        // 1. Check for std fixed-size array operations (`subscript`, `at`, `set`, `len`).
        let dest_ty = normalize_aliases(self.gcx(), body.place_ty(self.gcx(), destination));
        if let Some(handled) =
            self.try_eval_array_builtin(&name, &arg_tys, &arg_vals, dest_ty, span)?
        {
            self.write_place(frame_idx, destination, handled, span)?;
            return Ok(());
        }

        // 2. Check for pure primitive integer methods and checked/wrapping
        //    compiler arithmetic intrinsics.
        if let Some(handled) =
            self.try_eval_integer_builtin(&name, &arg_tys, &arg_vals, span)?
        {
            self.write_place(frame_idx, destination, handled, span)?;
            return Ok(());
        }

        // 3. Explicit compile-time panic diagnostic.
        if name == "panic" {
            let msg = match arg_vals.first() {
                Some(InterpVal::String(sym)) => {
                    format!(": {}", self.gcx().symbol_text(*sym))
                }
                _ => String::new(),
            };
            return Err(self.emit_err(format!("constant evaluation panicked{msg}"), span));
        }

        // 4. Reject non-const functions with a clear diagnostic naming the callee.
        if !self.gcx().definition_is_const(callee_id) {
            return Err(self.emit_err(
                format!(
                    "cannot call non-const function '{name}' during constant evaluation"
                ),
                span,
            ));
        }

        // 5. Lower and recursively interpret the `const func` MIR body.
        let Some(callee_body) = self.evaluator.get_or_build_const_fn_mir(callee_id)? else {
            return Err(self.emit_err(
                format!(
                    "body of const function '{name}' is not available for compile-time evaluation"
                ),
                span,
            ));
        };
        let ret = self.eval_body(&callee_body, arg_vals, span)?;
        self.write_place(frame_idx, destination, ret, span)?;
        Ok(())
    }

    fn try_eval_array_builtin(
        &mut self,
        name: &str,
        arg_tys: &[Ty<'ctx>],
        arg_vals: &[InterpVal],
        dest_ty: Ty<'ctx>,
        span: Span,
    ) -> CompileResult<Option<InterpVal>> {
        let Some(&first_ty) = arg_tys.first() else {
            return Ok(None);
        };
        let is_array_ref = matches!(
            first_ty.kind(),
            TyKind::Reference(inner) if matches!(normalize_aliases(self.gcx(), inner).kind(), TyKind::Array { .. })
        );
        let is_array_val = matches!(first_ty.kind(), TyKind::Array { .. });
        if !is_array_ref && !is_array_val {
            return Ok(None);
        }

        if name == "len" && arg_vals.len() == 1 {
            let len = match &arg_vals[0] {
                InterpVal::Array(elems) => elems.len(),
                InterpVal::Ref { frame, local, path } => {
                    match self.read_by_path(*frame, *local, path, span)? {
                        InterpVal::Array(elems) => elems.len(),
                        _ => return Ok(None),
                    }
                }
                _ => return Ok(None),
            };
            return Ok(Some(InterpVal::Int(len as i128)));
        }

        if (name == "at" || name == "address" || name.contains("subscript")) && arg_vals.len() == 2 {
            let InterpVal::Int(raw_idx) = arg_vals[1] else {
                return Ok(None);
            };
            if raw_idx < 0 {
                return Err(self.emit_err(
                    format!(
                        "array index out of bounds during constant evaluation: index {raw_idx}"
                    ),
                    span,
                ));
            }
            let idx = raw_idx as usize;
            let returns_ref = matches!(dest_ty.kind(), TyKind::Reference(_));
            match &arg_vals[0] {
                InterpVal::Ref { frame, local, path } => {
                    let elem = match self.read_by_path(*frame, *local, path, span)? {
                        InterpVal::Array(elems) => {
                            if idx >= elems.len() {
                                return Err(self.emit_err(
                                    format!(
                                        "array index out of bounds during constant evaluation: index {idx} >= length {}",
                                        elems.len()
                                    ),
                                    span,
                                ));
                            }
                            if returns_ref {
                                let mut elem_path = path.clone();
                                elem_path.push(InterpProj::Index(idx));
                                return Ok(Some(InterpVal::Ref {
                                    frame: *frame,
                                    local: *local,
                                    path: elem_path,
                                }));
                            }
                            elems[idx].clone()
                        }
                        _ => return Ok(None),
                    };
                    return Ok(Some(elem));
                }
                InterpVal::Array(elems) if !returns_ref => {
                    if idx >= elems.len() {
                        return Err(self.emit_err(
                            format!(
                                "array index out of bounds during constant evaluation: index {idx} >= length {}",
                                elems.len()
                            ),
                            span,
                        ));
                    }
                    return Ok(Some(elems[idx].clone()));
                }
                _ => return Ok(None),
            }
        }

        if (name == "set" || name.contains("subscript")) && arg_vals.len() == 3 {
            let InterpVal::Int(raw_idx) = arg_vals[1] else {
                return Ok(None);
            };
            if raw_idx < 0 {
                return Err(self.emit_err(
                    format!(
                        "array index out of bounds during constant evaluation: index {raw_idx}"
                    ),
                    span,
                ));
            }
            let idx = raw_idx as usize;
            let InterpVal::Ref { frame, local, path } = &arg_vals[0] else {
                return Ok(None);
            };
            let mut elem_path = path.clone();
            elem_path.push(InterpProj::Index(idx));
            let target_frame = *frame;
            let target_local = *local;
            let mut cur = &mut self.frames[target_frame].locals[target_local.index()];
            for proj in elem_path {
                cur = match (cur, proj) {
                    (InterpVal::Tuple(fields), InterpProj::Field(i))
                    | (InterpVal::Adt { fields, .. }, InterpProj::Field(i)) => &mut fields[i],
                    (InterpVal::Array(elems), InterpProj::Index(i)) => {
                        let len = elems.len();
                        if i >= len {
                            return Err(self.emit_err(
                                format!(
                                    "array index out of bounds during constant evaluation: index {i} >= length {len}"
                                ),
                                span,
                            ));
                        }
                        &mut elems[i]
                    }
                    _ => {
                        return Err(self.emit_err(
                            "unsupported array element write during constant evaluation",
                            span,
                        ));
                    }
                };
            }
            *cur = arg_vals[2].clone();
            return Ok(Some(InterpVal::Unit));
        }

        Ok(None)
    }

    fn try_eval_integer_builtin(
        &self,
        name: &str,
        arg_tys: &[Ty<'ctx>],
        arg_vals: &[InterpVal],
        span: Span,
    ) -> CompileResult<Option<InterpVal>> {
        let Some(&ty) = arg_tys.first() else {
            return Ok(None);
        };
        if name == "__intrinsic_checked_neg" && arg_vals.len() == 1 {
            return Ok(Some(self.eval_unary(
                UnaryOperator::Negate,
                arg_vals[0].clone(),
                ty,
                span,
            )?));
        }
        if arg_vals.len() == 2 {
            let checked_op = match name {
                "__intrinsic_checked_add" => Some(BinaryOperator::Add),
                "__intrinsic_checked_sub" => Some(BinaryOperator::Sub),
                "__intrinsic_checked_mul" => Some(BinaryOperator::Mul),
                "__intrinsic_checked_div" => Some(BinaryOperator::Div),
                "__intrinsic_checked_rem" => Some(BinaryOperator::Rem),
                "__intrinsic_checked_shl" => Some(BinaryOperator::BitShl),
                "__intrinsic_checked_shr" => Some(BinaryOperator::BitShr),
                _ => None,
            };
            if let Some(op) = checked_op {
                return Ok(Some(self.eval_binary(
                    op,
                    arg_vals[0].clone(),
                    arg_vals[1].clone(),
                    ty,
                    span,
                )?));
            }
        }
        let Some(IntegerLayout { bits, signed }) = integer_layout(self.gcx(), ty) else {
            return Ok(None);
        };
        let mask = if bits == 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        let finish = |raw: u128| {
            let masked = raw & mask;
            if signed {
                InterpVal::Int(sign_extend(masked as u64, bits))
            } else {
                InterpVal::Int(masked as i128)
            }
        };
        if arg_vals.len() == 1 {
            let InterpVal::Int(a) = &arg_vals[0] else {
                return Ok(None);
            };
            let v = (*a as u128) & mask;
            return match name {
                "__intrinsic_ctpop" | "countOnes" => Ok(Some(InterpVal::Int(v.count_ones() as i128))),
                "__intrinsic_ctlz" | "leadingZeros" => {
                    let lz = if v == 0 {
                        bits
                    } else {
                        v.leading_zeros() - (128 - bits)
                    };
                    Ok(Some(InterpVal::Int(lz as i128)))
                }
                "__intrinsic_cttz" | "trailingZeros" => {
                    let tz = if v == 0 { bits } else { v.trailing_zeros() };
                    Ok(Some(InterpVal::Int(tz as i128)))
                }
                "__intrinsic_bswap" | "swapBytes" => {
                    let swapped = match bits {
                        8 => v,
                        16 => (v as u16).swap_bytes() as u128,
                        32 => (v as u32).swap_bytes() as u128,
                        64 => (v as u64).swap_bytes() as u128,
                        _ => return Ok(None),
                    };
                    Ok(Some(finish(swapped)))
                }
                "__intrinsic_bitreverse" | "reverseBits" => {
                    let reversed = v.reverse_bits() >> (128 - bits);
                    Ok(Some(finish(reversed)))
                }
                _ => Ok(None),
            };
        }
        if arg_vals.len() == 3 {
            let (InterpVal::Int(hi), InterpVal::Int(lo), InterpVal::Int(s)) =
                (&arg_vals[0], &arg_vals[1], &arg_vals[2])
            else {
                return Ok(None);
            };
            let rot = (*s as u32) % bits;
            let hi = (*hi as u128) & mask;
            let lo = (*lo as u128) & mask;
            return match name {
                "__intrinsic_fshl" => {
                    let res = if rot == 0 {
                        hi
                    } else {
                        ((hi << rot) | (lo >> (bits - rot))) & mask
                    };
                    Ok(Some(finish(res)))
                }
                "__intrinsic_fshr" => {
                    let res = if rot == 0 {
                        lo
                    } else {
                        ((lo >> rot) | (hi << (bits - rot))) & mask
                    };
                    Ok(Some(finish(res)))
                }
                _ => Ok(None),
            };
        }
        if arg_vals.len() != 2 {
            return Ok(None);
        }
        let (InterpVal::Int(a), InterpVal::Int(b)) = (&arg_vals[0], &arg_vals[1]) else {
            return Ok(None);
        };
        match name {
            "wrappingAdd" | "__intrinsic_wrapping_add" => {
                Ok(Some(finish((*a as u128).wrapping_add(*b as u128))))
            }
            "wrappingSub" | "__intrinsic_wrapping_sub" => {
                Ok(Some(finish((*a as u128).wrapping_sub(*b as u128))))
            }
            "wrappingMul" | "__intrinsic_wrapping_mul" => {
                Ok(Some(finish((*a as u128).wrapping_mul(*b as u128))))
            }
            "rotateLeft" => {
                let rot = (*b as u32) % bits;
                let v = (*a as u128) & mask;
                let res = if rot == 0 {
                    v
                } else {
                    ((v << rot) | (v >> (bits - rot))) & mask
                };
                Ok(Some(finish(res)))
            }
            "rotateRight" => {
                let rot = (*b as u32) % bits;
                let v = (*a as u128) & mask;
                let res = if rot == 0 {
                    v
                } else {
                    ((v >> rot) | (v << (bits - rot))) & mask
                };
                Ok(Some(finish(res)))
            }
            _ => {
                let _ = span;
                Ok(None)
            }
        }
    }
}

fn enum_unit_variant_index(gcx: Gcx<'_>, variant_def_id: DefinitionID) -> Option<usize> {
    let parent_id = gcx.definition_parent(variant_def_id)?;
    let enum_id = match gcx.definition_kind(parent_id) {
        hir::DefinitionKind::Enum => parent_id,
        hir::DefinitionKind::Variant => gcx.definition_parent(parent_id)?,
        _ => return None,
    };
    let enum_def = gcx.try_get_enum_definition(enum_id)?;
    enum_def
        .variants
        .iter()
        .position(|variant| variant.def_id == variant_def_id || variant.ctor_def_id == variant_def_id)
}

fn interp_eq(gcx: Gcx<'_>, lhs: &InterpVal, rhs: &InterpVal) -> CompileResult<bool> {
    Ok(match (lhs, rhs) {
        (InterpVal::Unit, InterpVal::Unit) => true,
        (InterpVal::Bool(a), InterpVal::Bool(b)) => a == b,
        (InterpVal::Rune(a), InterpVal::Rune(b)) => a == b,
        (InterpVal::Int(a), InterpVal::Int(b)) => a == b,
        (InterpVal::Float(a), InterpVal::Float(b)) => a == b,
        (InterpVal::String(a), InterpVal::String(b)) => a == b,
        (InterpVal::Bytes(a), InterpVal::Bytes(b)) => a == b,
        (InterpVal::EnumUnitVariant(a), InterpVal::EnumUnitVariant(b)) => a == b,
        (
            InterpVal::EnumUnitVariant(def_id),
            InterpVal::Adt {
                variant: Some(idx),
                fields,
            },
        )
        | (
            InterpVal::Adt {
                variant: Some(idx),
                fields,
            },
            InterpVal::EnumUnitVariant(def_id),
        ) if fields.is_empty() => enum_unit_variant_index(gcx, *def_id) == Some(*idx),
        (
            InterpVal::Adt {
                variant: v1,
                fields: f1,
            },
            InterpVal::Adt {
                variant: v2,
                fields: f2,
            },
        ) => {
            v1 == v2
                && f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2.iter())
                    .all(|(a, b)| interp_eq(gcx, a, b).unwrap_or(false))
        }
        _ => false,
    })
}

fn sign_extend(bits: u64, width: u32) -> i128 {
    if width >= 64 {
        (bits as i64) as i128
    } else {
        let shift = 64 - width;
        (((bits << shift) as i64) >> shift) as i128
    }
}

fn mask_int_to_u128<'ctx>(gcx: Gcx<'ctx>, value: i128, ty: Ty<'ctx>) -> u128 {
    let Some(IntegerLayout { bits, .. }) = integer_layout(gcx, ty) else {
        return value as u64 as u128;
    };
    if bits == 128 {
        value as u128
    } else {
        (value as u128) & ((1u128 << bits) - 1)
    }
}

fn check_int_range<'ctx>(
    gcx: Gcx<'ctx>,
    value: i128,
    ty: Ty<'ctx>,
    span: Span,
) -> CompileResult<()> {
    let Some(IntegerLayout { bits, signed }) = integer_layout(gcx, ty) else {
        return Ok(());
    };
    let (min, max) = if signed {
        let min = -(1i128 << (bits - 1));
        let max = (1i128 << (bits - 1)) - 1;
        (min, max)
    } else {
        let max = if bits == 128 {
            i128::MAX
        } else {
            (1i128 << bits) - 1
        };
        (0i128, max)
    };
    if value < min || value > max {
        gcx.dcx().emit_error(
            format!(
                "integer overflow during constant evaluation: value {value} out of range for '{}'",
                ty.format(gcx)
            ),
            Some(span),
        );
        return Err(ReportedError);
    }
    Ok(())
}
