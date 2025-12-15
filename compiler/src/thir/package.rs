use crate::{
    compile::{context::GlobalContext, entry::validate_entry_point},
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, Mutability, Resolution},
    sema::{
        models::{AdtKind, Ty, TyKind},
        tycheck::solve::Adjustment,
    },
    thir::{
        self, Block, BlockId, Constant, ConstantKind, Expr, ExprId, ExprKind, Param, Stmt, StmtId,
        StmtKind, ThirFunction, ThirPackage, pattern::pattern_from_hir,
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
) -> CompileResult<ThirPackage<'ctx>> {
    let entry = validate_entry_point(&package, gcx)?;
    let package = Actor::run(package, gcx, entry)?;
    Ok(package)
}

struct Actor<'ctx> {
    gcx: GlobalContext<'ctx>,
    functions: FxHashMap<DefinitionID, ThirFunction<'ctx>>,
    entry: Option<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn new(gcx: GlobalContext<'ctx>, entry: Option<DefinitionID>) -> Self {
        Actor {
            gcx,
            functions: FxHashMap::default(),
            entry,
        }
    }

    fn run(
        package: &hir::Package,
        gcx: GlobalContext<'ctx>,
        entry: Option<DefinitionID>,
    ) -> CompileResult<ThirPackage<'ctx>> {
        let mut actor = Actor::new(gcx, entry);
        hir::walk_package(&mut actor, package);
        let pkg = ThirPackage {
            functions: actor.functions,
            entry: actor.entry,
        };
        gcx.dcx().ok()?;
        Ok(pkg)
    }
}

impl<'ctx> HirVisitor for Actor<'ctx> {
    fn visit_function(
        &mut self,
        id: DefinitionID,
        node: &hir::Function,
        fn_ctx: hir::FunctionContext,
    ) -> Self::Result {
        let func = FunctionLower::lower(self.gcx, id, node);
        self.functions.insert(id, func);
        hir::walk_function(self, id, node, fn_ctx);
    }
}

struct FunctionLower<'ctx> {
    gcx: GlobalContext<'ctx>,
    func: ThirFunction<'ctx>,
}

impl<'ctx> FunctionLower<'ctx> {
    fn lower(
        gcx: GlobalContext<'ctx>,
        id: DefinitionID,
        node: &hir::Function,
    ) -> ThirFunction<'ctx> {
        let mut lower = FunctionLower {
            gcx,
            func: ThirFunction {
                id,
                body: None,
                span: node.signature.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
            },
        };

        lower.lower_params(node);
        lower.lower_body(node);
        lower.func
    }

    fn lower_params(&mut self, node: &hir::Function) {
        let signature = self.gcx.get_signature(self.func.id);
        self.func.params = node
            .signature
            .prototype
            .inputs
            .iter()
            .zip(signature.inputs.iter())
            .map(|(param, lowered)| Param {
                id: param.id,
                name: param.name.symbol,
                ty: lowered.ty,
                span: param.span,
            })
            .collect();
    }

    fn lower_body(&mut self, node: &hir::Function) {
        if let Some(block) = &node.block {
            let block_id = self.lower_block(block, false);
            self.func.body = Some(block_id);
        }
    }

    fn lower_block(&mut self, block: &hir::Block, capture_tail_expr: bool) -> BlockId {
        let id = BlockId::from_raw(self.func.blocks.len() as u32);
        self.func.blocks.push(Block {
            id,
            stmts: vec![],
            expr: None,
        });

        let mut stmts = Vec::new();
        let mut expr = None;

        for (idx, stmt) in block.statements.iter().enumerate() {
            let is_last = idx + 1 == block.statements.len();
            if capture_tail_expr && is_last {
                if let hir::StatementKind::Expression(expr_stmt) = &stmt.kind {
                    let expr_id = self.lower_expr(expr_stmt);
                    expr = Some(expr_id);
                    continue;
                }
            }

            if let Some(stmt) = self.lower_statement(stmt) {
                let id = self.push_stmt(stmt);
                stmts.push(id);
            }
        }

        self.func.blocks[id].stmts = stmts;
        self.func.blocks[id].expr = expr;
        id
    }

    fn lower_statement(&mut self, stmt: &hir::Statement) -> Option<Stmt<'ctx>> {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => None,
            hir::StatementKind::Expression(expr) => {
                if let hir::ExpressionKind::Assign(lhs, rhs) = &expr.kind {
                    let target = self.lower_expr(lhs);
                    let value = self.lower_expr(rhs);
                    return Some(Stmt {
                        kind: StmtKind::Assign { target, value },
                        span: stmt.span,
                    });
                }

                let expr_id = self.lower_expr(expr);
                Some(Stmt {
                    kind: StmtKind::Expr(expr_id),
                    span: stmt.span,
                })
            }
            hir::StatementKind::Variable(local) => Some(self.lower_local(local)),
            hir::StatementKind::Break => Some(Stmt {
                kind: StmtKind::Break,
                span: stmt.span,
            }),
            hir::StatementKind::Continue => Some(Stmt {
                kind: StmtKind::Continue,
                span: stmt.span,
            }),
            hir::StatementKind::Return(value) => {
                let expr_id = value.as_deref().map(|expr| self.lower_expr(expr));
                Some(Stmt {
                    kind: StmtKind::Return { value: expr_id },
                    span: stmt.span,
                })
            }
            hir::StatementKind::Loop { block, .. } => {
                let block_id = self.lower_block(block, false);
                Some(Stmt {
                    kind: StmtKind::Loop { block: block_id },
                    span: stmt.span,
                })
            }
            hir::StatementKind::Defer(_) => None,
            hir::StatementKind::Guard { .. } => None,
        }
    }

    fn lower_local(&mut self, local: &hir::Local) -> Stmt<'ctx> {
        let ty = self.gcx.get_node_type(local.id);
        let expr = local
            .initializer
            .as_deref()
            .map(|expr| self.lower_expr(expr));

        Stmt {
            kind: StmtKind::Let {
                id: local.id,
                pattern: pattern_from_hir(self.gcx, &local.pattern),
                expr,
                ty,
            },
            span: local.pattern.span,
        }
    }

    pub fn lower_expr(&mut self, expr: &hir::Expression) -> ExprId {
        self.lower_expr_inner(expr)
    }

    fn lower_expr_inner(&mut self, expr: &hir::Expression) -> ExprId {
        let mut thir_expr = self.lower_expr_unadjusted(expr);
        // Apply adjustments if any
        if let Some(adjustments) = self.gcx.node_adjustments(expr.id) {
            for adjustment in adjustments {
                thir_expr = self.apply_adjustment(expr.id, thir_expr, adjustment, expr.span);
            }
        }
        self.push_expr(thir_expr.kind, thir_expr.ty, thir_expr.span)
    }

    fn apply_adjustment(
        &mut self,
        _hir_id: hir::NodeID,
        expr: Expr<'ctx>,
        adjustment: Adjustment<'ctx>,
        span: crate::span::Span,
    ) -> Expr<'ctx> {
        let ty = expr.ty;
        match adjustment {
            Adjustment::Dereference => {
                let TyKind::Reference(inner, _) = ty.kind() else {
                    // Logic error if we try to deref non-ref type
                    return expr;
                };

                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::Deref(inner_id),
                    ty: inner,
                    span,
                }
            }
            Adjustment::BorrowMutable => {
                let ty = self
                    .gcx
                    .store
                    .interners
                    .intern_ty(TyKind::Reference(ty, Mutability::Mutable));

                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::Reference {
                        mutable: true,
                        expr: inner_id,
                    },
                    ty,
                    span,
                }
            }
            Adjustment::BorrowImmutable => {
                let ty = self
                    .gcx
                    .store
                    .interners
                    .intern_ty(TyKind::Reference(ty, Mutability::Immutable));
                let inner_id = self.push_expr(expr.kind, expr.ty, expr.span);

                Expr {
                    kind: ExprKind::Reference {
                        mutable: false,
                        expr: inner_id,
                    },
                    ty,
                    span,
                }
            }
            Adjustment::Ignore(_) => expr,
        }
    }

    fn lower_expr_unadjusted(&mut self, expr: &hir::Expression) -> Expr<'ctx> {
        let ty = self.gcx.get_node_type(expr.id);
        let span = expr.span;
        let kind = match &expr.kind {
            hir::ExpressionKind::Literal(lit) => {
                let value = self.lower_literal(lit);
                ExprKind::Literal(Constant { ty, value })
            }
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if matches!(&path.resolution, Resolution::LocalVariable(_)) =>
            {
                let Resolution::LocalVariable(id) = &path.resolution else {
                    unreachable!()
                };
                ExprKind::Local(*id)
            }
            hir::ExpressionKind::Call { callee, arguments } => {
                let callee_id: Option<DefinitionID> = match &callee.kind {
                    hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) => {
                        match &path.resolution {
                            Resolution::Definition(id, DefinitionKind::Function)
                            | Resolution::Definition(id, DefinitionKind::AssociatedFunction) => {
                                Some(*id)
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                };

                if let Some(id) = callee_id {
                    let args: Vec<ExprId> = arguments
                        .iter()
                        .map(|arg| self.lower_expr(&arg.expression))
                        .collect();
                    ExprKind::Call { callee: id, args }
                } else {
                    // Unsupported callee shape for now.
                    ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    })
                }
            }
            hir::ExpressionKind::Binary(op, lhs, rhs) => {
                let lhs = self.lower_expr(lhs);
                let rhs = self.lower_expr(rhs);
                ExprKind::Binary { op: *op, lhs, rhs }
            }
            hir::ExpressionKind::Unary(op, operand) => {
                let operand = self.lower_expr(operand);
                ExprKind::Unary { op: *op, operand }
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                let target = self.lower_expr(lhs);
                let value = self.lower_expr(rhs);
                ExprKind::Assign { target, value }
            }
            hir::ExpressionKind::If(node) => {
                let cond = self.lower_expr(&node.condition);
                let then_expr = self.lower_expr(&node.then_block);
                let else_expr = node.else_block.as_deref().map(|expr| self.lower_expr(expr));
                ExprKind::If {
                    cond,
                    then_expr,
                    else_expr,
                }
            }
            hir::ExpressionKind::Block(block) => {
                let block_id = self.lower_block(block, true);
                ExprKind::Block(block_id)
            }
            hir::ExpressionKind::Dereference(inner) => {
                let operand = self.lower_expr(inner);
                ExprKind::Deref(operand)
            }
            hir::ExpressionKind::Reference(inner, mutbl) => {
                let operand = self.lower_expr(inner);
                ExprKind::Reference {
                    mutable: *mutbl == hir::Mutability::Mutable,
                    expr: operand,
                }
            }
            hir::ExpressionKind::MethodCall {
                receiver,
                name: _,
                arguments,
            } => {
                // For now, lower method calls like regular calls with the receiver as first arg
                // when the callee resolved to a function id.
                // TODO: carry the resolved method id on HIR to avoid re-resolving here.
                let args: Vec<ExprId> = arguments
                    .iter()
                    .map(|arg| self.lower_expr(&arg.expression))
                    .collect();
                let recv = self.lower_expr(receiver);
                let mut all_args = Vec::with_capacity(args.len() + 1);
                all_args.push(recv);
                all_args.extend(args);
                // Without a resolved callee, emit an error literal for now.
                ExprKind::Literal(Constant {
                    ty: self.gcx.types.error,
                    value: ConstantKind::Unit,
                })
            }

            hir::ExpressionKind::StructLiteral(literal) => {
                let TyKind::Adt(definition) = ty.kind() else {
                    unreachable!()
                };

                if !matches!(definition.kind, AdtKind::Struct) {
                    unreachable!()
                }

                let node = thir::AdtExpression {
                    definition,
                    fields: literal
                        .fields
                        .iter()
                        .map(|f| thir::FieldExpression {
                            expression: self.lower_expr(&f.expression),
                            index: self
                                .gcx
                                .get_field_index(f.expression.id)
                                .expect("Field Index"),
                        })
                        .collect(),
                };

                ExprKind::Adt(node)
            }
            hir::ExpressionKind::Member { target, .. } => {
                let lhs = self.lower_expr(target);
                ExprKind::Field {
                    lhs,
                    index: self.gcx.get_field_index(expr.id).expect("Field Index"),
                }
            }
            hir::ExpressionKind::Tuple(elems) => {
                let fields = elems.iter().map(|e| self.lower_expr(&e)).collect();
                ExprKind::Tuple { fields }
            }
            hir::ExpressionKind::TupleAccess(target, ..) => {
                let lhs = self.lower_expr(target);
                ExprKind::Field {
                    lhs,
                    index: self.gcx.get_field_index(expr.id).expect("Field Index"),
                }
            }
            _ => {
                unimplemented!("hir node lowering pass");
            }
        };

        Expr { kind, ty, span }
    }

    fn lower_literal(&self, lit: &hir::Literal) -> ConstantKind {
        match lit {
            hir::Literal::Bool(b) => ConstantKind::Bool(*b),
            hir::Literal::Rune(r) => ConstantKind::Rune(*r),
            hir::Literal::String(s) => ConstantKind::String(*s),
            hir::Literal::Integer(i) => ConstantKind::Integer(*i),
            hir::Literal::Float(f) => ConstantKind::Float(*f),
            hir::Literal::Nil => ConstantKind::Unit,
        }
    }

    fn push_expr(&mut self, kind: ExprKind<'ctx>, ty: Ty<'ctx>, span: crate::span::Span) -> ExprId {
        let id = ExprId::from_raw(self.func.exprs.len() as u32);
        self.func.exprs.push(Expr { kind, ty, span });
        id
    }

    fn push_stmt(&mut self, stmt: Stmt<'ctx>) -> StmtId {
        let id = StmtId::from_raw(self.func.stmts.len() as u32);
        self.func.stmts.push(stmt);
        id
    }
}
