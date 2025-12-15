use crate::{
    compile::{context::GlobalContext, entry::validate_entry_point},
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, Mutability, Resolution},
    sema::models::{AdtKind, Ty, TyKind},
    thir::{
        self, Block, BlockId, Constant, ConstantKind, Expr, ExprId, ExprKind, Param, Stmt, StmtId,
        StmtKind, ThirFunction, ThirPackage,
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
        let name = match &local.pattern.kind {
            hir::PatternKind::Identifier(id) => Some(id.symbol),
            _ => todo!(),
        };
        let expr = local
            .initializer
            .as_deref()
            .map(|expr| self.lower_expr(expr));

        Stmt {
            kind: StmtKind::Let {
                id: local.id,
                pattern: local.pattern.id,
                name,
                mutable: local.mutability == Mutability::Mutable,
                expr,
                ty,
            },
            span: local.pattern.span,
        }
    }

    fn lower_expr(&mut self, expr: &hir::Expression) -> ExprId {
        let ty = self.gcx.get_node_type(expr.id);
        let span = expr.span;
        match &expr.kind {
            hir::ExpressionKind::Literal(lit) => {
                let value = self.lower_literal(lit);
                self.push_expr(ExprKind::Literal(Constant { ty, value }), ty, span)
            }
            hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path))
                if matches!(&path.resolution, Resolution::LocalVariable(_)) =>
            {
                let Resolution::LocalVariable(id) = &path.resolution else {
                    unreachable!()
                };
                self.push_expr(ExprKind::Local(*id), ty, span)
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
                    self.push_expr(ExprKind::Call { callee: id, args }, ty, span)
                } else {
                    // Unsupported callee shape for now.
                    self.push_expr(
                        ExprKind::Literal(Constant {
                            ty: self.gcx.types.error,
                            value: ConstantKind::Unit,
                        }),
                        self.gcx.types.error,
                        span,
                    )
                }
            }
            hir::ExpressionKind::Binary(op, lhs, rhs) => {
                let lhs = self.lower_expr(lhs);
                let rhs = self.lower_expr(rhs);
                self.push_expr(ExprKind::Binary { op: *op, lhs, rhs }, ty, span)
            }
            hir::ExpressionKind::Unary(op, operand) => {
                let operand = self.lower_expr(operand);
                self.push_expr(ExprKind::Unary { op: *op, operand }, ty, span)
            }
            hir::ExpressionKind::Assign(lhs, rhs) => {
                let target = self.lower_expr(lhs);
                let value = self.lower_expr(rhs);
                self.push_expr(ExprKind::Assign { target, value }, ty, span)
            }
            hir::ExpressionKind::If(node) => {
                let cond = self.lower_expr(&node.condition);
                let then_expr = self.lower_expr(&node.then_block);
                let else_expr = node.else_block.as_deref().map(|expr| self.lower_expr(expr));
                self.push_expr(
                    ExprKind::If {
                        cond,
                        then_expr,
                        else_expr,
                    },
                    ty,
                    span,
                )
            }
            hir::ExpressionKind::Block(block) => {
                let block_id = self.lower_block(block, true);
                self.push_expr(ExprKind::Block(block_id), ty, span)
            }
            hir::ExpressionKind::Dereference(inner) => {
                let operand = self.lower_expr(inner);
                self.push_expr(ExprKind::Deref(operand), ty, span)
            }
            hir::ExpressionKind::Reference(inner, mutbl) => {
                let operand = self.lower_expr(inner);
                self.push_expr(
                    ExprKind::Reference {
                        mutable: *mutbl == hir::Mutability::Mutable,
                        expr: operand,
                    },
                    ty,
                    span,
                )
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
                self.push_expr(
                    ExprKind::Literal(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    }),
                    self.gcx.types.error,
                    span,
                )
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

                self.push_expr(thir::ExprKind::Adt(node), ty, span)
            }
            hir::ExpressionKind::Member { target, .. } => {
                let lhs = self.lower_expr(target);
                self.push_expr(
                    thir::ExprKind::Field {
                        lhs,
                        index: self.gcx.get_field_index(expr.id).expect("Field Index"),
                    },
                    ty,
                    span,
                )
            }
            hir::ExpressionKind::Tuple(elems) => {
                let fields = elems.iter().map(|e| self.lower_expr(&e)).collect();
                self.push_expr(thir::ExprKind::Tuple { fields }, ty, span)
            }
            hir::ExpressionKind::TupleAccess(target, ..) => {
                let lhs = self.lower_expr(target);
                self.push_expr(
                    thir::ExprKind::Field {
                        lhs,
                        index: self.gcx.get_field_index(expr.id).expect("Field Index"),
                    },
                    ty,
                    span,
                )
            }
            _ => {
                unimplemented!("hir node lowering pass");
            }
        }
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
        self.func.exprs.push(Expr { id, kind, ty, span });
        id
    }

    fn push_stmt(&mut self, stmt: Stmt<'ctx>) -> StmtId {
        let id = StmtId::from_raw(self.func.stmts.len() as u32);
        self.func.stmts.push(stmt);
        id
    }
}
