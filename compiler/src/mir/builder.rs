use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID},
    mir::{
        BasicBlock, BasicBlockId, Body, Constant, ConstantKind, LocalDecl, LocalId, LocalKind,
        Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    sema::models::Ty,
    span::{Span, Symbol},
    thir,
};
use rustc_hash::FxHashMap;

#[derive(Debug)]
struct LoopScope {
    break_bb: BasicBlockId,
    continue_bb: BasicBlockId,
}

pub struct MirBuilder<'ctx, 'thir> {
    gcx: Gcx<'ctx>,
    thir: &'thir thir::ThirFunction<'ctx>,
    body: Body<'ctx>,
    current: Option<BasicBlockId>,
    locals: FxHashMap<hir::NodeID, LocalId>,
    loop_stack: Vec<LoopScope>,
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn build_function(gcx: Gcx<'ctx>, function: &'thir thir::ThirFunction<'ctx>) -> Body<'ctx> {
        let signature = gcx.get_signature(function.id);
        let output_ty = signature.output;
        let entry_span = function.span;

        let mut body = Body {
            locals: Default::default(),
            basic_blocks: Default::default(),
            start_block: BasicBlockId::from_raw(0),
            return_local: LocalId::from_raw(0),
        };

        // Create return place first.
        let ret_local = body.locals.push(LocalDecl {
            ty: output_ty,
            kind: LocalKind::Return,
            name: Some(Symbol::new("$ret")),
            span: entry_span,
        });
        body.return_local = ret_local;

        let start_block = body.basic_blocks.push(BasicBlock {
            statements: vec![],
            terminator: None,
        });
        body.start_block = start_block;

        let mut builder = MirBuilder {
            gcx,
            thir: function,
            body,
            current: Some(start_block),
            locals: FxHashMap::default(),
            loop_stack: vec![],
        };

        builder.declare_parameters(signature);
        builder.lower_body();
        builder.finish()
    }

    fn finish(self) -> Body<'ctx> {
        self.body
    }

    fn declare_parameters(
        &mut self,
        signature: &crate::sema::models::LabeledFunctionSignature<'ctx>,
    ) {
        let params: Vec<_> = self
            .thir
            .params
            .iter()
            .zip(signature.inputs.iter())
            .map(|(param, lowered)| (param.id, param.name, param.span, lowered.ty))
            .collect();
        for (id, name, span, ty) in params {
            let local = self.push_local(ty, LocalKind::Param, Some(name), span);
            self.locals.insert(id, local);
        }
    }

    fn lower_body(&mut self) {
        let Some(block) = self.thir.body else {
            return;
        };

        self.lower_block(block);

        if let Some(bb) = self.current {
            if !self.is_terminated(bb) {
                self.set_terminator(self.thir.span, TerminatorKind::Return);
                self.current = None;
            }
        }
    }

    fn lower_block(&mut self, block: thir::BlockId) {
        let stmts = self.thir.blocks[block].stmts.clone();
        for stmt in stmts {
            if self.current.is_none() {
                break;
            }
            let stmt_node = &self.thir.stmts[stmt];
            self.lower_statement(stmt_node);
        }
    }

    fn lower_statement(&mut self, stmt: &thir::Stmt<'ctx>) {
        match &stmt.kind {
            thir::StmtKind::Let {
                id,
                pattern,
                mutable: _,
                expr,
                ty,
                name,
            } => {
                self.lower_local(*id, *pattern, *ty, *name, expr.as_ref(), stmt.span);
            }
            thir::StmtKind::Assign { target, value } => {
                self.lower_assign_stmt(*target, *value, stmt.span);
            }
            thir::StmtKind::Break => self.lower_break(stmt.span),
            thir::StmtKind::Continue => self.lower_continue(stmt.span),
            thir::StmtKind::Return { value } => {
                self.lower_return(stmt.span, value.as_ref().copied())
            }
            thir::StmtKind::Loop { block, .. } => self.lower_loop(*block, stmt.span),
            thir::StmtKind::Expr(expr) => {
                let _ = self.lower_expr_id(*expr);
            }
        }
    }

    fn lower_local(
        &mut self,
        id: hir::NodeID,
        pattern: hir::NodeID,
        ty: Ty<'ctx>,
        name: Option<Symbol>,
        init: Option<&thir::ExprId>,
        span: Span,
    ) {
        let lid = self.push_local(ty, LocalKind::User, name, span);
        self.locals.insert(id, lid);
        self.locals.insert(pattern, lid);

        if let Some(init) = init {
            let value = self.lower_expr_id(*init);
            self.push_statement(
                span,
                StatementKind::Assign(
                    Place {
                        local: lid,
                        projection: vec![],
                    },
                    Rvalue::Use(value),
                ),
            );
        }
    }

    fn lower_assign_stmt(&mut self, target: thir::ExprId, value: thir::ExprId, span: Span) {
        let dest = self.place_from_expr(target, span);
        let rhs = self.lower_expr_id(value);
        self.push_statement(span, StatementKind::Assign(dest, Rvalue::Use(rhs)));
    }

    fn lower_break(&mut self, span: Span) {
        if let (Some(_), Some(scope)) = (self.current, self.loop_stack.last()) {
            self.set_terminator(
                span,
                TerminatorKind::Goto {
                    target: scope.break_bb,
                },
            );
            self.current = None;
        }
    }

    fn lower_continue(&mut self, span: Span) {
        if let (Some(_), Some(scope)) = (self.current, self.loop_stack.last()) {
            self.set_terminator(
                span,
                TerminatorKind::Goto {
                    target: scope.continue_bb,
                },
            );
            self.current = None;
        }
    }

    fn lower_loop(&mut self, block: thir::BlockId, span: Span) {
        let header = self.new_block();
        let break_bb = self.new_block();

        if let Some(bb) = self.current {
            if !self.is_terminated(bb) {
                self.set_terminator(span, TerminatorKind::Goto { target: header });
            }
        }

        self.current = Some(header);
        self.loop_stack.push(LoopScope {
            break_bb,
            continue_bb: header,
        });
        self.lower_block(block);
        self.loop_stack.pop();

        if let Some(bb) = self.current {
            if !self.is_terminated(bb) {
                self.set_terminator(span, TerminatorKind::Goto { target: header });
            }
        }

        self.current = Some(break_bb);
    }

    fn lower_return(&mut self, span: Span, expr: Option<thir::ExprId>) {
        if let Some(value) = expr {
            let operand = self.lower_expr_id(value);
            let dest = Place {
                local: self.body.return_local,
                projection: vec![],
            };
            self.push_statement(span, StatementKind::Assign(dest, Rvalue::Use(operand)));
        }

        self.set_terminator(span, TerminatorKind::Return);
        self.current = None;
    }

    fn lower_expr_id(&mut self, expr: thir::ExprId) -> Operand<'ctx> {
        let expr = &self.thir.exprs[expr];
        self.lower_expr(expr)
    }

    fn lower_expr(&mut self, expr: &thir::Expr<'ctx>) -> Operand<'ctx> {
        match &expr.kind {
            thir::ExprKind::Literal(lit) => Operand::Constant(self.lower_constant(&lit)),
            thir::ExprKind::Local(id) => {
                let local = *self.locals.get(&id).expect("MIR local for identifier");
                Operand::Copy(Place {
                    local,
                    projection: vec![],
                })
            }
            thir::ExprKind::Reference { .. } => Operand::Constant(Constant {
                ty: self.gcx.types.error,
                value: ConstantKind::Unit,
            }),
            thir::ExprKind::Deref(_) => Operand::Constant(Constant {
                ty: self.gcx.types.error,
                value: ConstantKind::Unit,
            }),
            thir::ExprKind::Call { callee, args } => self.lower_call(expr, *callee, args),
            thir::ExprKind::Binary { op, lhs, rhs } => {
                let lhs_op = self.lower_expr_id(*lhs);
                let rhs_op = self.lower_expr_id(*rhs);
                let dest = self.new_temp(expr.ty, expr.span);
                self.push_statement(
                    expr.span,
                    StatementKind::Assign(
                        dest.clone(),
                        Rvalue::BinaryOp {
                            op: *op,
                            lhs: lhs_op,
                            rhs: rhs_op,
                        },
                    ),
                );
                Operand::Copy(dest)
            }
            thir::ExprKind::Unary { op, operand } => {
                let operand = self.lower_expr_id(*operand);
                let dest = self.new_temp(expr.ty, expr.span);
                self.push_statement(
                    expr.span,
                    StatementKind::Assign(dest.clone(), Rvalue::UnaryOp { op: *op, operand }),
                );
                Operand::Copy(dest)
            }
            thir::ExprKind::Assign { target, value } => {
                self.lower_assign_expr(expr, *target, *value)
            }
            thir::ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => self.lower_if(expr, *cond, *then_expr, *else_expr),
            thir::ExprKind::Block(block) => self.lower_block_expr(*block, expr),
        }
    }

    fn lower_constant(&self, lit: &thir::Constant<'ctx>) -> Constant<'ctx> {
        let value = match &lit.value {
            thir::ConstantKind::Bool(b) => ConstantKind::Bool(*b),
            thir::ConstantKind::Rune(r) => ConstantKind::Rune(*r),
            thir::ConstantKind::String(s) => ConstantKind::String(*s),
            thir::ConstantKind::Integer(i) => ConstantKind::Integer(*i),
            thir::ConstantKind::Float(f) => ConstantKind::Float(*f),
            thir::ConstantKind::Unit => ConstantKind::Unit,
        };
        Constant { ty: lit.ty, value }
    }

    fn lower_call(
        &mut self,
        expr: &thir::Expr<'ctx>,
        callee: DefinitionID,
        args: &[thir::ExprId],
    ) -> Operand<'ctx> {
        let func_ty = self.gcx.get_type(callee);
        let func_op = Operand::Constant(Constant {
            ty: func_ty,
            value: ConstantKind::Function(callee, func_ty),
        });
        let arg_ops: Vec<Operand<'ctx>> = args.iter().map(|a| self.lower_expr_id(*a)).collect();
        let dest_place = self.new_temp(expr.ty, expr.span);
        let target = self.new_block();

        if let Some(bb) = self.current {
            self.body.basic_blocks[bb].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: func_op,
                    args: arg_ops,
                    destination: dest_place.clone(),
                    target,
                },
                span: expr.span,
            });
        }

        self.current = Some(target);
        Operand::Copy(dest_place)
    }

    fn lower_if(
        &mut self,
        expr: &thir::Expr<'ctx>,
        cond: thir::ExprId,
        then_expr: thir::ExprId,
        else_expr: Option<thir::ExprId>,
    ) -> Operand<'ctx> {
        let cond = self.lower_expr_id(cond);
        let then_bb = self.new_block();
        let else_bb = self.new_block();
        let join_bb = self.new_block();

        if self.current.is_some() {
            self.set_terminator(
                expr.span,
                TerminatorKind::SwitchInt {
                    discr: cond,
                    targets: vec![(1, then_bb)],
                    otherwise: else_bb,
                },
            );
        }

        let dest_place = self.new_temp(expr.ty, expr.span);

        // then branch
        self.current = Some(then_bb);
        self.assign_expr_to_place(dest_place.clone(), then_expr);
        if let Some(bb) = self.current {
            if !self.is_terminated(bb) {
                self.set_terminator(expr.span, TerminatorKind::Goto { target: join_bb });
            }
        }

        // else branch
        self.current = Some(else_bb);
        if let Some(else_expr) = else_expr {
            self.assign_expr_to_place(dest_place.clone(), else_expr);
        } else {
            let unit = Operand::Constant(Constant {
                ty: self.gcx.types.void,
                value: ConstantKind::Unit,
            });
            self.push_statement(
                expr.span,
                StatementKind::Assign(dest_place.clone(), Rvalue::Use(unit)),
            );
        }
        if let Some(bb) = self.current {
            if !self.is_terminated(bb) {
                self.set_terminator(expr.span, TerminatorKind::Goto { target: join_bb });
            }
        }

        self.current = Some(join_bb);
        Operand::Copy(dest_place)
    }

    fn assign_expr_to_place(&mut self, place: Place, expr: thir::ExprId) {
        let value = self.lower_expr_id(expr);
        let span = self.thir.exprs[expr].span;
        self.push_statement(span, StatementKind::Assign(place, Rvalue::Use(value)));
    }

    fn lower_assign_expr(
        &mut self,
        expr: &thir::Expr<'ctx>,
        target: thir::ExprId,
        rhs: thir::ExprId,
    ) -> Operand<'ctx> {
        let dest = self.place_from_expr(target, expr.span);
        let rhs_op = self.lower_expr_id(rhs);
        self.push_statement(expr.span, StatementKind::Assign(dest, Rvalue::Use(rhs_op)));
        Operand::Constant(Constant {
            ty: self.gcx.types.void,
            value: ConstantKind::Unit,
        })
    }

    fn lower_block_expr(
        &mut self,
        block_id: thir::BlockId,
        expr: &thir::Expr<'ctx>,
    ) -> Operand<'ctx> {
        let (block_expr, stmts) = {
            let block = &self.thir.blocks[block_id];
            (block.expr, block.stmts.clone())
        };
        for stmt in stmts {
            if self.current.is_none() {
                break;
            }
            let stmt_node = &self.thir.stmts[stmt];
            self.lower_statement(stmt_node);
        }

        if self.current.is_none() {
            return Operand::Constant(Constant {
                ty: expr.ty,
                value: ConstantKind::Unit,
            });
        }

        if let Some(expr_id) = block_expr {
            return self.lower_expr_id(expr_id);
        }

        Operand::Constant(Constant {
            ty: expr.ty,
            value: ConstantKind::Unit,
        })
    }

    fn place_from_expr(&mut self, expr: thir::ExprId, span: Span) -> Place {
        match &self.thir.exprs[expr].kind {
            thir::ExprKind::Local(id) => {
                let local = *self.locals.get(id).expect("lhs local");
                Place {
                    local,
                    projection: vec![],
                }
            }
            thir::ExprKind::Deref(inner) => {
                let ptr_place = self.place_from_expr(*inner, span);
                let base_local = ptr_place.local;
                // If there are existing projections, keep them and add Deref at end.
                let mut projection = ptr_place.projection;
                projection.push(crate::mir::PlaceElem::Deref);
                Place {
                    local: base_local,
                    projection,
                }
            }
            _ => {
                // Fallback: create a temp to hold the value, then deref it.
                let operand = self.lower_expr_id(expr);
                let tmp = self.push_local(self.thir.exprs[expr].ty, LocalKind::Temp, None, span);
                self.push_statement(
                    span,
                    StatementKind::Assign(
                        Place {
                            local: tmp,
                            projection: vec![],
                        },
                        Rvalue::Use(operand),
                    ),
                );
                Place {
                    local: tmp,
                    projection: vec![crate::mir::PlaceElem::Deref],
                }
            }
        }
    }

    fn push_local(
        &mut self,
        ty: Ty<'ctx>,
        kind: LocalKind,
        name: Option<Symbol>,
        span: Span,
    ) -> LocalId {
        self.body.locals.push(LocalDecl {
            ty,
            kind,
            name,
            span,
        })
    }

    fn new_temp(&mut self, ty: Ty<'ctx>, span: Span) -> Place {
        let local = self.push_local(ty, LocalKind::Temp, None, span);
        Place {
            local,
            projection: vec![],
        }
    }

    fn new_block(&mut self) -> BasicBlockId {
        self.body.basic_blocks.push(BasicBlock {
            statements: vec![],
            terminator: None,
        })
    }

    fn push_statement(&mut self, span: Span, kind: StatementKind<'ctx>) {
        if let Some(bb) = self.current {
            self.body.basic_blocks[bb]
                .statements
                .push(Statement { kind, span });
        }
    }

    fn set_terminator(&mut self, span: Span, kind: TerminatorKind<'ctx>) {
        if let Some(bb) = self.current {
            self.body.basic_blocks[bb].terminator = Some(Terminator { kind, span });
        }
    }

    fn is_terminated(&self, bb: BasicBlockId) -> bool {
        self.body.basic_blocks[bb].terminator.is_some()
    }
}
