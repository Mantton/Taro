use crate::{
    compile::context::Gcx,
    hir::{self, DefinitionID, DefinitionKind, Resolution},
    mir::{
        BasicBlock, BasicBlockId, Body, Constant, ConstantKind, LocalDecl, LocalId, LocalKind,
        Operand, Place, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
    },
    sema::models::Ty,
    span::{Span, Symbol},
};
use rustc_hash::FxHashMap;

#[derive(Debug)]
struct LoopScope {
    break_bb: BasicBlockId,
    continue_bb: BasicBlockId,
}

pub struct MirBuilder<'ctx> {
    gcx: Gcx<'ctx>,
    body: Body<'ctx>,
    current: Option<BasicBlockId>,
    locals: FxHashMap<hir::NodeID, LocalId>,
    loop_stack: Vec<LoopScope>,
}

impl<'ctx> MirBuilder<'ctx> {
    pub fn build_function(
        gcx: Gcx<'ctx>,
        def_id: DefinitionID,
        function: &hir::Function,
    ) -> Body<'ctx> {
        let signature = gcx.get_signature(def_id);
        let output_ty = signature.output;
        let entry_span = function.signature.span;

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
            body,
            current: Some(start_block),
            locals: FxHashMap::default(),
            loop_stack: vec![],
        };

        builder.declare_parameters(function, signature);
        builder.lower_body(function);
        builder.finish()
    }

    fn finish(self) -> Body<'ctx> {
        self.body
    }

    fn declare_parameters(
        &mut self,
        function: &hir::Function,
        signature: &crate::sema::models::LabeledFunctionSignature<'ctx>,
    ) {
        for (param, lowered) in function
            .signature
            .prototype
            .inputs
            .iter()
            .zip(signature.inputs.iter())
        {
            let local = self.push_local(
                lowered.ty,
                LocalKind::Param,
                Some(param.name.symbol),
                param.span,
            );
            self.locals.insert(param.id, local);
        }
    }

    fn lower_body(&mut self, function: &hir::Function) {
        let Some(block) = &function.block else {
            return;
        };

        self.lower_block(block);

        if let Some(bb) = self.current {
            if !self.is_terminated(bb) {
                self.set_terminator(block.span, TerminatorKind::Return);
                self.current = None;
            }
        }
    }

    fn lower_block(&mut self, block: &hir::Block) {
        for stmt in &block.statements {
            if self.current.is_none() {
                break;
            }
            self.lower_statement(stmt);
        }
    }

    fn lower_statement(&mut self, stmt: &hir::Statement) {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => {
                // Declarations are not part of MIR; ignore.
            }
            hir::StatementKind::Expression(expr) => {
                let _ = self.lower_expr(expr);
            }
            hir::StatementKind::Variable(local) => {
                self.lower_local(local);
            }
            hir::StatementKind::Break => self.lower_break(stmt.span),
            hir::StatementKind::Continue => self.lower_continue(stmt.span),
            hir::StatementKind::Return(expr) => self.lower_return(stmt.span, expr.as_deref()),
            hir::StatementKind::Loop { block, .. } => self.lower_loop(block, stmt.span),
            hir::StatementKind::Defer(_) => {
                // Not yet supported; keep the block well-formed.
            }
            hir::StatementKind::Guard { .. } => {
                // Not yet supported.
            }
        }
    }

    fn lower_local(&mut self, local: &hir::Local) {
        let ty = self.gcx.get_node_type(local.id);
        let name = match &local.pattern.kind {
            hir::PatternKind::Identifier(id) => Some(id.symbol),
            _ => None,
        };
        let lid = self.push_local(ty, LocalKind::User, name, local.pattern.span);
        self.locals.insert(local.pattern.id, lid);
        self.locals.insert(local.id, lid);

        if let Some(init) = &local.initializer {
            let value = self.lower_expr(init);
            self.push_statement(
                local.pattern.span,
                StatementKind::Assign(Place { local: lid }, Rvalue::Use(value)),
            );
        }
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

    fn lower_loop(&mut self, block: &hir::Block, span: Span) {
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

    fn lower_return(&mut self, span: Span, expr: Option<&hir::Expression>) {
        if let Some(value) = expr {
            let operand = self.lower_expr(value);
            let dest = Place {
                local: self.body.return_local,
            };
            self.push_statement(span, StatementKind::Assign(dest, Rvalue::Use(operand)));
        }

        self.set_terminator(span, TerminatorKind::Return);
        self.current = None;
    }

    fn lower_expr(&mut self, expr: &hir::Expression) -> Operand<'ctx> {
        match &expr.kind {
            hir::ExpressionKind::Literal(lit) => {
                let ty = self.gcx.get_node_type(expr.id);
                Operand::Constant(Constant {
                    ty,
                    value: self.lower_literal(lit),
                })
            }
            hir::ExpressionKind::Identifier(_, res) => self.lower_identifier(expr, res),
            hir::ExpressionKind::Call(callee, args) => self.lower_call(expr, callee, args),
            hir::ExpressionKind::Binary(op, lhs, rhs) => {
                let lhs_op = self.lower_expr(lhs);
                let rhs_op = self.lower_expr(rhs);
                let dest = self.new_temp_for(expr);
                self.push_statement(
                    expr.span,
                    StatementKind::Assign(
                        dest,
                        Rvalue::BinaryOp {
                            op: *op,
                            lhs: lhs_op,
                            rhs: rhs_op,
                        },
                    ),
                );
                Operand::Copy(dest)
            }
            hir::ExpressionKind::Unary(op, operand) => {
                let operand = self.lower_expr(operand);
                let dest = self.new_temp_for(expr);
                self.push_statement(
                    expr.span,
                    StatementKind::Assign(dest, Rvalue::UnaryOp { op: *op, operand }),
                );
                Operand::Copy(dest)
            }
            hir::ExpressionKind::Assign(lhs, rhs) => self.lower_assign(expr, lhs, rhs),
            hir::ExpressionKind::If(node) => self.lower_if(expr, node),
            hir::ExpressionKind::Block(block) => self.lower_block_expr(block, expr),
            _ => {
                // Future features not yet lowered.
                Operand::Constant(Constant {
                    ty: self.gcx.types.error,
                    value: ConstantKind::Unit,
                })
            }
        }
    }

    fn lower_literal(&self, lit: &hir::Literal) -> ConstantKind<'ctx> {
        match lit {
            hir::Literal::Bool(b) => ConstantKind::Bool(*b),
            hir::Literal::Rune(r) => ConstantKind::Rune(*r),
            hir::Literal::String(s) => ConstantKind::String(*s),
            hir::Literal::Integer(i) => ConstantKind::Integer(*i),
            hir::Literal::Float(f) => ConstantKind::Float(*f),
            hir::Literal::Nil => todo!(),
        }
    }

    fn lower_identifier(&self, expr: &hir::Expression, resolution: &Resolution) -> Operand<'ctx> {
        match resolution {
            Resolution::LocalVariable(id) => {
                let local = *self
                    .locals
                    .get(id)
                    .expect("MIR local for identifier must exist");
                Operand::Copy(Place { local })
            }
            Resolution::Definition(id, DefinitionKind::Function) => {
                let ty = self.gcx.get_node_type(expr.id);
                Operand::Constant(Constant {
                    ty,
                    value: ConstantKind::Function(*id, ty),
                })
            }
            _ => Operand::Constant(Constant {
                ty: self.gcx.types.error,
                value: ConstantKind::Unit,
            }),
        }
    }

    fn lower_call(
        &mut self,
        expr: &hir::Expression,
        callee: &hir::Expression,
        args: &[hir::ExpressionArgument],
    ) -> Operand<'ctx> {
        let func_op = self.lower_expr(callee);
        let arg_ops: Vec<Operand<'ctx>> = args
            .iter()
            .map(|a| self.lower_expr(&a.expression))
            .collect();
        let dest_place = self.new_temp_for(expr);
        let target = self.new_block();

        if let Some(bb) = self.current {
            self.body.basic_blocks[bb].terminator = Some(Terminator {
                kind: TerminatorKind::Call {
                    func: func_op,
                    args: arg_ops,
                    destination: dest_place,
                    target,
                },
                span: expr.span,
            });
        }

        self.current = Some(target);
        Operand::Copy(dest_place)
    }

    fn lower_if(&mut self, expr: &hir::Expression, node: &hir::IfExpression) -> Operand<'ctx> {
        let cond = self.lower_expr(&node.condition);
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

        let dest_place = self.new_temp_for(expr);

        // then branch
        self.current = Some(then_bb);
        self.assign_expr_to_place(dest_place, &node.then_block);
        if let Some(bb) = self.current {
            if !self.is_terminated(bb) {
                self.set_terminator(expr.span, TerminatorKind::Goto { target: join_bb });
            }
        }

        // else branch
        self.current = Some(else_bb);
        if let Some(else_expr) = &node.else_block {
            self.assign_expr_to_place(dest_place, else_expr);
        } else {
            let unit = Operand::Constant(Constant {
                ty: self.gcx.types.void,
                value: ConstantKind::Unit,
            });
            self.push_statement(
                expr.span,
                StatementKind::Assign(dest_place, Rvalue::Use(unit)),
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

    fn assign_expr_to_place(&mut self, place: Place, expr: &hir::Expression) {
        let value = self.lower_expr(expr);
        self.push_statement(expr.span, StatementKind::Assign(place, Rvalue::Use(value)));
    }

    fn lower_assign(
        &mut self,
        expr: &hir::Expression,
        lhs: &hir::Expression,
        rhs: &hir::Expression,
    ) -> Operand<'ctx> {
        match &lhs.kind {
            hir::ExpressionKind::Identifier(_, res) => {
                if let hir::Resolution::LocalVariable(id) = res {
                    let local = *self.locals.get(id).expect("assignment target local");
                    let place = Place { local };
                    let rhs_op = self.lower_expr(rhs);
                    self.push_statement(expr.span, StatementKind::Assign(place, Rvalue::Use(rhs_op)));
                    Operand::Constant(Constant {
                        ty: self.gcx.types.void,
                        value: ConstantKind::Unit,
                    })
                } else {
                    Operand::Constant(Constant {
                        ty: self.gcx.types.error,
                        value: ConstantKind::Unit,
                    })
                }
            }
            hir::ExpressionKind::Dereference(ptr_expr) => {
                let ptr = self.lower_expr(ptr_expr);
                let value = self.lower_expr(rhs);
                self.push_statement(
                    expr.span,
                    StatementKind::Store { ptr, value: value.clone() },
                );
                Operand::Constant(Constant {
                    ty: self.gcx.types.void,
                    value: ConstantKind::Unit,
                })
            }
            _ => Operand::Constant(Constant {
                ty: self.gcx.types.error,
                value: ConstantKind::Unit,
            }),
        }
    }

    fn lower_block_expr(&mut self, block: &hir::Block, expr: &hir::Expression) -> Operand<'ctx> {
        let mut last_value: Option<Operand<'ctx>> = None;

        for stmt in &block.statements {
            if self.current.is_none() {
                break;
            }
            match &stmt.kind {
                hir::StatementKind::Expression(inner) => {
                    last_value = Some(self.lower_expr(inner));
                }
                _ => {
                    last_value = None;
                    self.lower_statement(stmt);
                }
            }
        }

        match last_value {
            Some(op) => op,
            None => Operand::Constant(Constant {
                ty: self.gcx.get_node_type(expr.id),
                value: ConstantKind::Unit,
            }),
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

    fn new_temp_for(&mut self, expr: &hir::Expression) -> Place {
        let ty = self.gcx.get_node_type(expr.id);
        let local = self.push_local(ty, LocalKind::Temp, None, expr.span);
        Place { local }
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
