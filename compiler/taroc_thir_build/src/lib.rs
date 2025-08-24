use taroc_error::CompileResult;
use taroc_hir::visitor::HirVisitor;
use taroc_sema::{GlobalContext, typing::TypingResult};
use taroc_span::Spanned;
use taroc_thir::{BlockID, ExpressionID, StatementID, ThirBody};

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor { context }
    }

    fn run(package: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let mut actor = Actor::new(context);
        taroc_hir::visitor::walk_package(&mut actor, package); // Collect Top Level
        context.diagnostics.report()
    }
}

impl HirVisitor for Actor<'_> {
    fn visit_function(
        &mut self,
        id: taroc_hir::NodeID,
        f: &taroc_hir::Function,
        _: taroc_hir::visitor::FunctionContext,
    ) -> Self::Result {
        let Some(block) = &f.block else {
            return;
        };
        let def = self.context.def_id(id);

        let result = self
            .context
            .with_type_database(def.package(), |db| db.typing_results.get(&def).cloned());

        let Some(result) = result else {
            unreachable!("typing result of function body")
        };
        let build_context = BuildContext {
            gcx: self.context,
            thir: Default::default(),
            result,
        };

        let _ = build_context.build(block);
    }
}

struct BuildContext<'ctx> {
    gcx: GlobalContext<'ctx>,
    thir: ThirBody<'ctx>,
    result: &'ctx TypingResult<'ctx>,
}

impl<'ctx> BuildContext<'ctx> {
    fn build(mut self, block: &taroc_hir::Block) -> (ThirBody<'ctx>) {
        let block = self.build_block(block);
        self.thir
    }

    fn build_block(&mut self, node: &taroc_hir::Block) -> BlockID {
        let statments = self.build_statements(&node.statements);
        let block = taroc_thir::Block {
            span: node.span,
            statments,
        };
        self.thir.blocks.push(block)
    }

    fn build_statements(&mut self, nodes: &[taroc_hir::Statement]) -> Vec<StatementID> {
        nodes
            .iter()
            .filter_map(|s| self.build_statement(s))
            .collect()
    }

    fn build_statement(&mut self, node: &taroc_hir::Statement) -> Option<StatementID> {
        self.gcx
            .diagnostics
            .warn(format!("Building StmtNode"), node.span);
        let kind = match &node.kind {
            taroc_hir::StatementKind::Declaration(_) => return None,
            taroc_hir::StatementKind::Expression(expression) => {
                taroc_thir::StatementKind::Expression(self.build_expression(expression))
            }
            taroc_hir::StatementKind::Variable(local) => taroc_thir::StatementKind::Let {
                initializer: local.initializer.as_ref().map(|i| self.build_expression(i)),
                span: node.span,
            },
            taroc_hir::StatementKind::Break(_) => taroc_thir::StatementKind::Break,
            taroc_hir::StatementKind::Continue(_) => taroc_thir::StatementKind::Continue,
            taroc_hir::StatementKind::Return(expression) => taroc_thir::StatementKind::Return(
                expression.as_ref().map(|e| self.build_expression(&e)),
            ),
            taroc_hir::StatementKind::Loop(label, block) => todo!(),
            taroc_hir::StatementKind::Defer(block) => todo!(),
        };

        let statement = taroc_thir::Statement { kind };
        Some(self.thir.statements.push(statement))
    }
}

impl<'ctx> BuildContext<'ctx> {
    fn build_expressions(&mut self, nodes: &[taroc_hir::Expression]) -> Vec<ExpressionID> {
        nodes.iter().map(|e| self.build_expression(e)).collect()
    }
    fn build_expression(&mut self, node: &taroc_hir::Expression) -> ExpressionID {
        let mut expression = self.build_expression_node(node);
        // TODO: Apply Adjustments

        self.thir.expressions.push(expression)
    }

    fn build_expression_node(
        &mut self,
        node: &taroc_hir::Expression,
    ) -> taroc_thir::Expression<'ctx> {
        let gcx = self.gcx;
        let ty = self.result.type_of(node.id);
        gcx.diagnostics.warn(
            format!("Building ExprNode, type is {}", ty.format(gcx)),
            node.span,
        );
        let kind = match &node.kind {
            taroc_hir::ExpressionKind::Binary(op, lhs, rhs) => {
                if self.result.is_method_call(node) {
                    let lhs = self.build_expression(lhs);
                    let rhs = self.build_expression(rhs);
                    todo!()
                } else {
                    match op {
                        taroc_hir::BinaryOperator::BoolAnd => {
                            taroc_thir::ExpressionKind::LogicalOp {
                                op: taroc_thir::LogicalOperator::And,
                                lhs: self.build_expression(lhs),
                                rhs: self.build_expression(rhs),
                            }
                        }
                        taroc_hir::BinaryOperator::BoolOr => {
                            taroc_thir::ExpressionKind::LogicalOp {
                                op: taroc_thir::LogicalOperator::Or,
                                lhs: self.build_expression(lhs),
                                rhs: self.build_expression(rhs),
                            }
                        }
                        _ => {
                            let op = bin_op(*op);
                            taroc_thir::ExpressionKind::Binary {
                                op,
                                lhs: self.build_expression(lhs),
                                rhs: self.build_expression(rhs),
                            }
                        }
                    }
                }
            }
            taroc_hir::ExpressionKind::Unary(taroc_hir::UnaryOperator::Negate, rhs) => {
                if self.result.is_method_call(node) {
                    let rhs = self.build_expression(rhs);
                    todo!()
                } else if let taroc_hir::ExpressionKind::Literal(lit) = &rhs.kind {
                    taroc_thir::ExpressionKind::Literal {
                        value: Spanned::new(lit.clone(), node.span),
                        negate: true,
                    }
                } else {
                    taroc_thir::ExpressionKind::Unary {
                        op: taroc_thir::UnaryOp::Neg,
                        rhs: self.build_expression(rhs),
                    }
                }
            }
            taroc_hir::ExpressionKind::Unary(taroc_hir::UnaryOperator::LogicalNot, rhs) => {
                if self.result.is_method_call(node) {
                    let rhs = self.build_expression(rhs);
                    todo!()
                } else {
                    taroc_thir::ExpressionKind::Unary {
                        op: taroc_thir::UnaryOp::Not,
                        rhs: self.build_expression(rhs),
                    }
                }
            }
            taroc_hir::ExpressionKind::Unary(taroc_hir::UnaryOperator::BitwiseNot, rhs) => {
                if self.result.is_method_call(node) {
                    let rhs = self.build_expression(rhs);
                    todo!()
                } else {
                    taroc_thir::ExpressionKind::Unary {
                        op: taroc_thir::UnaryOp::BitNot,
                        rhs: self.build_expression(rhs),
                    }
                }
            }

            taroc_hir::ExpressionKind::Literal(literal) => taroc_thir::ExpressionKind::Literal {
                value: Spanned::new(literal.clone(), node.span),
                negate: false,
            },
            taroc_hir::ExpressionKind::Path(path) => {
                let resolution = self.result.path_resolution(node.id, path, gcx);
                self.build_from_path(node, resolution)
            }
            taroc_hir::ExpressionKind::FunctionCall(expression, expression_arguments) => {
                taroc_thir::ExpressionKind::Call {
                    fn_ty: self.result.type_of(expression.id),
                    func: self.build_expression(expression),
                    arguments: expression_arguments
                        .iter()
                        .map(|e| self.build_expression(&e.expression))
                        .collect(),
                    from_overload: false,
                    fn_span: expression.span,
                }
            }
            taroc_hir::ExpressionKind::StructLiteral(struct_literal) => todo!(),
            taroc_hir::ExpressionKind::ArrayLiteral(expressions) => todo!(),
            taroc_hir::ExpressionKind::Tuple(expressions) => todo!(),
            taroc_hir::ExpressionKind::If(if_expression) => todo!(),
            taroc_hir::ExpressionKind::Match(match_expression) => todo!(),
            taroc_hir::ExpressionKind::MethodCall(method_call) => todo!(),
            taroc_hir::ExpressionKind::Reference(expression, mutability) => todo!(),
            taroc_hir::ExpressionKind::Dereference(expression) => todo!(),
            taroc_hir::ExpressionKind::FieldAccess(expression, path_segment) => todo!(),
            taroc_hir::ExpressionKind::TupleAccess(expression, anon_const) => todo!(),
            taroc_hir::ExpressionKind::Subscript(expression, expression_arguments) => todo!(),
            taroc_hir::ExpressionKind::AssignOp(binary_operator, expression, expression1) => {
                todo!()
            }
            taroc_hir::ExpressionKind::Assign(lhs, rhs) => taroc_thir::ExpressionKind::Assign(
                self.build_expression(lhs),
                self.build_expression(rhs),
            ),
            taroc_hir::ExpressionKind::CastAs(expression, _) => todo!(),

            taroc_hir::ExpressionKind::Block(block) => {
                let id = self.build_block(block);
                taroc_thir::ExpressionKind::Block(id)
            }
            taroc_hir::ExpressionKind::Closure(..)
            | taroc_hir::ExpressionKind::PatternBinding(..)
            | taroc_hir::ExpressionKind::Await(..) => todo!(),
            taroc_hir::ExpressionKind::Malformed => unreachable!(),
        };

        return taroc_thir::Expression {
            ty,
            span: node.span,
            kind,
        };
    }
}

impl<'ctx> BuildContext<'ctx> {
    fn build_from_path(
        &self,
        _: &taroc_hir::Expression,
        resolution: taroc_hir::Resolution,
    ) -> taroc_thir::ExpressionKind<'ctx> {
        match resolution {
            taroc_hir::Resolution::Local(node_id) => {
                taroc_thir::ExpressionKind::VariableReference(node_id)
            }
            _ => taroc_thir::ExpressionKind::Placeholder, // TODO
        }
    }
}

fn bin_op(op: taroc_hir::BinaryOperator) -> taroc_thir::BinaryOperator {
    type Op = taroc_thir::BinaryOperator;
    match op {
        taroc_hir::BinaryOperator::Add => Op::Add,
        taroc_hir::BinaryOperator::Sub => Op::Sub,
        taroc_hir::BinaryOperator::Mul => Op::Mul,
        taroc_hir::BinaryOperator::Div => Op::Div,
        taroc_hir::BinaryOperator::Rem => Op::Rem,
        taroc_hir::BinaryOperator::BitAnd => Op::BitAnd,
        taroc_hir::BinaryOperator::BitOr => Op::BitOr,
        taroc_hir::BinaryOperator::BitXor => Op::BitXor,
        taroc_hir::BinaryOperator::BitShl => Op::Shl,
        taroc_hir::BinaryOperator::BitShr => Op::Shr,
        taroc_hir::BinaryOperator::Eql => Op::Eq,
        taroc_hir::BinaryOperator::Lt => Op::Lt,
        taroc_hir::BinaryOperator::Gt => Op::Gt,
        taroc_hir::BinaryOperator::Leq => Op::Leq,
        taroc_hir::BinaryOperator::Geq => Op::Geq,
        taroc_hir::BinaryOperator::Neq => Op::Neq,
        taroc_hir::BinaryOperator::PtrEq => todo!(),
        _ => unreachable!(),
    }
}
