use crate::{
    compile::{context::GlobalContext, entry::validate_entry_point},
    error::CompileResult,
    hir::{self, DefinitionID, DefinitionKind, HirVisitor, Mutability, Resolution},
    mir::{self, LogicalOperator},
    sema::{
        models::{AdtKind, Ty, TyKind},
        resolve::models::VariantCtorKind,
        tycheck::results::TypeCheckResults,
        tycheck::solve::Adjustment,
    },
    thir::{
        self, Block, BlockId, Constant, ConstantKind, Expr, ExprId, ExprKind, FieldIndex, Param,
        Stmt, StmtId, StmtKind, ThirFunction, ThirPackage, VariantIndex,
        pattern::pattern_from_hir,
    },
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

pub fn build_package<'ctx>(
    package: &hir::Package,
    gcx: GlobalContext<'ctx>,
    results: TypeCheckResults<'ctx>,
) -> CompileResult<ThirPackage<'ctx>> {
    let entry = validate_entry_point(&package, gcx)?;
    let package = Actor::run(package, gcx, results, entry)?;
    thir::passes::exhaustiveness::run(&package, gcx)?;
    Ok(package)
}

struct Actor<'ctx> {
    gcx: GlobalContext<'ctx>,
    results: std::rc::Rc<TypeCheckResults<'ctx>>,
    functions: FxHashMap<DefinitionID, ThirFunction<'ctx>>,
    entry: Option<DefinitionID>,
}

impl<'ctx> Actor<'ctx> {
    fn new(
        gcx: GlobalContext<'ctx>,
        results: TypeCheckResults<'ctx>,
        entry: Option<DefinitionID>,
    ) -> Self {
        Actor {
            gcx,
            results: std::rc::Rc::new(results),
            functions: FxHashMap::default(),
            entry,
        }
    }

    fn run(
        package: &hir::Package,
        gcx: GlobalContext<'ctx>,
        results: TypeCheckResults<'ctx>,
        entry: Option<DefinitionID>,
    ) -> CompileResult<ThirPackage<'ctx>> {
        let mut actor = Actor::new(gcx, results, entry);
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
        let func = FunctionLower::lower(self.gcx, self.results.clone(), id, node);
        self.functions.insert(id, func);
        hir::walk_function(self, id, node, fn_ctx);
    }
}

struct FunctionLower<'ctx> {
    gcx: GlobalContext<'ctx>,
    results: std::rc::Rc<TypeCheckResults<'ctx>>,
    func: ThirFunction<'ctx>,
}

impl<'ctx> FunctionLower<'ctx> {
    fn lower(
        gcx: GlobalContext<'ctx>,
        results: std::rc::Rc<TypeCheckResults<'ctx>>,
        id: DefinitionID,
        node: &hir::Function,
    ) -> ThirFunction<'ctx> {
        let mut lower = FunctionLower {
            gcx,
            results,
            func: ThirFunction {
                id,
                body: None,
                span: node.signature.span,
                params: vec![],
                stmts: IndexVec::new(),
                blocks: IndexVec::new(),
                exprs: IndexVec::new(),
                arms: IndexVec::new(),
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
            let block_id = self.lower_block(block);
            self.func.body = Some(block_id);
        }
    }

    fn lower_block(&mut self, block: &hir::Block) -> BlockId {
        let id = BlockId::from_raw(self.func.blocks.len() as u32);
        self.func.blocks.push(Block {
            id,
            stmts: vec![],
            expr: None,
        });

        let stmts: Vec<_> = block
            .statements
            .iter()
            .filter_map(|stmt| self.lower_statement(stmt).map(|s| self.push_stmt(s)))
            .collect();
        let expr = block.tail.as_deref().map(|expr| self.lower_expr(expr));

        self.func.blocks[id].stmts = stmts;
        self.func.blocks[id].expr = expr;
        id
    }

    fn lower_statement(&mut self, stmt: &hir::Statement) -> Option<Stmt<'ctx>> {
        match &stmt.kind {
            hir::StatementKind::Declaration(_) => None,
            hir::StatementKind::Expression(expr) => {
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
                let block_id = self.lower_block(block);
                Some(Stmt {
                    kind: StmtKind::Loop { block: block_id },
                    span: stmt.span,
                })
            }
            hir::StatementKind::Defer(block) => {
                let block_id = self.lower_block(block);
                Some(Stmt {
                    kind: StmtKind::Defer(block_id),
                    span: stmt.span,
                })
            }
            hir::StatementKind::Guard { .. } => None,
        }
    }

    fn lower_local(&mut self, local: &hir::Local) -> Stmt<'ctx> {
        let ty = self.results.node_type(local.id);
        let expr = local
            .initializer
            .as_deref()
            .map(|expr| self.lower_expr(expr));

        Stmt {
            kind: StmtKind::Let {
                id: local.id,
                pattern: pattern_from_hir(self.gcx, self.results.as_ref(), &local.pattern),
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
        if let Some(adjustments) = self
            .results
            .node_adjustments(expr.id)
            .map(|adj| adj.to_vec())
        {
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
                let inner = match ty.kind() {
                    TyKind::Reference(inner, _) | TyKind::Pointer(inner, _) => inner,
                    // Logic error if we try to deref non-derefable type.
                    _ => return expr,
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
        let ty = self.results.node_type(expr.id);
        let span = expr.span;
        let kind = match &expr.kind {
            hir::ExpressionKind::Literal(lit) => {
                let value = self.lower_literal(lit);
                ExprKind::Literal(Constant { ty, value })
            }
            hir::ExpressionKind::Path(path) => {
                let res = if let Some(def_id) = self.results.overload_source(expr.id) {
                    Resolution::Definition(def_id, self.gcx.definition_kind(def_id))
                } else if let Some(resolution) = self.results.value_resolution(expr.id) {
                    resolution
                } else {
                    match path {
                        hir::ResolvedPath::Resolved(path) => path.resolution.clone(),
                        hir::ResolvedPath::Relative(..) => {
                            self.gcx.dcx().emit_error(
                                "unresolved relative path (typecheck should have resolved this)"
                                    .into(),
                                Some(expr.span),
                            );
                            Resolution::Error
                        }
                    }
                };
                self.lower_path_expression(expr, res)
            }
            hir::ExpressionKind::Call { callee, arguments } => {
                // Builtin make: lower to ExprKind::Make.
                if let hir::ExpressionKind::Path(hir::ResolvedPath::Resolved(path)) = &callee.kind
                    && matches!(
                        path.resolution,
                        hir::Resolution::Foundation(hir::FoundationDecl::Make)
                    )
                {
                    if arguments.len() != 1 {
                        self.gcx.dcx().emit_error(
                            "`make` expects exactly one argument".into(),
                            Some(expr.span),
                        );
                        return Expr {
                            kind: ExprKind::Literal(Constant {
                                ty: self.gcx.types.error,
                                value: ConstantKind::Unit,
                            }),
                            ty: self.gcx.types.error,
                            span: expr.span,
                        };
                    }
                    let value = self.lower_expr(&arguments[0].expression);
                    return Expr {
                        kind: ExprKind::Make { value },
                        ty,
                        span,
                    };
                }
                if let Some(ctor_id) = self.variant_ctor_callee(callee) {
                    let (definition, variant_index) = self.enum_variant_from_ctor(ctor_id);
                    let fields = arguments
                        .iter()
                        .enumerate()
                        .map(|(index, arg)| thir::FieldExpression {
                            index: FieldIndex::from_usize(index),
                            expression: self.lower_expr(&arg.expression),
                        })
                        .collect();
                    return Expr {
                        kind: ExprKind::Adt(thir::AdtExpression {
                            definition,
                            variant_index: Some(variant_index),
                            fields,
                        }),
                        ty,
                        span,
                    };
                }
                let callee = self.lower_expr(callee);
                let args: Vec<ExprId> = arguments
                    .iter()
                    .map(|arg| self.lower_expr(&arg.expression))
                    .collect();
                ExprKind::Call { callee, args }
            }
            hir::ExpressionKind::Binary(op, lhs, rhs) => match op {
                hir::BinaryOperator::BoolAnd => ExprKind::Logical {
                    op: LogicalOperator::And,
                    lhs: self.lower_expr(lhs),
                    rhs: self.lower_expr(rhs),
                },
                hir::BinaryOperator::BoolOr => ExprKind::Logical {
                    op: LogicalOperator::Or,
                    lhs: self.lower_expr(lhs),
                    rhs: self.lower_expr(rhs),
                },
                hir::BinaryOperator::PtrEq => todo!(),
                _ => {
                    let lhs = self.lower_expr(lhs);
                    let rhs = self.lower_expr(rhs);
                    let op = bin_op(*op);
                    ExprKind::Binary { op, lhs, rhs }
                }
            },
            hir::ExpressionKind::Unary(hir::UnaryOperator::LogicalNot, operand) => {
                let operand = self.lower_expr(operand);
                ExprKind::Unary {
                    op: mir::UnaryOperator::LogicalNot,
                    operand,
                }
            }
            hir::ExpressionKind::Unary(hir::UnaryOperator::Negate, operand) => {
                let operand = self.lower_expr(operand);
                ExprKind::Unary {
                    op: mir::UnaryOperator::Negate,
                    operand,
                }
            }
            hir::ExpressionKind::Unary(hir::UnaryOperator::BitwiseNot, operand) => {
                let operand = self.lower_expr(operand);
                ExprKind::Unary {
                    op: mir::UnaryOperator::BitwiseNot,
                    operand,
                }
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
            hir::ExpressionKind::Match(node) => {
                let scrutinee = self.lower_expr(&node.value);
                let arms = node
                    .arms
                    .iter()
                    .map(|arm| self.lower_match_arm(arm))
                    .collect();
                ExprKind::Match { scrutinee, arms }
            }
            hir::ExpressionKind::Block(block) => {
                let block_id = self.lower_block(block);
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
                let Some(def_id) = self.results.overload_source(expr.id) else {
                    self.gcx.dcx().emit_error(
                        "failed to lower method call (no resolved target)".into(),
                        Some(expr.span),
                    );
                    return Expr {
                        kind: ExprKind::Literal(Constant {
                            ty: self.gcx.types.error,
                            value: ConstantKind::Unit,
                        }),
                        ty: self.gcx.types.error,
                        span: expr.span,
                    };
                };

                let args: Vec<ExprId> = arguments
                    .iter()
                    .map(|arg| self.lower_expr(&arg.expression))
                    .collect();
                let recv = self.lower_expr(receiver);
                let mut all_args = Vec::with_capacity(args.len() + 1);
                all_args.push(recv);
                all_args.extend(args);

                let callee_ty = self.gcx.get_type(def_id);
                let callee = self.push_expr(ExprKind::Zst { id: def_id }, callee_ty, expr.span);
                ExprKind::Call {
                    callee,
                    args: all_args,
                }
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
                    variant_index: None,
                    fields: literal
                        .fields
                        .iter()
                        .map(|f| thir::FieldExpression {
                            expression: self.lower_expr(&f.expression),
                            index: FieldIndex::from_usize(
                                self.results
                                    .field_index(f.expression.id)
                                    .expect("Field Index"),
                            ),
                        })
                        .collect(),
                };

                ExprKind::Adt(node)
            }
            hir::ExpressionKind::Member { target, .. } => {
                let lhs = self.lower_expr(target);
                ExprKind::Field {
                    lhs,
                    index: FieldIndex::from_usize(
                        self.results.field_index(expr.id).expect("Field Index"),
                    ),
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
                    index: FieldIndex::from_usize(
                        self.results.field_index(expr.id).expect("Field Index"),
                    ),
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

    fn lower_path_expression(
        &mut self,
        expr: &hir::Expression,
        resolution: Resolution,
    ) -> thir::ExprKind<'ctx> {
        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::Function | DefinitionKind::AssociatedFunction,
            ) => ExprKind::Zst { id },
            Resolution::Definition(
                id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Function),
            ) => ExprKind::Zst { id },
            Resolution::Definition(
                ctor_id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
            ) => {
                let (definition, variant_index) = self.enum_variant_from_ctor(ctor_id);
                ExprKind::Adt(thir::AdtExpression {
                    definition,
                    variant_index: Some(variant_index),
                    fields: Vec::new(),
                })
            }
            Resolution::LocalVariable(id) => ExprKind::Local(id),
            _ => unreachable!(),
        }
    }

    fn push_expr(&mut self, kind: ExprKind<'ctx>, ty: Ty<'ctx>, span: crate::span::Span) -> ExprId {
        let id = ExprId::from_raw(self.func.exprs.len() as u32);
        self.func.exprs.push(Expr { kind, ty, span });
        id
    }

    fn variant_ctor_callee(&self, callee: &hir::Expression) -> Option<DefinitionID> {
        let resolution = match &callee.kind {
            hir::ExpressionKind::Path(path) => match path {
                hir::ResolvedPath::Resolved(path) => Some(path.resolution.clone()),
                hir::ResolvedPath::Relative(..) => self.results.value_resolution(callee.id),
            },
            _ => None,
        }?;

        match resolution {
            Resolution::Definition(
                id,
                DefinitionKind::VariantConstructor(VariantCtorKind::Function),
            ) => Some(id),
            _ => None,
        }
    }

    fn enum_variant_from_ctor(
        &self,
        ctor_id: DefinitionID,
    ) -> (crate::sema::models::AdtDef, VariantIndex) {
        let Some(parent_id) = self.gcx.definition_parent(ctor_id) else {
            unreachable!()
        };

        let enum_id = match self.gcx.definition_kind(parent_id) {
            DefinitionKind::Enum => parent_id,
            DefinitionKind::Variant => match self.gcx.definition_parent(parent_id) {
                Some(enum_id) => enum_id,
                None => {
                    unreachable!()
                }
            },
            _ => {
                unreachable!()
            }
        };

        let def = self.gcx.get_enum_definition(enum_id);
        let Some((index, _)) = def
            .variants
            .iter()
            .enumerate()
            .find(|(_, v)| v.ctor_def_id == ctor_id)
        else {
            unreachable!()
        };

        (def.adt_def, VariantIndex::from_usize(index))
    }

    fn lower_match_arm(&mut self, arm: &hir::MatchArm) -> thir::ArmId {
        let guard = arm.guard.as_deref().map(|expr| self.lower_expr(expr));
        let body = self.lower_expr(&arm.body);
        let pattern = pattern_from_hir(self.gcx, self.results.as_ref(), &arm.pattern);
        let id = thir::ArmId::from_raw(self.func.arms.len() as u32);
        self.func.arms.push(thir::Arm {
            pattern: Box::new(pattern),
            guard,
            body,
            span: arm.span,
        });
        id
    }

    fn push_stmt(&mut self, stmt: Stmt<'ctx>) -> StmtId {
        let id = StmtId::from_raw(self.func.stmts.len() as u32);
        self.func.stmts.push(stmt);
        id
    }
}

fn bin_op(op: hir::BinaryOperator) -> mir::BinaryOperator {
    match op {
        hir::BinaryOperator::Add => mir::BinaryOperator::Add,
        hir::BinaryOperator::Sub => mir::BinaryOperator::Sub,
        hir::BinaryOperator::Mul => mir::BinaryOperator::Mul,
        hir::BinaryOperator::Div => mir::BinaryOperator::Div,
        hir::BinaryOperator::Rem => mir::BinaryOperator::Rem,
        hir::BinaryOperator::BitOr => mir::BinaryOperator::BitOr,
        hir::BinaryOperator::BitXor => mir::BinaryOperator::BitXor,
        hir::BinaryOperator::BitShl => mir::BinaryOperator::BitShl,
        hir::BinaryOperator::BitShr => mir::BinaryOperator::BitShr,
        hir::BinaryOperator::Eql => mir::BinaryOperator::Eql,
        hir::BinaryOperator::Lt => mir::BinaryOperator::Lt,
        hir::BinaryOperator::Gt => mir::BinaryOperator::Gt,
        hir::BinaryOperator::Leq => mir::BinaryOperator::Leq,
        hir::BinaryOperator::Geq => mir::BinaryOperator::Geq,
        hir::BinaryOperator::Neq => mir::BinaryOperator::Neq,
        _ => {
            unreachable!()
        }
    }
}
