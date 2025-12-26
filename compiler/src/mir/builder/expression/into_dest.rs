use crate::{
    compile::context::Gcx,
    mir::{
        self, AggregateKind, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, Category,
        Constant, Operand, Place, PlaceElem, Rvalue, RvalueFunc, TerminatorKind,
        builder::MirBuilder,
    },
    span::Span,
    thir::{self, ExprId, ExprKind, FieldIndex},
    unpack,
};
use index_vec::IndexVec;
use rustc_hash::FxHashMap;

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub fn expr_into_dest(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        expr_id: ExprId,
    ) -> BlockAnd<()> {
        let expr = &self.thir.exprs[expr_id];
        let block_and = match &expr.kind {
            ExprKind::Local(..) => {
                let place = unpack!(block = self.as_place(block, expr_id));
                let rvalue = Rvalue::Use(Operand::Copy(place));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Reference {
                mutable,
                expr: ref_expr,
            } => {
                // Take the address of the place, preserving mutability.
                let place = unpack!(block = self.as_place(block, *ref_expr));
                let rvalue = Rvalue::Ref {
                    mutable: *mutable,
                    place,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Logical { op, lhs, rhs } => {
                // Short-circuiting logical ops.
                let lhs_op = unpack!(block = self.as_operand(block, *lhs));
                let then_block = self.new_block_with_note("logical-then".into());
                let else_block = self.new_block_with_note("logical-else".into());
                self.terminate(
                    block,
                    expr.span,
                    TerminatorKind::if_(lhs_op, then_block, else_block),
                );

                // For `&&`: false short-circuits; true continues to RHS.
                // For `||`: true short-circuits; false continues to RHS.
                let (short_block, cont_block, short_val) = match op {
                    mir::LogicalOperator::And => (else_block, then_block, false),
                    mir::LogicalOperator::Or => (then_block, else_block, true),
                };

                // Short-circuit path writes the known value.
                let short_const = Constant {
                    ty: expr.ty,
                    value: mir::ConstantKind::Bool(short_val),
                };
                self.push_assign(
                    short_block,
                    destination.clone(),
                    Rvalue::Use(Operand::Constant(short_const)),
                    expr.span,
                );

                // Continue with RHS evaluation.
                let rhs_block = self
                    .expr_into_dest(destination.clone(), cont_block, *rhs)
                    .into_block();

                // Join both paths.
                let join = self.new_block_with_note("logical-join".into());
                self.goto(rhs_block, join, expr.span);
                self.goto(short_block, join, expr.span);
                join.unit()
            }
            ExprKind::If {
                cond,
                then_expr,
                else_expr,
            } => {
                let destination_then = destination.clone();
                let (then_end, mut else_blk) = self.in_if_then_scope(expr.span, |this| {
                    let then_blk = this.then_else_break(block, *cond).into_block();
                    this.expr_into_dest(destination_then, then_blk, *then_expr)
                });

                if let Some(&expr) = else_expr.as_ref() {
                    else_blk = self
                        .expr_into_dest(destination, else_blk, expr)
                        .into_block();
                } else {
                    self.push_assign_unit(else_blk, expr.span, destination, self.gcx);
                }

                let join_block = self.new_block_with_note("Join Block".into());
                self.goto(then_end, join_block, expr.span);
                self.goto(else_blk, join_block, expr.span);
                join_block.unit()
            }
            ExprKind::Match { scrutinee, arms } => {
                self.lower_match_expr(destination, block, expr_id, *scrutinee, arms)
            }
            ExprKind::Assign { .. } | ExprKind::AssignOp { .. } => {
                block = self.lower_statement_expression(block, expr_id).into_block();
                self.push_assign_unit(block, expr.span, destination, self.gcx);
                block.unit()
            }
            ExprKind::Call { callee, args } => {
                let function = unpack!(block = self.as_local_operand(block, *callee));
                let args: Vec<Operand<'ctx>> = args
                    .iter()
                    .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                    .collect();
                let next = self.new_block();
                let terminator = TerminatorKind::Call {
                    func: function,
                    args,
                    destination,
                    target: next,
                };
                self.terminate(block, expr.span, terminator);
                next.unit()
            }
            ExprKind::Make { value } => {
                let value_ty = self.thir.exprs[*value].ty;
                let ptr_local = self.new_temp_with_ty(
                    self.gcx
                        .store
                        .interners
                        .intern_ty(crate::sema::models::TyKind::Pointer(
                            value_ty,
                            crate::hir::Mutability::Immutable,
                        )),
                    expr.span,
                );
                let alloc_rvalue = Rvalue::Alloc { ty: value_ty };
                self.push_assign(block, Place::from_local(ptr_local), alloc_rvalue, expr.span);

                // Store initializer into *ptr_local.
                let dest_place = Place {
                    local: ptr_local,
                    projection: vec![mir::PlaceElem::Deref],
                };
                block = self.expr_into_dest(dest_place, block, *value).into_block();

                // Return the pointer.
                let rvalue = Rvalue::Use(Operand::Copy(Place::from_local(ptr_local)));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Block(block_id) => self.lower_block(destination, block, *block_id),
            ExprKind::Adt(adt_expression) => {
                // Evaluate each field into an operand in declaration order.
                let field_count = match adt_expression.definition.kind {
                    crate::sema::models::AdtKind::Struct => {
                        let def = self.gcx.get_struct_definition(adt_expression.definition.id);
                        def.fields.len()
                    }
                    crate::sema::models::AdtKind::Enum => {
                        let Some(variant_index) = adt_expression.variant_index else {
                            unreachable!()
                        };
                        let variant = self
                            .gcx
                            .enum_variant_by_index(adt_expression.definition.id, variant_index);
                        match variant.kind {
                            crate::sema::models::EnumVariantKind::Unit => 0,
                            crate::sema::models::EnumVariantKind::Tuple(enum_variant_fields) => {
                                enum_variant_fields.len()
                            }
                        }
                    }
                };

                let mut tmp: Vec<Option<Operand<'ctx>>> = vec![None; field_count];
                for field in &adt_expression.fields {
                    let operand = unpack!(block = self.as_operand(block, field.expression));
                    tmp[field.index.index()] = Some(operand);
                }
                let fields: IndexVec<FieldIndex, Operand<'ctx>> = IndexVec::from_vec(
                    tmp.into_iter()
                        .map(|o| o.expect("missing struct field operand"))
                        .collect(),
                );

                let rvalue = Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: adt_expression.definition.id,
                        variant_index: adt_expression.variant_index,
                    },
                    fields,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Deref(..) | ExprKind::Field { .. } => {
                debug_assert!(matches!(Category::of(&expr.kind), Category::Place));
                let place = unpack!(block = self.as_place(block, expr_id));
                let rvalue = Rvalue::Use(Operand::Copy(place));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Tuple { .. }
            | ExprKind::Literal(..)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Cast { .. }
            | ExprKind::Zst { .. } => {
                debug_assert!(match Category::of(&expr.kind) {
                    // should be handled above
                    Category::Rvalue(RvalueFunc::Into) => false,

                    // must be handled above or else we get an
                    // infinite loop in the builder; see
                    // e.g., `ExprKind::VarRef` above
                    Category::Place => false,

                    _ => true,
                });

                let rvalue = unpack!(block = self.as_local_rvalue(block, expr_id));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
        };

        block_and
    }

    fn lower_match_expr(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        expr_id: ExprId,
        scrutinee: ExprId,
        arms: &[thir::ArmId],
    ) -> BlockAnd<()> {
        let expr = &self.thir.exprs[expr_id];
        let scrutinee_place = unpack!(block = self.as_place(block, scrutinee));

        let mut owned_tree = None;
        let tree = match self.thir.match_trees.get(&expr_id) {
            Some(tree) => tree,
            None => {
                let report = thir::match_tree::compile_match(self.gcx, self.thir, scrutinee, arms);
                owned_tree = Some(report.tree);
                owned_tree.as_ref().expect("match tree")
            }
        };
        // Keep owned_tree alive for the duration of this function
        let _keep_alive = &owned_tree;

        let mut var_places: FxHashMap<usize, Place<'ctx>> = FxHashMap::default();
        var_places.insert(tree.root_var.id, scrutinee_place.clone());

        let join_block = self.new_block_with_note("match-join".into());
        self.lower_match_decision(
            block,
            &tree.decision,
            &destination,
            join_block,
            &var_places,
            expr.span,
        );
        join_block.unit()
    }

    fn lower_match_decision(
        &mut self,
        mut block: BasicBlockId,
        decision: &thir::match_tree::Decision<'ctx>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
    ) {
        match decision {
            thir::match_tree::Decision::Success(body) => {
                let arm = &self.thir.arms[body.arm];
                let arm_block = self.new_block_with_note(format!("match-arm-{}", body.arm.index()));
                self.goto(block, arm_block, span);
                let arm_block = self
                    .bind_match_bindings(arm_block, body.arm, &body.bindings, var_places)
                    .into_block();
                let arm_block = self
                    .expr_into_dest(destination.clone(), arm_block, arm.body)
                    .into_block();
                self.goto(arm_block, join_block, arm.span);
            }
            thir::match_tree::Decision::Failure => {
                self.terminate(block, span, TerminatorKind::Unreachable);
            }
            thir::match_tree::Decision::Guard(guard_expr, body, fallback) => {
                let arm = &self.thir.arms[body.arm];
                let guard_block =
                    self.new_block_with_note(format!("match-guard-{}", body.arm.index()));
                self.goto(block, guard_block, span);
                block = self
                    .bind_match_bindings(guard_block, body.arm, &body.bindings, var_places)
                    .into_block();
                let guard_operand = unpack!(block = self.as_operand(block, *guard_expr));
                let then_block =
                    self.new_block_with_note(format!("match-arm-{}", body.arm.index()));
                let else_block = self.new_block_with_note("match-guard-fallback".into());
                self.terminate(
                    block,
                    arm.span,
                    TerminatorKind::if_(guard_operand, then_block, else_block),
                );
                let then_block = self
                    .expr_into_dest(destination.clone(), then_block, arm.body)
                    .into_block();
                self.goto(then_block, join_block, arm.span);
                self.lower_match_decision(
                    else_block,
                    fallback,
                    destination,
                    join_block,
                    var_places,
                    span,
                );
            }
            thir::match_tree::Decision::Switch(branch_var, cases, fallback) => {
                let Some(branch_place) = var_places.get(&branch_var.id) else {
                    self.terminate(block, span, TerminatorKind::Unreachable);
                    return;
                };

                let Some(first_case) = cases.first() else {
                    if let Some(fallback) = fallback {
                        self.lower_match_decision(
                            block,
                            fallback,
                            destination,
                            join_block,
                            var_places,
                            span,
                        );
                    } else {
                        self.terminate(block, span, TerminatorKind::Unreachable);
                    }
                    return;
                };

                match &first_case.constructor {
                    thir::match_tree::Constructor::Tuple(_) => {
                        if cases.len() != 1 {
                            self.terminate(block, span, TerminatorKind::Unreachable);
                            return;
                        }
                        let case = &cases[0];
                        let mut case_places = var_places.clone();
                        self.add_tuple_case_places(&mut case_places, branch_place, &case.arguments);
                        self.lower_match_decision(
                            block,
                            &case.body,
                            destination,
                            join_block,
                            &case_places,
                            span,
                        );
                    }
                    thir::match_tree::Constructor::Literal(
                        thir::match_tree::LiteralKey::Float(_),
                    )
                    | thir::match_tree::Constructor::Literal(
                        thir::match_tree::LiteralKey::String(_),
                    ) => {
                        self.lower_match_literal_chain(
                            block,
                            branch_place,
                            branch_var.ty,
                            cases,
                            fallback.as_deref(),
                            destination,
                            join_block,
                            var_places,
                            span,
                        );
                    }
                    _ => {
                        let discr = match &first_case.constructor {
                            thir::match_tree::Constructor::Variant { .. } => {
                                unpack!(
                                    block =
                                        self.enum_discriminant_operand(block, branch_place, span)
                                )
                            }
                            _ => Operand::Copy(branch_place.clone()),
                        };

                        let mut targets = Vec::with_capacity(cases.len());
                        for case in cases {
                            let case_block = self.new_block_with_note("match-case".into());
                            let mut case_places = var_places.clone();

                            let value = match &case.constructor {
                                thir::match_tree::Constructor::Bool(b) => {
                                    if *b {
                                        1u128
                                    } else {
                                        0u128
                                    }
                                }
                                thir::match_tree::Constructor::Variant { name, index } => {
                                    let variant_index = thir::VariantIndex::from_usize(*index);
                                    self.add_variant_case_places(
                                        &mut case_places,
                                        branch_place,
                                        *name,
                                        variant_index,
                                        &case.arguments,
                                    );
                                    *index as u128
                                }
                                thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::Integer(i),
                                ) => *i as u128,
                                thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::Rune(r),
                                ) => *r as u32 as u128,
                                thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::Float(_),
                                )
                                | thir::match_tree::Constructor::Literal(
                                    thir::match_tree::LiteralKey::String(_),
                                )
                                | thir::match_tree::Constructor::Tuple(_) => {
                                    self.terminate(block, span, TerminatorKind::Unreachable);
                                    return;
                                }
                            };

                            self.lower_match_decision(
                                case_block,
                                &case.body,
                                destination,
                                join_block,
                                &case_places,
                                span,
                            );
                            targets.push((value, case_block));
                        }

                        let otherwise_block = if let Some(fallback) = fallback.as_deref() {
                            let fallback_block = self.new_block_with_note("match-fallback".into());
                            self.lower_match_decision(
                                fallback_block,
                                fallback,
                                destination,
                                join_block,
                                var_places,
                                span,
                            );
                            fallback_block
                        } else {
                            let unreachable = self.new_block_with_note("match-unreachable".into());
                            self.terminate(unreachable, span, TerminatorKind::Unreachable);
                            unreachable
                        };

                        self.terminate(
                            block,
                            span,
                            TerminatorKind::SwitchInt {
                                discr,
                                targets,
                                otherwise: otherwise_block,
                            },
                        );
                    }
                }
            }
        }
    }

    fn lower_match_literal_chain(
        &mut self,
        mut block: BasicBlockId,
        branch_place: &Place<'ctx>,
        branch_ty: crate::sema::models::Ty<'ctx>,
        cases: &[thir::match_tree::Case<'ctx>],
        fallback: Option<&thir::match_tree::Decision<'ctx>>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
    ) {
        if cases.is_empty() {
            if let Some(fallback) = fallback {
                self.lower_match_decision(
                    block,
                    fallback,
                    destination,
                    join_block,
                    var_places,
                    span,
                );
            } else {
                self.terminate(block, span, TerminatorKind::Unreachable);
            }
            return;
        }

        let fallback_block = fallback.map(|decision| {
            let fb = self.new_block_with_note("match-fallback".into());
            self.lower_match_decision(
                fb,
                decision,
                destination,
                join_block,
                var_places,
                span,
            );
            fb
        });

        for (idx, case) in cases.iter().enumerate() {
            let is_last = idx + 1 == cases.len();
            let next_block = if is_last {
                fallback_block.unwrap_or_else(|| {
                    let bb = self.new_block_with_note("match-unreachable".into());
                    self.terminate(bb, span, TerminatorKind::Unreachable);
                    bb
                })
            } else {
                self.new_block_with_note("match-next".into())
            };

            let case_block = self.new_block_with_note("match-case".into());
            let cond = unpack!(
                block = self.build_literal_eq_operand(
                    block,
                    branch_place,
                    branch_ty,
                    &case.constructor,
                    span
                )
            );

            self.terminate(
                block,
                span,
                TerminatorKind::if_(cond, case_block, next_block),
            );

            self.lower_match_decision(
                case_block,
                &case.body,
                destination,
                join_block,
                var_places,
                span,
            );

            block = next_block;
        }
    }

    fn build_literal_eq_operand(
        &mut self,
        block: BasicBlockId,
        branch_place: &Place<'ctx>,
        branch_ty: crate::sema::models::Ty<'ctx>,
        constructor: &thir::match_tree::Constructor,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        let literal = match constructor {
            thir::match_tree::Constructor::Literal(key) => key,
            _ => {
                return block.and(Operand::Constant(Constant {
                    ty: self.gcx.types.bool,
                    value: mir::ConstantKind::Bool(false),
                }));
            }
        };

        let value = match literal {
            thir::match_tree::LiteralKey::Integer(i) => mir::ConstantKind::Integer(*i),
            thir::match_tree::LiteralKey::Float(bits) => {
                mir::ConstantKind::Float(f64::from_bits(*bits))
            }
            thir::match_tree::LiteralKey::Rune(r) => mir::ConstantKind::Rune(*r),
            thir::match_tree::LiteralKey::String(_) => {
                panic!("string literal match lowering is not implemented yet");
            }
        };

        let constant = Constant {
            ty: branch_ty,
            value,
        };
        let temp = self.new_temp_with_ty(self.gcx.types.bool, span);
        let rvalue = Rvalue::BinaryOp {
            op: BinaryOperator::Eql,
            lhs: Operand::Copy(branch_place.clone()),
            rhs: Operand::Constant(constant),
        };
        self.push_assign(block, Place::from_local(temp), rvalue, span);
        block.and(Operand::Move(Place::from_local(temp)))
    }

    fn enum_discriminant_operand(
        &mut self,
        block: BasicBlockId,
        place: &Place<'ctx>,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        let temp = self.new_temp_with_ty(self.gcx.types.uint, span);
        self.push_assign(
            block,
            Place::from_local(temp),
            Rvalue::Discriminant {
                place: place.clone(),
            },
            span,
        );
        block.and(Operand::Copy(Place::from_local(temp)))
    }

    fn add_tuple_case_places(
        &self,
        places: &mut FxHashMap<usize, Place<'ctx>>,
        base_place: &Place<'ctx>,
        args: &[thir::match_tree::Variable<'ctx>],
    ) {
        for (idx, var) in args.iter().enumerate() {
            let mut proj = base_place.projection.clone();
            proj.push(PlaceElem::Field(FieldIndex::from_usize(idx), var.ty));
            places.insert(
                var.id,
                Place {
                    local: base_place.local,
                    projection: proj,
                },
            );
        }
    }

    fn add_variant_case_places(
        &self,
        places: &mut FxHashMap<usize, Place<'ctx>>,
        base_place: &Place<'ctx>,
        name: crate::span::Symbol,
        index: thir::VariantIndex,
        args: &[thir::match_tree::Variable<'ctx>],
    ) {
        for (idx, var) in args.iter().enumerate() {
            let mut proj = base_place.projection.clone();
            proj.push(PlaceElem::VariantDowncast { name, index });
            proj.push(PlaceElem::Field(FieldIndex::from_usize(idx), var.ty));
            places.insert(
                var.id,
                Place {
                    local: base_place.local,
                    projection: proj,
                },
            );
        }
    }

    /// Binds match pattern variables using the precomputed var_places mapping.
    /// This correctly handles or-patterns by using the exact places computed
    /// during match tree traversal.
    ///
    /// For or-patterns, multiple alternatives may bind the same name. We ensure
    /// all alternatives share the same MIR local by tracking (arm_id, name) -> local.
    fn bind_match_bindings(
        &mut self,
        block: BasicBlockId,
        arm_id: thir::ArmId,
        bindings: &[thir::match_tree::Binding<'ctx>],
        var_places: &FxHashMap<usize, Place<'ctx>>,
    ) -> BlockAnd<()> {
        for binding in bindings {
            // Look up the place for this binding's variable
            let Some(src_place) = var_places.get(&binding.variable.id) else {
                // Variable not found in var_places - this shouldn't happen
                // but we'll skip it rather than crash
                continue;
            };

            // Get or create the MIR local for this binding.
            // For or-patterns, all alternatives with the same binding name share
            // the same local so the body can reference it consistently.
            let key = (arm_id, binding.name);
            let local = if let Some(&existing) = self.arm_binding_locals.get(&key) {
                existing
            } else {
                let new_local = self.push_local(
                    binding.ty,
                    mir::LocalKind::User,
                    Some(binding.name),
                    binding.span,
                );
                self.arm_binding_locals.insert(key, new_local);
                new_local
            };

            // Map the pattern's NodeID to the MIR local.
            // This ensures the body can find the local regardless of which
            // alternative's NodeID it references.
            self.locals.insert(binding.local, local);

            // Copy from the source place to the local
            let rvalue = Rvalue::Use(Operand::Copy(src_place.clone()));
            self.push_assign(block, Place::from_local(local), rvalue, binding.span);
        }
        block.unit()
    }
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    fn then_else_break(&mut self, mut block: BasicBlockId, condition: ExprId) -> BlockAnd<()> {
        let place = unpack!(block = self.as_temp(block, condition));
        let operand = Operand::Move(Place::from_local(place));

        let then_block = self.new_block_with_note("then block".into());
        let else_block = self.new_block_with_note("else block".into());

        let expr = &self.thir.exprs[condition];
        self.terminate(
            block,
            expr.span,
            TerminatorKind::if_(operand, then_block, else_block),
        );
        self.break_for_else(else_block, expr.span);
        then_block.unit()
    }

    pub fn push_assign_unit(
        &mut self,
        block: BasicBlockId,
        span: Span,
        place: Place<'ctx>,
        gcx: Gcx<'ctx>,
    ) {
        self.push_assign(
            block,
            place,
            Rvalue::Use(Operand::Constant(Constant {
                ty: gcx.types.void,
                value: mir::ConstantKind::Unit,
            })),
            span,
        );
    }
}
