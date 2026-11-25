use crate::{
    compile::context::Gcx,
    hir::StdItem,
    mir::{
        self, AggregateKind, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, CastKind,
        Category, Constant, LocalId, Operand, Place, PlaceElem, Rvalue, RvalueFunc, TerminatorKind,
        builder::{CleanupId, CleanupScopeId, MirBuilder},
        optimize::async_transform::{
            AsyncRuntimeFn, definition_in_std_module, find_or_register_async_runtime_function,
            find_std_function,
        },
    },
    sema::{
        models::{GenericArgument, GenericArguments, Ty, TyKind},
        resolve::models::DefinitionKind,
        tycheck::utils::instantiate::instantiate_signature_with_args,
    },
    span::Span,
    thir::{self, ExprId, ExprKind, FieldIndex},
    unpack,
    utils::intern::List,
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
        if let Some(operand) = self.prepared_argument_operand(block, expr_id) {
            self.push_assign(block, destination, Rvalue::Use(operand), expr.span);
            return block.unit();
        }
        let block_and = match &expr.kind {
            ExprKind::Local(..) => {
                let place = unpack!(block = self.as_place(block, expr_id));
                let operand = Operand::Copy(place);
                let rvalue = Rvalue::Use(operand);
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Reference { expr: ref_expr } => {
                if self.static_place(*ref_expr).is_some() {
                    return self.static_reference_into(destination, block, *ref_expr);
                }
                if self.is_class_field(*ref_expr) {
                    return self.class_field_into(destination, block, *ref_expr);
                }
                let place = unpack!(block = self.as_place(block, *ref_expr));
                let rvalue = Rvalue::Ref { place };
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
                let rhs_incoming = self.goto_if_fallthrough(rhs_block, join, expr.span);
                let short_incoming = self.goto_if_fallthrough(short_block, join, expr.span);
                if !rhs_incoming && !short_incoming {
                    self.terminate(join, expr.span, TerminatorKind::Unreachable);
                }
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
                let then_incoming = self.goto_if_fallthrough(then_end, join_block, expr.span);
                let else_incoming = self.goto_if_fallthrough(else_blk, join_block, expr.span);
                if !then_incoming && !else_incoming {
                    self.terminate(join_block, expr.span, TerminatorKind::Unreachable);
                }
                join_block.unit()
            }
            ExprKind::Match { scrutinee, .. } => {
                self.lower_match_expr(destination, block, expr_id, *scrutinee)
            }
            ExprKind::Return { value } => {
                let place = Place::from_local(self.body.return_local);
                if let Some(&value) = value.as_ref() {
                    block = self.expr_into_dest(place, block, value).into_block();
                } else if self.thir.constructor_self.is_none() {
                    self.push_assign_unit(block, expr.span, place, self.gcx);
                }
                self.record_return_edge(block, expr.span)
            }
            ExprKind::Loop { label, body } => {
                let loop_block = self.new_block_with_note("loop block".into());
                self.goto(block, loop_block, expr.span);
                let break_dest =
                    (!matches!(expr.ty.kind(), TyKind::Never)).then_some(destination);
                self.in_loop_scope(*label, loop_block, break_dest, expr.span, |this| {
                    let body_block = this.new_block_with_note("loop body block".into());
                    this.terminate(
                        loop_block,
                        expr.span,
                        TerminatorKind::Goto { target: body_block },
                    );
                    let unit = this.unit_temp_place(expr.span);
                    let end = this.lower_block(unit, body_block, *body).into_block();
                    this.goto(end, loop_block, expr.span);
                    None
                })
            }
            ExprKind::Break { label, value } => {
                self.record_break_edge(*label, *value, block, expr.span)
            }
            ExprKind::Continue { label } => self.record_continue_edge(*label, block, expr.span),
            ExprKind::Assign { .. } | ExprKind::AssignOp { .. } => {
                block = self.lower_statement_expression(block, expr_id).into_block();
                self.push_assign_unit(block, expr.span, destination, self.gcx);
                block.unit()
            }
            ExprKind::Call {
                callee,
                args,
                argument_evaluation_order,
                is_async,
            } => self.lower_ordered_call_into_dest(
                destination,
                block,
                *callee,
                args,
                argument_evaluation_order.as_deref(),
                *is_async,
                expr.span,
            ),
            ExprKind::ListLiteral {
                elements,
                element_ty,
            } => {
                block = self.lower_list_literal(
                    block,
                    destination,
                    elements,
                    expr.ty,
                    *element_ty,
                    expr.span,
                );
                block.unit()
            }
            ExprKind::BoxExistential { value, .. } => {
                let operand = unpack!(block = self.as_operand(block, *value));
                let rvalue = Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::BoxExistential,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::ExistentialUpcast { value, .. } => {
                let operand = unpack!(block = self.as_operand(block, *value));
                let rvalue = Rvalue::Cast {
                    operand,
                    ty: expr.ty,
                    kind: CastKind::ExistentialUpcast,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Block(block_id) => self.lower_block(destination, block, *block_id),
            ExprKind::Adt(adt_expression) => {
                // Snapshot explicit fields in source order, then evaluate the
                // update base once. Aggregate operands are arranged by slot.
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
                            crate::sema::models::EnumVariantKind::Tuple(enum_variant_fields)
                            | crate::sema::models::EnumVariantKind::Struct(enum_variant_fields) => {
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
                if let Some(base) = adt_expression.base {
                    // A place base needs no whole-struct temporary. An rvalue
                    // is materialized by as_place. No calls occur between the
                    // field reads and the aggregate assignment.
                    let base = unpack!(block = self.as_place(block, base));
                    let declared = self.gcx.get_struct_definition(adt_expression.definition.id);
                    for (index, operand) in tmp.iter_mut().enumerate() {
                        if operand.is_some() {
                            continue;
                        }
                        let ty = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                            self.gcx,
                            declared.fields[index].ty,
                            adt_expression.generic_args,
                        );
                        let mut field = base.clone();
                        field
                            .projection
                            .push(PlaceElem::Field(FieldIndex::from_usize(index), ty));
                        *operand = Some(Operand::Copy(field));
                    }
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
                        generic_args: adt_expression.generic_args,
                    },
                    fields,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Field { .. } if self.is_instant_class_field(expr_id) => {
                self.class_field_read_into(destination, block, expr_id)
            }
            ExprKind::Deref(..) | ExprKind::Field { .. } | ExprKind::Upvar { .. } => {
                debug_assert!(matches!(Category::of(&expr.kind), Category::Place));
                let place = unpack!(block = self.as_place(block, expr_id));
                let operand = Operand::Copy(place);
                let rvalue = Rvalue::Use(operand);
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Closure {
                def_id, captures, ..
            } => {
                // Build closure environment by evaluating each capture expression
                let capture_operands: Vec<Operand<'ctx>> = captures
                    .iter()
                    .map(|cap| {
                        // For now, captures are empty, so this won't execute
                        unpack!(block = self.as_operand(block, cap.capture_expr))
                    })
                    .collect();

                let fields: IndexVec<FieldIndex, Operand<'ctx>> =
                    IndexVec::from_vec(capture_operands);

                let captured_generics = match expr.ty.kind() {
                    TyKind::Closure {
                        closure_def_id,
                        captured_generics,
                        ..
                    } => {
                        debug_assert!(
                            closure_def_id == *def_id,
                            "closure expression def_id should match closure type def_id"
                        );
                        captured_generics
                    }
                    _ => GenericArguments::empty(),
                };

                let rvalue = Rvalue::Aggregate {
                    kind: AggregateKind::Closure {
                        def_id: *def_id,
                        captured_generics,
                    },
                    fields,
                };

                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Yield { value } => {
                let BlockAnd(block, operand) = self.as_operand(block, *value);
                let resume = self.new_block_with_note("generator-yield-resume".into());
                let (cancel, cancel_complete) = self.async_cancel_cleanup_target(expr.span);
                self.terminate(
                    block,
                    expr.span,
                    TerminatorKind::GeneratorYield {
                        value: operand,
                        resume,
                        cancel,
                        cancel_complete,
                    },
                );
                self.push_assign_unit(resume, expr.span, destination, self.gcx);
                resume.unit()
            }
            ExprKind::AwaitAsyncVar { local } => {
                self.lower_await_async_var(destination, block, *local, expr.span)
            }
            ExprKind::Select { arms } => {
                self.lower_select_expression(destination, block, arms, expr.span)
            }
            ExprKind::Await { future } => {
                if let ExprKind::Call {
                    callee,
                    args,
                    argument_evaluation_order,
                    is_async: true,
                    ..
                } = &self.thir.exprs[*future].kind
                {
                    if self.is_hidden_task_result_intrinsic(*callee) {
                        return self.with_call_arguments_in_order(
                            block,
                            args,
                            argument_evaluation_order.as_deref(),
                            |this, block| {
                                this.lower_awaited_task_result(destination, block, args, expr.span)
                            },
                        );
                    }
                    if self.is_hidden_task_group_next_intrinsic(*callee) {
                        return self.with_call_arguments_in_order(
                            block,
                            args,
                            argument_evaluation_order.as_deref(),
                            |this, block| {
                                this.lower_awaited_task_group_next(
                                    destination,
                                    block,
                                    args,
                                    expr.span,
                                )
                            },
                        );
                    }
                }
                let future_op = if matches!(
                    self.thir.exprs[*future].kind,
                    ExprKind::Call { is_async: true, .. }
                ) {
                    let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), expr.span);
                    block = self
                        .expr_into_dest(Place::from_local(handle_local), block, *future)
                        .into_block();
                    Operand::Copy(Place::from_local(handle_local))
                } else {
                    unpack!(block = self.as_operand(block, *future))
                };
                let resume = self.new_block_with_note("await-resume".into());
                let (cancel, cancel_complete) = self.async_cancel_cleanup_target(expr.span);
                let unwind = self.call_unwind_action(expr.span);
                self.terminate(
                    block,
                    expr.span,
                    TerminatorKind::Yield {
                        value: future_op,
                        resume,
                        resume_arg: destination.clone(),
                        no_result: None,
                        cancel,
                        cancel_complete,
                        unwind,
                    },
                );
                resume.unit()
            }
            ExprKind::Tuple { .. }
            | ExprKind::Array { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Literal(..)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::ClassIdentity { .. }
            | ExprKind::Cast { .. }
            | ExprKind::ClassUpcast { .. }
            | ExprKind::ClassSelfResult { .. }
            | ExprKind::ExistentialTryCast { .. }
            | ExprKind::ExistentialTypeIs { .. }
            | ExprKind::ClosureToFnPointer { .. }
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

                let rvalue = unpack!(block = self.as_rvalue(block, expr_id));
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
        };

        let end = block_and.into_block();
        // An async call constructs a future even when its eventual result is
        // Never. Only execution/await of that operation is non-returning.
        if matches!(expr.ty.kind(), TyKind::Never)
            && !matches!(expr.kind, ExprKind::Call { is_async: true, .. })
            && self.body.basic_blocks[end].terminator.is_none()
        {
            self.terminate(end, expr.span, TerminatorKind::Unreachable);
            return self
                .new_block_with_note("after never expression".into())
                .unit();
        }
        end.unit()
    }

    pub(super) fn lower_call_into_dest(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        is_async: bool,
        span: Span,
    ) -> BlockAnd<()> {
        let lower_public_task_api = !definition_in_std_module(self.gcx, self.thir.id, "task");
        if lower_public_task_api && self.is_std_task_free_function_named(callee, "spawn") {
            return self.lower_spawn_call(destination, block, args, span);
        }
        if lower_public_task_api && self.is_std_task_free_function_named(callee, "detached") {
            return self.lower_detached_spawn_call(destination, block, callee, args, span);
        }
        if lower_public_task_api && self.is_std_task_free_function_named(callee, "blocking") {
            return self.lower_blocking_call(destination, block, callee, args, span);
        }
        if lower_public_task_api && self.is_std_task_associated_function_named(callee, "spawn") {
            return self.lower_public_task_group_spawn_call(destination, block, callee, args, span);
        }
        if self.is_hidden_spawn_intrinsic(callee) {
            return self.lower_spawn_call(destination, block, args, span);
        }
        if self.is_hidden_wait_readable_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::WaitReadable,
            );
        }
        if self.is_hidden_wait_writable_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::WaitWritable,
            );
        }
        if self.is_hidden_channel_wait_send_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::ChannelWaitSend,
            );
        }
        if self.is_hidden_channel_wait_recv_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::ChannelWaitRecv,
            );
        }
        if self.is_hidden_mutex_lock_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::MutexLock,
            );
        }
        if self.is_hidden_rwlock_read_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::RwLockRead,
            );
        }
        if self.is_hidden_rwlock_write_intrinsic(callee) {
            return self.lower_io_wait_call(
                destination,
                block,
                args,
                span,
                AsyncRuntimeFn::RwLockWrite,
            );
        }
        if self.is_hidden_sleep_intrinsic(callee) {
            return self.lower_sleep_call(destination, block, args, span);
        }
        if self.is_hidden_intrinsic_named(callee, "__intrinsic_async_generator_next") {
            return self.lower_async_generator_next_call(destination, block, args, span);
        }
        if self.is_hidden_is_task_cancelled_intrinsic(callee) {
            return self.lower_is_task_cancelled_call(destination, block, args, span);
        }
        if self.is_hidden_dump_tasks_intrinsic(callee) {
            return self.lower_dump_tasks_call(destination, block, args, span);
        }
        if self.is_hidden_select_tasks_intrinsic(callee) {
            return self.lower_select_tasks_call(destination, block, args, span);
        }
        if self.is_hidden_task_timeout_intrinsic(callee) {
            return self.lower_task_timeout_call(destination, block, args, span);
        }
        if self.is_hidden_blocking_intrinsic(callee) {
            return self.lower_blocking_call(destination, block, callee, args, span);
        }
        if self.is_hidden_intrinsic_named(callee, "__intrinsic_keep_alive") {
            // No call survives: the statement is a liveness use, so the value
            // stays a reported root at every earlier safepoint even after
            // inlining removes the surrounding uses.
            let [argument] = args else {
                panic!("keep-alive intrinsic arity")
            };
            let operand = unpack!(block = self.as_operand(block, *argument));
            self.body.basic_blocks[block]
                .statements
                .push(mir::Statement {
                    kind: mir::StatementKind::KeepAlive(operand),
                    span,
                });
            self.push_assign_unit(block, span, destination.clone(), self.gcx);
            return block.unit();
        }
        if self.is_hidden_intrinsic_named(callee, "__intrinsic_class_owner") {
            let [argument] = args else {
                panic!("class owner intrinsic arity")
            };
            let operand = unpack!(block = self.as_operand(block, *argument));
            let reference_ty = self.thir.exprs[*argument].ty;
            let reference = self.new_temp_with_ty(reference_ty, span);

            self.push_assign(
                block,
                Place::from_local(reference),
                Rvalue::Use(operand),
                span,
            );
            let source = Place {
                local: reference,
                projection: vec![PlaceElem::Deref],
            };
            self.push_assign(
                block,
                destination.clone(),
                Rvalue::Cast {
                    operand: Operand::Copy(source),
                    ty: self.body.place_ty(self.gcx, &destination),
                    kind: CastKind::ClassObjectOwner,
                },
                span,
            );
            return block.unit();
        }
        if self.is_hidden_intrinsic_named(callee, "__intrinsic_class_from_owner")
            || self.is_hidden_intrinsic_named(callee, "__intrinsic_class_from_handle")
        {
            let [argument] = args else {
                panic!("class ownership intrinsic arity")
            };
            let operand = if self.is_hidden_intrinsic_named(callee, "__intrinsic_class_from_handle")
            {
                // Materialize the argument once, then transfer that temporary's
                // strong debt. A fresh allocation needs no extra retain/release.
                let handle = unpack!(block = self.as_temp(block, *argument));
                Operand::Copy(Place::from_local(handle))
            } else {
                unpack!(block = self.as_operand(block, *argument))
            };
            let kind = if self.is_hidden_intrinsic_named(callee, "__intrinsic_class_from_handle") {
                CastKind::NativeClassHandle
            } else {
                CastKind::ClassFromOwner
            };
            self.push_assign(
                block,
                destination.clone(),
                Rvalue::Cast {
                    operand,
                    ty: self.body.place_ty(self.gcx, &destination),
                    kind,
                },
                span,
            );
            return block.unit();
        }
        if self.is_hidden_cancel_task_intrinsic(callee) {
            return self.lower_cancel_task_call(destination, block, args, span);
        }
        if self.is_hidden_task_result_intrinsic(callee) {
            return self.lower_task_result_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_create_intrinsic(callee) {
            return self.lower_task_group_create_call(destination, block, callee, args, span);
        }
        if self.is_hidden_task_group_spawn_intrinsic(callee) {
            return self.lower_task_group_spawn_call(destination, block, callee, args, span);
        }
        if self.is_hidden_task_group_next_intrinsic(callee) {
            return self.lower_task_group_next_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_close_intrinsic(callee) {
            return self.lower_task_group_close_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_cancel_intrinsic(callee) {
            return self.lower_task_group_cancel_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_destroy_intrinsic(callee) {
            return self.lower_task_group_destroy_call(destination, block, args, span);
        }
        if self.is_hidden_task_group_destroy_and_rethrow_intrinsic(callee) {
            return self.lower_task_group_destroy_and_rethrow_call(destination, block, args, span);
        }
        if self.is_hidden_panic_payload_message_intrinsic(callee) {
            return self.lower_panic_payload_message_call(destination, block, args, span);
        }
        if self.is_hidden_panic_payload_rethrow_intrinsic(callee) {
            return self.lower_panic_payload_rethrow_call(destination, block, args, span);
        }

        let mut variadic_split_idx = None;
        let callee_expr = &self.thir.exprs[callee];
        let is_known_variadic = match callee_expr.kind {
            ExprKind::Zst { id, .. } => {
                matches!(
                    self.gcx.try_definition_kind(id),
                    Some(DefinitionKind::Function | DefinitionKind::AssociatedFunction)
                ) && self.gcx.get_signature(id).is_variadic
            }
            _ => false,
        };

        let callee_ty = callee_expr.ty;
        let callable_trait_target =
            if matches!(callee_ty.kind(), crate::sema::models::TyKind::Parameter(_)) {
                self.get_callable_trait_ref(callee_ty)
                    .and_then(|interface| {
                        let method_id = self.get_callable_trait_method_id(callee_ty)?;
                        let signature = instantiate_signature_with_args(
                            self.gcx,
                            self.gcx.get_signature(method_id),
                            interface.arguments,
                        );
                        let mut method_ty = Ty::from_labeled_signature(self.gcx, &signature);
                        if self.gcx.definition_is_async(method_id)
                            && let TyKind::FnPointer { inputs, .. } = method_ty.kind()
                        {
                            method_ty = self.gcx.store.interners.intern_ty(TyKind::FnPointer {
                                effects: Default::default(),
                                inputs,
                                output: self.gcx.async_handle_ty(),
                            });
                        }
                        Some((method_id, interface.arguments, method_ty))
                    })
            } else {
                None
            };
        let callable_self_place = if matches!(callee_ty.kind(), TyKind::Closure { .. })
            || callable_trait_target.is_some()
        {
            Some(unpack!(block = self.as_place(block, callee)))
        } else {
            None
        };

        let function = if let Some((method_id, generic_args, method_ty)) = callable_trait_target {
            Operand::Constant(Constant {
                ty: method_ty,
                value: mir::ConstantKind::Function(method_id, generic_args, method_ty),
            })
        } else if let Some(place) = callable_self_place.clone() {
            Operand::Copy(place)
        } else if is_async {
            unpack!(block = self.async_callable_operand(block, callee, callee_ty))
        } else {
            unpack!(block = self.as_operand(block, callee))
        };

        let closure_self_arg = callable_self_place.map(|place| {
            // Fn and AsyncFn receive a value, including their environment.
            // CopyValue also snapshots nested erased payloads while captured
            // references and class handles keep their ordinary shared identity.
            let environment = self.new_temp_with_ty(callee_ty, span);
            self.push_assign(
                block,
                Place::from_local(environment),
                Rvalue::Use(Operand::Copy(place)),
                span,
            );
            Operand::Copy(Place::from_local(environment))
        });
        if let crate::sema::models::TyKind::FnPointer { inputs, .. } = callee_ty.kind() {
            let param_count = inputs.len();
            if is_known_variadic && param_count > 0 {
                let list_idx = param_count - 1;
                if list_idx <= args.len() {
                    let needs_pack = if args.len() != param_count {
                        true
                    } else {
                        let last_param_ty = inputs[list_idx];
                        let last_arg_ty = self.thir.exprs[args[list_idx]].ty;
                        last_arg_ty != last_param_ty
                    };
                    if needs_pack {
                        variadic_split_idx = Some(list_idx);
                    }
                }
            } else if args.len() > param_count && param_count > 0 {
                variadic_split_idx = Some(param_count - 1);
            }
        }

        let fn_trait_args_ty = if let crate::sema::models::TyKind::Parameter(_) = callee_ty.kind() {
            self.get_fn_trait_args_type(callee_ty)
        } else {
            None
        };

        let (fixed_args, variadic_list_operand) = if let Some(split) = variadic_split_idx {
            let (fixed, var_args) = args.split_at(split);
            let inputs =
                if let crate::sema::models::TyKind::FnPointer { inputs, .. } = callee_ty.kind() {
                    inputs
                } else {
                    panic!("callee must be fn pointer");
                };
            let list_ty = inputs[inputs.len() - 1];
            let elem_ty = if let crate::sema::models::TyKind::Adt(_, args) = list_ty.kind() {
                if let Some(crate::sema::models::GenericArgument::Type(ty)) = args.get(0) {
                    *ty
                } else {
                    panic!("List must have generic arg");
                }
            } else {
                panic!("Variadic param must be List");
            };

            let fixed_operands: Vec<Operand<'ctx>> = fixed
                .iter()
                .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                .collect();
            let list_operand = unpack!(
                block = self.lower_variadic_sequence(block, var_args, list_ty, elem_ty, span)
            );
            (fixed_operands, Some(list_operand))
        } else {
            let all_args = args
                .iter()
                .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                .collect();
            (all_args, None)
        };

        let mut final_args = Vec::new();
        if let Some(self_arg) = closure_self_arg {
            final_args.push(self_arg);
        }
        if callable_trait_target.is_some() {
            let args_ty =
                fn_trait_args_ty.expect("callable type parameter must carry its argument type");
            let packed_args = if matches!(args_ty.kind(), TyKind::Tuple(_)) {
                let tuple_local = self.new_temp_with_ty(args_ty, span);
                self.register_storage_cleanup(tuple_local, span);

                self.push_assign(
                    block,
                    Place::from_local(tuple_local),
                    Rvalue::Aggregate {
                        kind: AggregateKind::Tuple,
                        fields: IndexVec::from_vec(fixed_args),
                    },
                    span,
                );
                // This is a fresh compiler-owned pack, not a user argument
                // binding. Its fields already performed their required copies
                // or moves. Transfer the pack, even if its tuple type is Copy,
                // so borrowed controllers are not duplicated and left behind.
                Operand::Copy(Place::from_local(tuple_local))
            } else {
                let [argument] = fixed_args.as_slice() else {
                    panic!("ICE: single-argument callable bound received the wrong arity")
                };
                argument.clone()
            };
            final_args.push(packed_args);
        } else {
            final_args.extend(fixed_args);
        }
        if let Some(list) = variadic_list_operand {
            final_args.push(list);
        }

        let next = self.new_block();
        let unwind = self.call_unwind_for_callee(&function, span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: function,
                args: final_args,
                destination,
                target: next,
                unwind,
            },
        );
        next.unit()
    }

    fn lower_spawn_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [thunk] = args else {
            panic!("ICE: spawn lowering expects exactly one thunk argument");
        };

        let task_ty = self.body.place_ty(self.gcx, &destination);
        let TyKind::Adt(def, task_args) = task_ty.kind() else {
            panic!("ICE: spawn destination must be Task[T]");
        };
        let Some(task_def_id) = self.gcx.std_item_def(StdItem::Task) else {
            panic!("ICE: Task std item missing");
        };
        assert_eq!(
            def.id, task_def_id,
            "ICE: spawn destination must be Task[T]"
        );
        let Some(GenericArgument::Type(task_output_ty)) = task_args.first().copied() else {
            panic!("ICE: Task[T] must carry its output type");
        };

        let (after_spawn, task_token_local) =
            self.lower_spawn_to_token(block, *thunk, task_output_ty, span);

        let fields = IndexVec::from_vec(vec![Operand::Copy(Place::from_local(task_token_local))]);
        self.push_assign(
            after_spawn,
            destination,
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: task_def_id,
                    variant_index: None,
                    generic_args: task_args,
                },
                fields,
            },
            span,
        );

        after_spawn.unit()
    }

    pub(in crate::mir::builder) fn lower_async_let(
        &mut self,
        block: BasicBlockId,
        pat_id: crate::hir::NodeID,
        name: crate::span::Symbol,
        value_ty: Ty<'ctx>,
        closure: ExprId,
        span: Span,
    ) -> BlockAnd<()> {
        let token_local = self.push_local(
            task_handle_ty(self.gcx),
            mir::LocalKind::User,
            true,
            Some(name),
            span,
        );
        self.push_storage_live(block, token_local, span);
        self.register_storage_cleanup(token_local, span);

        let awaited_local =
            self.push_local(self.gcx.types.bool, mir::LocalKind::Temp, true, None, span);
        self.push_storage_live(block, awaited_local, span);
        self.register_storage_cleanup(awaited_local, span);
        self.push_assign(
            block,
            Place::from_local(awaited_local),
            Rvalue::Use(Operand::Constant(Constant {
                ty: self.gcx.types.bool,
                value: mir::ConstantKind::Bool(false),
            })),
            span,
        );

        let (after_spawn, spawned_token) =
            self.lower_spawn_to_token(block, closure, value_ty, span);
        self.push_assign(
            after_spawn,
            Place::from_local(token_local),
            Rvalue::Use(Operand::Copy(Place::from_local(spawned_token))),
            span,
        );

        let scope_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskScopeToCurrent,
            span,
        );
        let scope_ty = self.gcx.get_type(scope_id);
        let after_scope = self.new_block();
        let unit = self.unit_temp_place(span);
        self.terminate(
            after_spawn,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: scope_ty,
                    value: mir::ConstantKind::Function(
                        scope_id,
                        GenericArguments::empty(),
                        scope_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: unit,
                target: after_scope,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let info = crate::mir::builder::ScopedTaskCleanup {
            token_local,
            awaited_local,
            value_ty,
        };
        self.async_var_locals.insert(pat_id, info);
        self.push_scoped_task_action(info, span);
        after_scope.unit()
    }

    fn lower_await_async_var(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        pat_id: crate::hir::NodeID,
        span: Span,
    ) -> BlockAnd<()> {
        let info = *self
            .async_var_locals
            .get(&pat_id)
            .expect("ICE: async var binding missing from MirBuilder");
        self.lower_await_scoped_task_value(destination, block, info, span)
    }

    fn lower_await_scoped_task_value(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        info: crate::mir::builder::ScopedTaskCleanup<'ctx>,
        span: Span,
    ) -> BlockAnd<()> {
        let ready_is_never = matches!(info.value_ty.kind(), TyKind::Never);

        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let from_spawned_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::FromSpawnedChecked,
            span,
        );
        let from_spawned_ty = self.gcx.get_type(from_spawned_id);
        let after_handle = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: from_spawned_ty,
                    value: mir::ConstantKind::Function(
                        from_spawned_id,
                        GenericArguments::empty(),
                        from_spawned_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(info.token_local))],
                destination: Place::from_local(handle_local),
                target: after_handle,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let resume_place = if ready_is_never {
            Place::from_local(self.new_temp_with_ty(self.gcx.types.uint8, span))
        } else {
            destination
        };

        let resume = self.new_block_with_note("async-var-resume".into());
        let no_result = self.new_block_with_note("async-var-no-result".into());
        let (cancel, cancel_complete) = self.async_cancel_cleanup_target(span);
        let unwind = self.call_unwind_action(span);
        self.terminate(
            after_handle,
            span,
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(handle_local)),
                resume,
                resume_arg: resume_place,
                no_result: Some(no_result),
                cancel,
                cancel_complete,
                unwind,
            },
        );

        let set_awaited = |this: &mut Self, bb: BasicBlockId| {
            this.push_assign(
                bb,
                Place::from_local(info.awaited_local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: this.gcx.types.bool,
                    value: mir::ConstantKind::Bool(true),
                })),
                span,
            );
        };

        set_awaited(self, resume);
        let join = self.new_block_with_note("async-var-join".into());
        if ready_is_never {
            self.terminate(resume, span, TerminatorKind::Unreachable);
        } else {
            self.goto(resume, join, span);
        }

        set_awaited(self, no_result);
        let status_local = self.new_temp_with_ty(self.gcx.types.uint8, span);
        let status_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskCompletionStatus,
            span,
        );
        let status_ty = self.gcx.get_type(status_id);
        let after_status = self.new_block();
        self.terminate(
            no_result,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: status_ty,
                    value: mir::ConstantKind::Function(
                        status_id,
                        GenericArguments::empty(),
                        status_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(info.token_local))],
                destination: Place::from_local(status_local),
                target: after_status,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let panicked = self.new_block_with_note("async-var-panicked".into());
        let cancelled = self.new_block_with_note("async-var-cancelled".into());
        self.terminate(
            after_status,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(status_local)),
                targets: vec![(3, panicked)],
                otherwise: cancelled,
            },
        );

        self.lower_rethrow_task_panic(panicked, info.token_local, span);

        let empty_str = Operand::Constant(Constant {
            ty: self.gcx.types.string,
            value: mir::ConstantKind::String(self.gcx.intern_symbol("")),
        });
        let rethrow_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::PanicPayloadRethrow,
            span,
        );
        let rethrow_ty = self.gcx.get_type(rethrow_id);
        let after_cancelled = self.new_block();
        let never_dest =
            Place::from_local(self.new_temp_with_ty(Ty::new(TyKind::Never, self.gcx), span));
        let cancel_unwind = self.call_unwind_action(span);
        self.terminate(
            cancelled,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: rethrow_ty,
                    value: mir::ConstantKind::Function(
                        rethrow_id,
                        GenericArguments::empty(),
                        rethrow_ty,
                    ),
                }),
                args: vec![empty_str],
                destination: never_dest,
                target: after_cancelled,
                unwind: cancel_unwind,
            },
        );
        self.terminate(after_cancelled, span, TerminatorKind::Unreachable);

        join.unit()
    }

    pub(in crate::mir::builder) fn lower_scoped_task_cleanup(
        &mut self,
        start: BasicBlockId,
        info: crate::mir::builder::ScopedTaskCleanup<'ctx>,
        drain: bool,
        next_block: BasicBlockId,
        span: Span,
    ) {
        let not_awaited = self.new_block_with_note("scoped-task-cancel".into());
        self.terminate(
            start,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(info.awaited_local)),
                targets: vec![(0, not_awaited)],
                otherwise: next_block,
            },
        );

        let cancel_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::CancelTask, span);
        let cancel_ty = self.gcx.get_type(cancel_id);
        let after_cancel = self.new_block();
        let unit = self.unit_temp_place(span);
        self.terminate(
            not_awaited,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: cancel_ty,
                    value: mir::ConstantKind::Function(
                        cancel_id,
                        GenericArguments::empty(),
                        cancel_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(info.token_local))],
                destination: unit,
                target: after_cancel,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        if !drain {
            self.goto(after_cancel, next_block, span);
            return;
        }

        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let from_spawned_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::FromSpawnedChecked,
            span,
        );
        let from_spawned_ty = self.gcx.get_type(from_spawned_id);
        let after_handle = self.new_block();
        self.terminate(
            after_cancel,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: from_spawned_ty,
                    value: mir::ConstantKind::Function(
                        from_spawned_id,
                        GenericArguments::empty(),
                        from_spawned_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(info.token_local))],
                destination: Place::from_local(handle_local),
                target: after_handle,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let resume_ty = if matches!(info.value_ty.kind(), TyKind::Never) {
            self.gcx.types.uint8
        } else {
            info.value_ty
        };
        let discard_local = self.new_temp_with_ty(resume_ty, span);
        let resume = self.new_block_with_note("scoped-task-drain-ok".into());
        let no_result = self.new_block_with_note("scoped-task-drain-no-result".into());
        let (cancel, cancel_complete) = self.async_cancel_cleanup_target(span);
        let unwind = self.call_unwind_action(span);
        self.terminate(
            after_handle,
            span,
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(handle_local)),
                resume,
                resume_arg: Place::from_local(discard_local),
                no_result: Some(no_result),
                cancel,
                cancel_complete,
                unwind,
            },
        );

        self.push_assign(
            resume,
            Place::from_local(info.awaited_local),
            Rvalue::Use(Operand::Constant(Constant {
                ty: self.gcx.types.bool,
                value: mir::ConstantKind::Bool(true),
            })),
            span,
        );
        self.goto(resume, next_block, span);

        self.push_assign(
            no_result,
            Place::from_local(info.awaited_local),
            Rvalue::Use(Operand::Constant(Constant {
                ty: self.gcx.types.bool,
                value: mir::ConstantKind::Bool(true),
            })),
            span,
        );
        let status_local = self.new_temp_with_ty(self.gcx.types.uint8, span);
        let status_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskCompletionStatus,
            span,
        );
        let status_ty = self.gcx.get_type(status_id);
        let after_status = self.new_block();
        self.terminate(
            no_result,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: status_ty,
                    value: mir::ConstantKind::Function(
                        status_id,
                        GenericArguments::empty(),
                        status_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(info.token_local))],
                destination: Place::from_local(status_local),
                target: after_status,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let panicked = self.new_block_with_note("scoped-task-drain-panicked".into());
        self.terminate(
            after_status,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(status_local)),
                targets: vec![(3, panicked)],
                otherwise: next_block,
            },
        );
        self.lower_rethrow_task_panic(panicked, info.token_local, span);
    }

    fn lower_rethrow_task_panic(
        &mut self,
        block: BasicBlockId,
        token_local: LocalId,
        span: Span,
    ) {
        let payload_local = self.new_temp_with_ty(self.gcx.types.string, span);
        let take_panic_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TakeTaskPanicPayload,
            span,
        );
        let take_panic_ty = self.gcx.get_type(take_panic_id);
        let after_take = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: take_panic_ty,
                    value: mir::ConstantKind::Function(
                        take_panic_id,
                        GenericArguments::empty(),
                        take_panic_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(payload_local),
                target: after_take,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let rethrow_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::PanicPayloadRethrow,
            span,
        );
        let rethrow_ty = self.gcx.get_type(rethrow_id);
        let after_rethrow = self.new_block();
        let never_dest =
            Place::from_local(self.new_temp_with_ty(Ty::new(TyKind::Never, self.gcx), span));
        let unwind = self.call_unwind_action(span);
        self.terminate(
            after_take,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: rethrow_ty,
                    value: mir::ConstantKind::Function(
                        rethrow_id,
                        GenericArguments::empty(),
                        rethrow_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(payload_local))],
                destination: never_dest,
                target: after_rethrow,
                unwind,
            },
        );
        self.terminate(after_rethrow, span, TerminatorKind::Unreachable);
    }

    fn lower_select_expression(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        arms: &[crate::thir::SelectArm<'ctx>],
        span: Span,
    ) -> BlockAnd<()> {
        assert!(!arms.is_empty(), "ICE: select requires at least one arm");

        let saved_cleanup = self.current_cleanup;
        let saved_scope = self.current_cleanup_scope;
        let select_scope = self.fresh_cleanup_scope();
        self.current_cleanup_scope = select_scope;

        let handle_ty = task_handle_ty(self.gcx);
        let mut arm_infos = Vec::with_capacity(arms.len());

        // 1. Spawn all arm operations once in source order and scope them to the current task.
        for arm in arms {
            let token_local = self.push_local(handle_ty, mir::LocalKind::Temp, true, None, arm.span);
            self.push_storage_live(block, token_local, arm.span);
            self.register_storage_cleanup(token_local, arm.span);

            let awaited_local =
                self.push_local(self.gcx.types.bool, mir::LocalKind::Temp, true, None, arm.span);
            self.push_storage_live(block, awaited_local, arm.span);
            self.register_storage_cleanup(awaited_local, arm.span);
            self.push_assign(
                block,
                Place::from_local(awaited_local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: self.gcx.types.bool,
                    value: mir::ConstantKind::Bool(false),
                })),
                arm.span,
            );

            let hold_id = find_or_register_async_runtime_function(
                self.gcx,
                AsyncRuntimeFn::HoldNextSpawn,
                arm.span,
            );
            let hold_ty = self.gcx.get_type(hold_id);
            let after_hold = self.new_block();
            let hold_unit = self.unit_temp_place(arm.span);
            self.terminate(
                block,
                arm.span,
                TerminatorKind::Call {
                    func: Operand::Constant(Constant {
                        ty: hold_ty,
                        value: mir::ConstantKind::Function(
                            hold_id,
                            GenericArguments::empty(),
                            hold_ty,
                        ),
                    }),
                    args: vec![],
                    destination: hold_unit,
                    target: after_hold,
                    unwind: mir::CallUnwindAction::Terminate,
                },
            );

            let (after_spawn, spawned_token) =
                self.lower_spawn_to_token(after_hold, arm.closure, arm.value_ty, arm.span);
            self.push_assign(
                after_spawn,
                Place::from_local(token_local),
                Rvalue::Use(Operand::Copy(Place::from_local(spawned_token))),
                arm.span,
            );

            let scope_id = find_or_register_async_runtime_function(
                self.gcx,
                AsyncRuntimeFn::TaskScopeToCurrent,
                arm.span,
            );
            let scope_ty = self.gcx.get_type(scope_id);
            let after_scope = self.new_block();
            let unit = self.unit_temp_place(arm.span);
            self.terminate(
                after_spawn,
                arm.span,
                TerminatorKind::Call {
                    func: Operand::Constant(Constant {
                        ty: scope_ty,
                        value: mir::ConstantKind::Function(
                            scope_id,
                            GenericArguments::empty(),
                            scope_ty,
                        ),
                    }),
                    args: vec![Operand::Copy(Place::from_local(token_local))],
                    destination: unit,
                    target: after_scope,
                    unwind: mir::CallUnwindAction::Terminate,
                },
            );

            let info = crate::mir::builder::ScopedTaskCleanup {
                token_local,
                awaited_local,
                value_ty: arm.value_ty,
            };
            self.push_scoped_task_action(info, arm.span);
            arm_infos.push(info);
            block = after_scope;
        }

        // 2. Pack all task handles into a fixed-size stack array and wait for the first completion.
        let arr_ty = self.variadic_pack_ty(handle_ty, arms.len());
        let arr_local = self.push_local(arr_ty, mir::LocalKind::Temp, true, None, span);
        self.push_storage_live(block, arr_local, span);
        self.register_storage_cleanup(arr_local, span);
        let arr_fields: IndexVec<crate::thir::FieldIndex, Operand<'ctx>> = arm_infos
            .iter()
            .map(|info| Operand::Copy(Place::from_local(info.token_local)))
            .collect();
        self.push_assign(
            block,
            Place::from_local(arr_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Array {
                    element: handle_ty,
                    len: arms.len(),
                },
                fields: arr_fields,
            },
            span,
        );

        let arr_ref_ty = Ty::new(TyKind::Reference(arr_ty), self.gcx);
        let arr_ref_local = self.new_temp_with_ty(arr_ref_ty, span);
        self.push_assign(
            block,
            Place::from_local(arr_ref_local),
            Rvalue::Ref {
                place: Place::from_local(arr_local),
            },
            span,
        );
        let const_u8_ptr = crate::mir::optimize::async_transform::raw_ptr_ty(
            self.gcx,
            self.gcx.types.uint8,
            crate::hir::Mutability::Immutable,
        );
        let arr_ptr_local = self.new_temp_with_ty(const_u8_ptr, span);
        self.push_assign(
            block,
            Place::from_local(arr_ptr_local),
            Rvalue::Cast {
                operand: Operand::Copy(Place::from_local(arr_ref_local)),
                ty: const_u8_ptr,
                kind: CastKind::Pointer,
            },
            span,
        );

        let select_handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let select_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::SelectManyTasks,
            span,
        );
        let select_ty = self.gcx.get_type(select_id);
        let after_select_create = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: select_ty,
                    value: mir::ConstantKind::Function(
                        select_id,
                        GenericArguments::empty(),
                        select_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(arr_ptr_local)),
                    Operand::Constant(Constant {
                        ty: self.gcx.types.uint,
                        value: mir::ConstantKind::Integer(arms.len() as u64),
                    }),
                ],
                destination: Place::from_local(select_handle_local),
                target: after_select_create,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let winner_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        let after_wait = self.new_block_with_note("select-winner".into());
        let (cancel, cancel_complete) = self.async_cancel_cleanup_target(span);
        let unwind = self.call_unwind_action(span);
        self.terminate(
            after_select_create,
            span,
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(select_handle_local)),
                resume: after_wait,
                resume_arg: Place::from_local(winner_local),
                no_result: None,
                cancel,
                cancel_complete,
                unwind,
            },
        );

        // 3. Dispatch on the winning arm index (source order breaks ties).
        let join_block = self.new_block_with_note("select-join".into());
        let invalid_arm = self.new_block_with_note("select-unreachable".into());
        self.terminate(invalid_arm, span, TerminatorKind::Unreachable);

        let mut switch_targets = Vec::with_capacity(arms.len());
        let mut arm_entry_blocks = Vec::with_capacity(arms.len());
        for i in 0..arms.len() {
            let entry = self.new_block_with_note(format!("select-arm-{i}"));
            switch_targets.push((i as u128, entry));
            arm_entry_blocks.push(entry);
        }
        self.terminate(
            after_wait,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(winner_local)),
                targets: switch_targets,
                otherwise: invalid_arm,
            },
        );

        let cancel_fn_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::CancelTask, span);
        let cancel_fn_ty = self.gcx.get_type(cancel_fn_id);

        let select_cleanup_head = self.current_cleanup;
        for (i, arm) in arms.iter().enumerate() {
            let mut arm_block = arm_entry_blocks[i];

            // 3a. Cancel every losing arm immediately before awaiting/draining.
            for (j, loser) in arm_infos.iter().enumerate() {
                if j == i {
                    continue;
                }
                let next = self.new_block();
                let unit = self.unit_temp_place(arm.span);
                self.terminate(
                    arm_block,
                    arm.span,
                    TerminatorKind::Call {
                        func: Operand::Constant(Constant {
                            ty: cancel_fn_ty,
                            value: mir::ConstantKind::Function(
                                cancel_fn_id,
                                GenericArguments::empty(),
                                cancel_fn_ty,
                            ),
                        }),
                        args: vec![Operand::Copy(Place::from_local(loser.token_local))],
                        destination: unit,
                        target: next,
                        unwind: mir::CallUnwindAction::Terminate,
                    },
                );
                arm_block = next;
            }

            // 3b. Retrieve the winning arm's result at its own type T_i.
            let win_is_never = matches!(arm.value_ty.kind(), TyKind::Never);
            let win_val_local = if win_is_never {
                None
            } else {
                let local = self.new_temp_with_ty(arm.value_ty, arm.span);
                Some(local)
            };
            let win_dest = match win_val_local {
                Some(local) => Place::from_local(local),
                None => Place::from_local(self.new_temp_with_ty(self.gcx.types.uint8, arm.span)),
            };
            arm_block = self
                .lower_await_scoped_task_value(win_dest, arm_block, arm_infos[i], arm.span)
                .into_block();

            // 3c. Drain every losing arm cleanly before running the winner body.
            for (j, loser) in arm_infos.iter().enumerate() {
                if j == i {
                    continue;
                }
                let after_drain = self.new_block_with_note(format!("select-drained-{i}-{j}"));
                self.lower_scoped_task_cleanup(arm_block, *loser, true, after_drain, arm.span);
                arm_block = after_drain;
            }

            // 3d. Bind winning result and execute winner body once in its own scope.
            let arm_scope = self.fresh_cleanup_scope();
            self.current_cleanup_scope = arm_scope;
            if let Some(win_local) = win_val_local {
                arm_block = self
                    .bind_pattern_to_place(
                        arm_block,
                        &arm.pattern,
                        Some(&Place::from_local(win_local)),
                        false,
                    )
                    .into_block();
            }
            arm_block = self
                .expr_into_dest(destination.clone(), arm_block, arm.body)
                .into_block();

            if self.body.basic_blocks[arm_block].terminator.is_none() {
                if self.current_cleanup != select_cleanup_head {
                    let mut cache = FxHashMap::default();
                    cache.insert(select_cleanup_head, join_block);
                    let cleanup_entry = self.ensure_cleanup_path(
                        self.current_cleanup,
                        select_cleanup_head,
                        join_block,
                        &mut cache,
                    );
                    self.goto(arm_block, cleanup_entry, arm.span);
                } else {
                    self.goto(arm_block, join_block, arm.span);
                }
            }
            self.current_cleanup = select_cleanup_head;
            self.current_cleanup_scope = select_scope;
        }

        // 4. Exit select_scope cleanly (all tasks already have awaited == true).
        let after_select = self.new_block_with_note("select-after".into());
        let mut cache = FxHashMap::default();
        cache.insert(saved_cleanup, after_select);
        let cleanup_entry =
            self.ensure_cleanup_path(select_cleanup_head, saved_cleanup, after_select, &mut cache);
        self.goto(join_block, cleanup_entry, span);

        self.current_cleanup = saved_cleanup;
        self.current_cleanup_scope = saved_scope;
        after_select.unit()
    }

    fn lower_detached_spawn_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [thunk] = args else {
            panic!("ICE: detached lowering expects exactly one thunk argument");
        };
        let task_output_ty = intrinsic_type_arg(self.thir, callee, 0);
        // Work runs independently of its handle, so fire-and-forget work is an
        // ordinary spawn whose handle is discarded.
        let (after_spawn, _) = self.lower_spawn_to_token(block, *thunk, task_output_ty, span);
        let _ = destination;
        after_spawn.unit()
    }

    fn lower_spawn_to_token(
        &mut self,
        mut block: BasicBlockId,
        thunk: ExprId,
        task_output_ty: crate::sema::models::Ty<'ctx>,
        span: Span,
    ) -> (BasicBlockId, LocalId) {
        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        block = self
            .lower_async_callable_into_dest(
                Place::from_local(handle_local),
                block,
                thunk,
                task_output_ty,
                span,
            )
            .into_block();

        let desc_local = unpack!(
            block = self.lower_task_output_descriptor_to_local(block, task_output_ty, span)
        );
        let task_token_local = self.new_temp_with_ty(task_handle_ty(self.gcx), span);

        let executor_spawn_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::Spawn, span);
        let executor_spawn_ty = self.gcx.get_type(executor_spawn_id);
        let spawn_metadata = self.spawn_metadata_operands(span);
        let after_spawn = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: executor_spawn_ty,
                    value: mir::ConstantKind::Function(
                        executor_spawn_id,
                        GenericArguments::empty(),
                        executor_spawn_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(handle_local)),
                    Operand::Copy(Place::from_local(desc_local)),
                    spawn_metadata[0].clone(),
                    spawn_metadata[1].clone(),
                    spawn_metadata[2].clone(),
                    spawn_metadata[3].clone(),
                ],
                destination: Place::from_local(task_token_local),
                target: after_spawn,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        (after_spawn, task_token_local)
    }

    /// Invoke the repeatable AsyncFn adapter. Its reference to the selected
    /// environment is retained by the child's GC-traced future, including when
    /// the caller's temporary closure value escapes into that future.
    fn lower_async_callable_into_dest(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        thunk: ExprId,
        output_ty: Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<()> {
        let thunk_ty = self.thir.exprs[thunk].ty;
        let interface_id = self
            .gcx
            .std_item_def(StdItem::AsyncFn)
            .expect("AsyncFn std item must be available for task lowering");
        let method_id = self
            .gcx
            .get_interface_requirements(interface_id)
            .and_then(|requirements| {
                requirements
                    .methods
                    .iter()
                    .find(|method| self.gcx.symbol_eq(method.name, "call"))
                    .map(|method| method.id)
            })
            .expect("AsyncFn.call requirement must be available for task lowering");

        let empty_inputs = self.gcx.store.interners.intern_ty_list(vec![]);
        let args_ty = self
            .gcx
            .store
            .interners
            .intern_ty(TyKind::Tuple(empty_inputs));
        let generic_args = self.gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(thunk_ty),
            GenericArgument::Type(args_ty),
            GenericArgument::Type(output_ty),
        ]);
        let callable_inputs = self
            .gcx
            .store
            .interners
            .intern_ty_list(vec![thunk_ty, args_ty]);
        let callable_ty = self.gcx.store.interners.intern_ty(TyKind::FnPointer {
            effects: Default::default(),
            inputs: callable_inputs,
            output: self.gcx.async_handle_ty(),
        });

        let thunk_place = unpack!(block = self.as_place(block, thunk));
        let thunk_operand = Operand::Copy(thunk_place);
        let unit_operand = Operand::Constant(Constant {
            ty: args_ty,
            value: mir::ConstantKind::Unit,
        });
        let next = self.new_block();
        let function = Operand::Constant(Constant {
            ty: callable_ty,
            value: mir::ConstantKind::Function(method_id, generic_args, callable_ty),
        });
        let unwind = self.call_unwind_for_callee(&function, span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: function,
                args: vec![thunk_operand, unit_operand],
                destination,
                target: next,
                unwind,
            },
        );
        next.unit()
    }

    fn spawn_metadata_operands(&self, span: Span) -> [Operand<'ctx>; 4] {
        let name = self.spawn_owner_name();
        let file = self
            .gcx
            .dcx()
            .file_path(span.file)
            .map(|path| path.to_string_lossy().into_owned())
            .unwrap_or_else(|| "<unknown>".into());
        [
            Operand::Constant(Constant {
                ty: self.gcx.types.string,
                value: mir::ConstantKind::String(name),
            }),
            Operand::Constant(Constant {
                ty: self.gcx.types.string,
                value: mir::ConstantKind::String(self.gcx.intern_symbol(&file)),
            }),
            Operand::Constant(Constant {
                ty: self.gcx.types.uint,
                value: mir::ConstantKind::Integer((span.start.line + 1) as u64),
            }),
            Operand::Constant(Constant {
                ty: self.gcx.types.uint,
                value: mir::ConstantKind::Integer((span.start.offset + 1) as u64),
            }),
        ]
    }

    fn spawn_owner_name(&self) -> crate::span::Symbol {
        let mut current = Some(self.thir.id);
        while let Some(id) = current {
            if let Some(ident) = self.gcx.try_definition_ident(id) {
                return ident.symbol;
            }
            current = self.gcx.definition_parent(id);
        }
        self.gcx.intern_symbol("<async closure>")
    }

    fn lower_sleep_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [duration] = args else {
            panic!("ICE: sleep lowering expects exactly one duration argument");
        };

        let destination_ty = self.body.place_ty(self.gcx, &destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: sleep intrinsic must lower into an async handle destination"
        );

        let duration_local = unpack!(block = self.as_temp(block, *duration));
        let duration_place = Place::from_local(duration_local);
        let sleep_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::Sleep, span);
        let sleep_ty = self.gcx.get_type(sleep_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: sleep_ty,
                    value: mir::ConstantKind::Function(
                        sleep_id,
                        GenericArguments::empty(),
                        sleep_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(duration_secs_place(self.gcx, duration_place.clone())),
                    Operand::Copy(duration_nanos_place(self.gcx, duration_place)),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_async_generator_next_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [frame_expr, poll_expr] = args else {
            panic!("ICE: __intrinsic_async_generator_next expects (frame, poll)");
        };

        let destination_ty = self.body.place_ty(self.gcx, &destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: __intrinsic_async_generator_next must lower into an async handle destination"
        );

        let frame_op = unpack!(block = self.as_operand(block, *frame_expr));
        let poll_op = unpack!(block = self.as_operand(block, *poll_expr));

        let const_u8_ptr = self.gcx.store.interners.intern_ty(TyKind::Pointer(
            self.gcx.types.uint8,
            crate::hir::Mutability::Immutable,
        ));
        let poll_ptr_local = self.new_temp_with_ty(const_u8_ptr, span);
        self.push_assign(
            block,
            Place::from_local(poll_ptr_local),
            Rvalue::Cast {
                operand: poll_op,
                ty: const_u8_ptr,
                kind: mir::CastKind::Pointer,
            },
            span,
        );
        let null_drop_local = self.new_temp_with_ty(const_u8_ptr, span);
        self.push_assign(
            block,
            Place::from_local(null_drop_local),
            Rvalue::Zeroed { ty: const_u8_ptr },
            span,
        );

        let create_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::Create, span);
        let create_ty = self.gcx.get_type(create_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: create_ty,
                    value: mir::ConstantKind::Function(
                        create_id,
                        GenericArguments::empty(),
                        create_ty,
                    ),
                }),
                args: vec![
                    frame_op,
                    Operand::Copy(Place::from_local(poll_ptr_local)),
                    Operand::Copy(Place::from_local(null_drop_local)),
                    Operand::Constant(Constant {
                        ty: self.gcx.types.uint8,
                        value: mir::ConstantKind::Integer(1),
                    }),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn lower_cancel_task_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [task] = args else {
            panic!("ICE: cancel task lowering expects exactly one task argument");
        };

        let token_local = unpack!(block = self.lower_task_token_local(block, *task, span));
        let cancel_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::CancelTask, span);
        let cancel_ty = self.gcx.get_type(cancel_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: cancel_ty,
                    value: mir::ConstantKind::Function(
                        cancel_id,
                        GenericArguments::empty(),
                        cancel_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_task_result_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [task] = args else {
            panic!("ICE: task result lowering expects exactly one task argument");
        };

        let destination_ty = self.body.place_ty(self.gcx, &destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: task result intrinsic must lower into an async handle destination"
        );

        let token_local = unpack!(block = self.lower_task_token_local(block, *task, span));
        let from_spawned_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::FromSpawnedChecked,
            span,
        );
        let from_spawned_ty = self.gcx.get_type(from_spawned_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: from_spawned_ty,
                    value: mir::ConstantKind::Function(
                        from_spawned_id,
                        GenericArguments::empty(),
                        from_spawned_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_awaited_task_result(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [task] = args else {
            panic!("ICE: awaited task result lowering expects exactly one task argument");
        };

        let destination_ty = self.body.place_ty(self.gcx, &destination);
        let TyKind::Adt(result_def, result_args) = destination_ty.kind() else {
            panic!("ICE: awaited task result destination must be Result[T, E]");
        };
        let ready_ty = result_args
            .first()
            .copied()
            .and_then(GenericArgument::ty)
            .unwrap_or_else(|| panic!("ICE: Result[T, E] is missing value type"));
        let ready_is_never = matches!(ready_ty.kind(), TyKind::Never);

        let token_local = unpack!(block = self.lower_task_token_local(block, *task, span));
        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let (ready_local, resume_local) = if ready_is_never {
            (None, self.new_temp_with_ty(self.gcx.types.uint8, span))
        } else {
            let ready_local = self.new_temp_with_ty(ready_ty, span);
            (Some(ready_local), ready_local)
        };

        let from_spawned_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::FromSpawnedChecked,
            span,
        );
        let from_spawned_ty = self.gcx.get_type(from_spawned_id);
        let after_handle = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: from_spawned_ty,
                    value: mir::ConstantKind::Function(
                        from_spawned_id,
                        GenericArguments::empty(),
                        from_spawned_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(handle_local),
                target: after_handle,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let resume = self.new_block_with_note("task-result-resume".into());
        let no_result = self.new_block_with_note("task-result-without-value".into());
        let (cancel, cancel_complete) = self.async_cancel_cleanup_target(span);
        let unwind = self.call_unwind_action(span);
        self.terminate(
            after_handle,
            span,
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(handle_local)),
                resume,
                resume_arg: Place::from_local(resume_local),
                no_result: Some(no_result),
                cancel,
                cancel_complete,
                unwind,
            },
        );

        let status_local = self.new_temp_with_ty(self.gcx.types.uint8, span);
        let status_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskCompletionStatus,
            span,
        );
        let status_ty = self.gcx.get_type(status_id);
        let after_status = self.new_block();
        self.terminate(
            no_result,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: status_ty,
                    value: mir::ConstantKind::Function(
                        status_id,
                        GenericArguments::empty(),
                        status_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(status_local),
                target: after_status,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        // Each observer receives its own immutable copy of a panic payload.
        let payload_data_local = self.new_temp_with_ty(self.gcx.types.string, span);
        let take_panic_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TakeTaskPanicPayload,
            span,
        );
        let take_panic_ty = self.gcx.get_type(take_panic_id);
        let after_take_panic = self.new_block();
        self.terminate(
            after_status,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: take_panic_ty,
                    value: mir::ConstantKind::Function(
                        take_panic_id,
                        GenericArguments::empty(),
                        take_panic_ty,
                    ),
                }),
                args: vec![Operand::Copy(Place::from_local(token_local))],
                destination: Place::from_local(payload_data_local),
                target: after_take_panic,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let ok_block = resume;
        let cancelled_block = self.new_block_with_note("task-result-cancelled".into());
        let panicked_block = self.new_block_with_note("task-result-panicked".into());
        let join_block = self.new_block_with_note("task-result-join".into());
        self.terminate(
            after_take_panic,
            span,
            TerminatorKind::SwitchInt {
                discr: Operand::Copy(Place::from_local(status_local)),
                targets: vec![(2, cancelled_block)],
                otherwise: panicked_block,
            },
        );

        // ok branch: Result.ok(ready_value)
        if let Some(ready_local) = ready_local {
            self.push_assign(
                ok_block,
                destination.clone(),
                Rvalue::Aggregate {
                    kind: AggregateKind::Adt {
                        def_id: result_def.id,
                        variant_index: Some(thir::VariantIndex::from_usize(0)),
                        generic_args: result_args,
                    },
                    fields: IndexVec::from_vec(vec![Operand::Copy(Place::from_local(ready_local))]),
                },
                span,
            );
            self.goto(ok_block, join_block, span);
        } else {
            // `Task[!]` cannot complete with an `ok` value.
            self.terminate(ok_block, span, TerminatorKind::Unreachable);
        }

        let err_ty = result_args
            .get(1)
            .copied()
            .and_then(GenericArgument::ty)
            .unwrap_or_else(|| panic!("ICE: Result[T, E] is missing error type"));
        let TyKind::Adt(err_def, err_args) = err_ty.kind() else {
            panic!("ICE: Task.result() error type must be an enum");
        };

        // cancelled branch: Result.err(TaskError.cancelled)  [variant 0, no fields]
        let cancelled_error_local = self.new_temp_with_ty(err_ty, span);
        self.push_assign(
            cancelled_block,
            Place::from_local(cancelled_error_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: err_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(0)),
                    generic_args: err_args,
                },
                fields: IndexVec::new(),
            },
            span,
        );
        self.push_assign(
            cancelled_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: result_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: result_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Copy(Place::from_local(
                    cancelled_error_local,
                ))]),
            },
            span,
        );
        self.goto(cancelled_block, join_block, span);

        // panicked branch: Result.err(TaskError.panicked(PanicPayload { data }))  [variant 1]
        let panic_payload_def_id = self
            .gcx
            .std_item_def(StdItem::PanicPayload)
            .unwrap_or_else(|| panic!("ICE: PanicPayload std item missing"));
        let panic_payload_ty = self.gcx.get_type(panic_payload_def_id);
        let TyKind::Adt(panic_payload_adt, panic_payload_args) = panic_payload_ty.kind() else {
            panic!("ICE: PanicPayload must be a struct");
        };
        let payload_local = self.new_temp_with_ty(panic_payload_ty, span);
        self.push_assign(
            panicked_block,
            Place::from_local(payload_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: panic_payload_adt.id,
                    variant_index: None,
                    generic_args: panic_payload_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Copy(Place::from_local(
                    payload_data_local,
                ))]),
            },
            span,
        );
        let panicked_error_local = self.new_temp_with_ty(err_ty, span);
        self.push_assign(
            panicked_block,
            Place::from_local(panicked_error_local),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: err_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: err_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Copy(Place::from_local(payload_local))]),
            },
            span,
        );
        self.push_assign(
            panicked_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: result_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: result_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Copy(Place::from_local(
                    panicked_error_local,
                ))]),
            },
            span,
        );
        self.goto(panicked_block, join_block, span);

        join_block.unit()
    }

    fn lower_task_group_create_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [cancel_on_panic] = args else {
            panic!("ICE: task group create lowering expects exactly one policy argument");
        };

        let result_ty = intrinsic_type_arg(self.thir, callee, 0);
        let policy_local =
            unpack!(block = self.lower_bool_to_u8_local(block, *cancel_on_panic, span));
        let size_local = unpack!(block = self.lower_size_of_type_to_local(block, result_ty, span));
        let create_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskGroupCreate,
            span,
        );
        let create_ty = self.gcx.get_type(create_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: create_ty,
                    value: mir::ConstantKind::Function(
                        create_id,
                        GenericArguments::empty(),
                        create_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(size_local)),
                    Operand::Copy(Place::from_local(policy_local)),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_task_group_spawn_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id, thunk] = args else {
            panic!("ICE: task group spawn lowering expects group id and thunk");
        };

        let result_ty = intrinsic_type_arg(self.thir, callee, 0);
        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        block = self
            .lower_async_callable_into_dest(
                Place::from_local(handle_local),
                block,
                *thunk,
                result_ty,
                span,
            )
            .into_block();

        let desc_local =
            unpack!(block = self.lower_task_output_descriptor_to_local(block, result_ty, span));
        let token_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        let spawn_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::TaskGroupSpawn, span);
        let spawn_ty = self.gcx.get_type(spawn_id);
        let spawn_metadata = self.spawn_metadata_operands(span);
        let after_spawn = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: spawn_ty,
                    value: mir::ConstantKind::Function(
                        spawn_id,
                        GenericArguments::empty(),
                        spawn_ty,
                    ),
                }),
                args: vec![
                    group_operand,
                    Operand::Copy(Place::from_local(handle_local)),
                    Operand::Copy(Place::from_local(desc_local)),
                    spawn_metadata[0].clone(),
                    spawn_metadata[1].clone(),
                    spawn_metadata[2].clone(),
                    spawn_metadata[3].clone(),
                ],
                destination: Place::from_local(token_local),
                target: after_spawn,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        self.push_assign_unit(after_spawn, span, destination, self.gcx);
        after_spawn.unit()
    }

    fn lower_public_task_group_spawn_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group, thunk] = args else {
            panic!("ICE: TaskGroup.spawn lowering expects a receiver and thunk");
        };

        let result_ty = intrinsic_type_arg(self.thir, callee, 0);
        let mut group_place = unpack!(block = self.as_place(block, *group));
        if matches!(
            self.thir.exprs[*group].ty.kind(),
            TyKind::Reference(..) | TyKind::Pointer(..)
        ) {
            group_place.projection.push(PlaceElem::Deref);
        }
        group_place.projection.push(PlaceElem::Field(
            FieldIndex::from_raw(0),
            self.gcx.types.uint,
        ));

        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        block = self
            .lower_async_callable_into_dest(
                Place::from_local(handle_local),
                block,
                *thunk,
                result_ty,
                span,
            )
            .into_block();

        let desc_local =
            unpack!(block = self.lower_task_output_descriptor_to_local(block, result_ty, span));
        let token_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        let spawn_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::TaskGroupSpawn, span);
        let spawn_ty = self.gcx.get_type(spawn_id);
        let spawn_metadata = self.spawn_metadata_operands(span);
        let after_spawn = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: spawn_ty,
                    value: mir::ConstantKind::Function(
                        spawn_id,
                        GenericArguments::empty(),
                        spawn_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(group_place),
                    Operand::Copy(Place::from_local(handle_local)),
                    Operand::Copy(Place::from_local(desc_local)),
                    spawn_metadata[0].clone(),
                    spawn_metadata[1].clone(),
                    spawn_metadata[2].clone(),
                    spawn_metadata[3].clone(),
                ],
                destination: Place::from_local(token_local),
                target: after_spawn,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        self.push_assign_unit(after_spawn, span, destination, self.gcx);
        after_spawn.unit()
    }

    fn lower_task_group_next_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: task group next lowering expects exactly one group id argument");
        };

        let destination_ty = self.body.place_ty(self.gcx, &destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: task group next intrinsic must lower into an async handle destination"
        );

        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let next_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::GroupNext, span);
        let next_ty = self.gcx.get_type(next_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: next_ty,
                    value: mir::ConstantKind::Function(next_id, GenericArguments::empty(), next_ty),
                }),
                args: vec![group_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_awaited_task_group_next(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: awaited task group next lowering expects exactly one group id argument");
        };

        let destination_ty = self.body.place_ty(self.gcx, &destination);
        let TyKind::Adt(optional_def, optional_args) = destination_ty.kind() else {
            panic!("ICE: awaited task group next destination must be Optional[T]");
        };
        let ready_ty = optional_args
            .first()
            .copied()
            .and_then(GenericArgument::ty)
            .unwrap_or_else(|| panic!("ICE: Optional[T] is missing payload type"));

        let group_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        self.push_assign(
            block,
            Place::from_local(group_local),
            Rvalue::Use(group_operand),
            span,
        );

        let handle_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let ready_local = self.new_temp_with_ty(ready_ty, span);
        let next_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::GroupNext, span);
        let next_ty = self.gcx.get_type(next_id);
        let after_handle = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: next_ty,
                    value: mir::ConstantKind::Function(next_id, GenericArguments::empty(), next_ty),
                }),
                args: vec![Operand::Copy(Place::from_local(group_local))],
                destination: Place::from_local(handle_local),
                target: after_handle,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        let resume = self.new_block_with_note("task-group-next-resume".into());
        let no_result = self.new_block_with_note("task-group-next-without-value".into());
        let (cancel, cancel_complete) = self.async_cancel_cleanup_target(span);
        let unwind = self.call_unwind_action(span);
        self.terminate(
            after_handle,
            span,
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(handle_local)),
                resume,
                resume_arg: Place::from_local(ready_local),
                no_result: Some(no_result),
                cancel,
                cancel_complete,
                unwind,
            },
        );

        let some_block = resume;
        let none_block = no_result;
        let join_block = self.new_block_with_note("task-group-next-join".into());

        self.push_assign(
            some_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: optional_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(0)),
                    generic_args: optional_args,
                },
                fields: IndexVec::from_vec(vec![Operand::Copy(Place::from_local(ready_local))]),
            },
            span,
        );
        self.goto(some_block, join_block, span);

        self.push_assign(
            none_block,
            destination.clone(),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: optional_def.id,
                    variant_index: Some(thir::VariantIndex::from_usize(1)),
                    generic_args: optional_args,
                },
                fields: IndexVec::new(),
            },
            span,
        );
        self.goto(none_block, join_block, span);

        join_block.unit()
    }

    fn lower_task_group_close_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        self.lower_task_group_void_call(
            destination,
            block,
            args,
            span,
            AsyncRuntimeFn::TaskGroupClose,
        )
    }

    fn lower_task_group_cancel_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        self.lower_task_group_void_call(
            destination,
            block,
            args,
            span,
            AsyncRuntimeFn::TaskGroupCancelAll,
        )
    }

    fn lower_task_group_destroy_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        self.lower_task_group_void_call(
            destination,
            block,
            args,
            span,
            AsyncRuntimeFn::TaskGroupDestroy,
        )
    }

    fn lower_task_group_destroy_and_rethrow_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: task group runtime call expects exactly one group id argument");
        };

        let mut block = block;
        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let call_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::TaskGroupDestroyAndRethrowPanic,
            span,
        );
        let call_ty = self.gcx.get_type(call_id);
        let next = self.new_block();
        let unwind = self.call_unwind_action(span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: call_ty,
                    value: mir::ConstantKind::Function(call_id, GenericArguments::empty(), call_ty),
                }),
                args: vec![group_operand],
                destination,
                target: next,
                // This runtime helper re-panics when a child panic was recorded,
                // so it must unwind through active cleanup/defer scopes.
                unwind,
            },
        );

        next.unit()
    }

    fn lower_task_group_void_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
        which: AsyncRuntimeFn,
    ) -> BlockAnd<()> {
        let [group_id] = args else {
            panic!("ICE: task group runtime call expects exactly one group id argument");
        };

        let group_operand = unpack!(block = self.as_operand(block, *group_id));
        let call_id = find_or_register_async_runtime_function(self.gcx, which, span);
        let call_ty = self.gcx.get_type(call_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: call_ty,
                    value: mir::ConstantKind::Function(call_id, GenericArguments::empty(), call_ty),
                }),
                args: vec![group_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn lower_task_token_local(
        &mut self,
        mut block: BasicBlockId,
        task: ExprId,
        span: Span,
    ) -> BlockAnd<LocalId> {
        let mut task_place = unpack!(block = self.as_place(block, task));
        let task_is_indirect = matches!(
            crate::sema::tycheck::utils::normalize_aliases(self.gcx, self.thir.exprs[task].ty)
                .kind(),
            TyKind::Reference(..) | TyKind::Pointer(..)
        );
        if task_is_indirect {
            task_place.projection.push(PlaceElem::Deref);
        }
        let token_local = self.new_temp_with_ty(task_handle_ty(self.gcx), span);
        let token = task_token_place(self.gcx, task_place);
        self.push_assign(
            block,
            Place::from_local(token_local),
            Rvalue::Use(Operand::Copy(token)),
            span,
        );
        block.and(token_local)
    }

    fn lower_task_output_descriptor_to_local(
        &mut self,
        block: BasicBlockId,
        ty: Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<LocalId> {
        let id = find_std_function(
            self.gcx,
            "intrinsic",
            "__intrinsic_task_output_descriptor",
            span,
        )
        .unwrap_or_else(|_| panic!("task lowering requires its output descriptor intrinsic"));
        let generic_args = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(ty)]);
        let function_ty = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
            self.gcx,
            self.gcx.get_type(id),
            generic_args,
        );
        let local = self.new_temp_with_ty(self.gcx.get_signature(id).output, span);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: function_ty,
                    value: mir::ConstantKind::Function(id, generic_args, function_ty),
                }),
                args: vec![],
                destination: Place::from_local(local),
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.and(local)
    }

    fn lower_size_of_type_to_local(
        &mut self,
        block: BasicBlockId,
        ty: crate::sema::models::Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<LocalId> {
        let size_local = self.new_temp_with_ty(self.gcx.types.uint, span);
        if matches!(ty.kind(), TyKind::Never) {
            self.push_assign(
                block,
                Place::from_local(size_local),
                Rvalue::Use(Operand::Constant(Constant {
                    ty: self.gcx.types.uint,
                    value: mir::ConstantKind::Integer(0),
                })),
                span,
            );
            return block.and(size_local);
        }
        let size_of_id = find_std_function(self.gcx, "mem", "sizeOf", span)
            .unwrap_or_else(|_| panic!("lowering requires std.mem.sizeOf"));
        let size_of_ty = self.gcx.get_type(size_of_id);
        let after_size = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: size_of_ty,
                    value: mir::ConstantKind::Function(
                        size_of_id,
                        self.gcx
                            .store
                            .interners
                            .intern_generic_args(vec![GenericArgument::Type(ty)]),
                        size_of_ty,
                    ),
                }),
                args: vec![],
                destination: Place::from_local(size_local),
                target: after_size,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        after_size.and(size_local)
    }

    fn lower_bool_to_u8_local(
        &mut self,
        mut block: BasicBlockId,
        expr: ExprId,
        span: Span,
    ) -> BlockAnd<LocalId> {
        let policy_operand = unpack!(block = self.as_operand(block, expr));
        let policy_local = self.new_temp_with_ty(self.gcx.types.uint8, span);
        self.push_assign(
            block,
            Place::from_local(policy_local),
            Rvalue::Cast {
                operand: policy_operand,
                ty: self.gcx.types.uint8,
                kind: CastKind::Numeric,
            },
            span,
        );
        block.and(policy_local)
    }

    fn lower_io_wait_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
        which: AsyncRuntimeFn,
    ) -> BlockAnd<()> {
        let [source_id] = args else {
            panic!("ICE: async io wait lowering expects exactly one source id argument");
        };

        let destination_ty = self.body.place_ty(self.gcx, &destination);
        assert_eq!(
            destination_ty,
            self.gcx.async_handle_ty(),
            "ICE: async io wait intrinsic must lower into an async handle destination"
        );

        let source_id_operand = unpack!(block = self.as_operand(block, *source_id));
        let wait_id = find_or_register_async_runtime_function(self.gcx, which, span);
        let wait_ty = self.gcx.get_type(wait_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: wait_ty,
                    value: mir::ConstantKind::Function(wait_id, GenericArguments::empty(), wait_ty),
                }),
                args: vec![source_id_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );

        next.unit()
    }

    fn is_hidden_spawn_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self.gcx.symbol_eq(
            self.gcx.definition_ident(id).symbol,
            "__intrinsic_spawn_async",
        )
    }

    fn is_std_task_free_function_named(&self, callee: ExprId, name: &str) -> bool {
        self.is_std_task_definition_named(callee, name, DefinitionKind::Function)
    }

    fn is_std_task_associated_function_named(&self, callee: ExprId, name: &str) -> bool {
        self.is_std_task_definition_named(callee, name, DefinitionKind::AssociatedFunction)
    }

    fn is_std_task_definition_named(
        &self,
        callee: ExprId,
        name: &str,
        kind: DefinitionKind,
    ) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };
        self.gcx.try_definition_kind(id) == Some(kind)
            && definition_in_std_module(self.gcx, id, "task")
            && self
                .gcx
                .symbol_eq(self.gcx.definition_symbol_or_fallback(id), name)
    }

    fn is_hidden_is_task_cancelled_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_is_task_cancelled")
    }

    fn is_hidden_dump_tasks_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_dump_tasks")
    }

    fn is_hidden_select_tasks_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_select_tasks")
    }

    fn is_hidden_task_timeout_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_timeout")
    }

    fn is_hidden_blocking_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_blocking")
    }

    fn lower_dump_tasks_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [] = args else {
            panic!("ICE: task dump lowering expects no arguments");
        };
        let func_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::DumpTasks, span);
        let func_ty = self.gcx.get_type(func_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: func_ty,
                    value: mir::ConstantKind::Function(func_id, GenericArguments::empty(), func_ty),
                }),
                args: vec![],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn lower_select_tasks_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [first, second] = args else {
            panic!("ICE: task selection lowering expects exactly two task arguments");
        };
        assert_eq!(
            self.body.place_ty(self.gcx, &destination),
            self.gcx.async_handle_ty(),
            "ICE: task selection intrinsic must lower into an async handle destination"
        );

        let first_token = unpack!(block = self.lower_task_token_local(block, *first, span));
        let second_token = unpack!(block = self.lower_task_token_local(block, *second, span));
        let select_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::SelectTasks, span);
        let select_ty = self.gcx.get_type(select_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: select_ty,
                    value: mir::ConstantKind::Function(
                        select_id,
                        GenericArguments::empty(),
                        select_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(first_token)),
                    Operand::Copy(Place::from_local(second_token)),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn lower_task_timeout_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [task, duration] = args else {
            panic!("ICE: task timeout lowering expects a task and duration");
        };
        assert_eq!(
            self.body.place_ty(self.gcx, &destination),
            self.gcx.async_handle_ty(),
            "ICE: task timeout intrinsic must lower into an async handle destination"
        );

        let task_token = unpack!(block = self.lower_task_token_local(block, *task, span));
        let duration_local = unpack!(block = self.as_temp(block, *duration));
        let duration_place = Place::from_local(duration_local);
        let timeout_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::TaskTimeout, span);
        let timeout_ty = self.gcx.get_type(timeout_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: timeout_ty,
                    value: mir::ConstantKind::Function(
                        timeout_id,
                        GenericArguments::empty(),
                        timeout_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(task_token)),
                    Operand::Copy(duration_secs_place(self.gcx, duration_place.clone())),
                    Operand::Copy(duration_nanos_place(self.gcx, duration_place)),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn lower_blocking_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [thunk] = args else {
            panic!("ICE: blocking lowering expects exactly one closure argument");
        };
        assert_eq!(
            self.body.place_ty(self.gcx, &destination),
            self.gcx.async_handle_ty(),
            "ICE: blocking intrinsic must lower into an async handle destination"
        );

        let output_ty = intrinsic_type_arg(self.thir, callee, 0);
        let closure_ty = intrinsic_type_arg(self.thir, callee, 1);
        let generic_args = self.gcx.store.interners.intern_generic_args(vec![
            GenericArgument::Type(output_ty),
            GenericArgument::Type(closure_ty),
        ]);

        // Move the closure into a compiler-generated async frame. The async
        // handle keeps that frame rooted while the blocking pool owns it.
        let thunk_operand = unpack!(block = self.as_operand(block, *thunk));
        let adapter_id = find_std_function(self.gcx, "task", "__blockingInvoke", span)
            .unwrap_or_else(|_| panic!("blocking lowering requires std.task.__blockingInvoke"));
        let adapter_inputs = self.gcx.store.interners.intern_ty_list(vec![closure_ty]);
        let adapter_ty = self.gcx.store.interners.intern_ty(TyKind::FnPointer {
            effects: Default::default(),
            inputs: adapter_inputs,
            output: self.gcx.async_handle_ty(),
        });
        let adapter_local = self.new_temp_with_ty(self.gcx.async_handle_ty(), span);
        let after_adapter = self.new_block();
        let adapter_unwind = self.call_unwind_action(span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: adapter_ty,
                    value: mir::ConstantKind::Function(adapter_id, generic_args, adapter_ty),
                }),
                args: vec![thunk_operand],
                destination: Place::from_local(adapter_local),
                target: after_adapter,
                unwind: adapter_unwind,
            },
        );
        block = after_adapter;

        let desc_local =
            unpack!(block = self.lower_task_output_descriptor_to_local(block, output_ty, span));
        let runtime_id =
            find_or_register_async_runtime_function(self.gcx, AsyncRuntimeFn::Blocking, span);
        let runtime_ty = self.gcx.get_type(runtime_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: runtime_ty,
                    value: mir::ConstantKind::Function(
                        runtime_id,
                        GenericArguments::empty(),
                        runtime_ty,
                    ),
                }),
                args: vec![
                    Operand::Copy(Place::from_local(adapter_local)),
                    Operand::Copy(Place::from_local(desc_local)),
                ],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn lower_is_task_cancelled_call(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [] = args else {
            panic!("ICE: task is_cancelled lowering expects no arguments");
        };
        let destination_ty = self.body.place_ty(self.gcx, &destination);
        assert_eq!(
            destination_ty, self.gcx.types.bool,
            "ICE: task is_cancelled intrinsic must lower into a bool destination"
        );
        let func_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::IsTaskCancelled,
            span,
        );
        let func_ty = self.gcx.get_type(func_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: func_ty,
                    value: mir::ConstantKind::Function(func_id, GenericArguments::empty(), func_ty),
                }),
                args: vec![],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn is_hidden_sleep_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self
            .gcx
            .symbol_eq(self.gcx.definition_ident(id).symbol, "__intrinsic_sleep")
    }

    fn is_hidden_wait_readable_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self.gcx.symbol_eq(
            self.gcx.definition_ident(id).symbol,
            "__intrinsic_wait_readable",
        )
    }

    fn is_hidden_wait_writable_intrinsic(&self, callee: ExprId) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };

        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self.gcx.symbol_eq(
            self.gcx.definition_ident(id).symbol,
            "__intrinsic_wait_writable",
        )
    }

    fn is_hidden_channel_wait_send_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_channel_wait_send")
    }

    fn is_hidden_channel_wait_recv_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_channel_wait_recv")
    }

    fn is_hidden_mutex_lock_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_mutex_lock")
    }

    fn is_hidden_rwlock_read_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_rwlock_read")
    }

    fn is_hidden_rwlock_write_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_rwlock_write")
    }

    fn is_hidden_intrinsic_named(&self, callee: ExprId, name: &str) -> bool {
        let ExprKind::Zst { id, .. } = self.thir.exprs[callee].kind else {
            return false;
        };
        matches!(
            self.gcx.get_signature(id).abi,
            Some(crate::hir::Abi::Intrinsic)
        ) && self
            .gcx
            .symbol_eq(self.gcx.definition_ident(id).symbol, name)
    }

    fn is_hidden_cancel_task_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_cancel_task")
    }

    fn is_hidden_task_result_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_result")
    }

    fn is_hidden_task_group_create_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_create")
    }

    fn is_hidden_task_group_spawn_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_spawn")
    }

    fn is_hidden_task_group_next_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_next")
    }

    fn is_hidden_task_group_close_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_close")
    }

    fn is_hidden_task_group_cancel_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_cancel")
    }

    fn is_hidden_task_group_destroy_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_destroy")
    }

    fn is_hidden_task_group_destroy_and_rethrow_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_task_group_destroy_and_rethrow")
    }

    fn is_hidden_panic_payload_message_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_panic_payload_message")
    }

    fn is_hidden_panic_payload_rethrow_intrinsic(&self, callee: ExprId) -> bool {
        self.is_hidden_intrinsic_named(callee, "__intrinsic_panic_payload_rethrow")
    }

    fn lower_panic_payload_message_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [data_arg] = args else {
            panic!("ICE: panic_payload_message expects exactly one argument");
        };
        let data_operand = unpack!(block = self.as_operand(block, *data_arg));
        let msg_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::PanicPayloadMessage,
            span,
        );
        let msg_ty = self.gcx.get_type(msg_id);
        let next = self.new_block();
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: msg_ty,
                    value: mir::ConstantKind::Function(msg_id, GenericArguments::empty(), msg_ty),
                }),
                args: vec![data_operand],
                destination,
                target: next,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        next.unit()
    }

    fn lower_panic_payload_rethrow_call(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        args: &[ExprId],
        span: Span,
    ) -> BlockAnd<()> {
        let [data_arg] = args else {
            panic!("ICE: panic_payload_rethrow expects exactly one argument");
        };
        let data_operand = unpack!(block = self.as_operand(block, *data_arg));
        let rethrow_id = find_or_register_async_runtime_function(
            self.gcx,
            AsyncRuntimeFn::PanicPayloadRethrow,
            span,
        );
        let rethrow_ty = self.gcx.get_type(rethrow_id);
        let next = self.new_block();
        let unwind = self.call_unwind_action(span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: Operand::Constant(Constant {
                    ty: rethrow_ty,
                    value: mir::ConstantKind::Function(
                        rethrow_id,
                        GenericArguments::empty(),
                        rethrow_ty,
                    ),
                }),
                args: vec![data_operand],
                destination,
                target: next,
                // The runtime helper re-raises the captured panic, so the
                // wrapper must run active cleanup scopes before unwinding to
                // its caller. That includes compiler-emitted GC shadow pops.
                unwind,
            },
        );
        next.unit()
    }

    fn async_callable_operand(
        &mut self,
        block: BasicBlockId,
        callee: ExprId,
        callee_ty: crate::sema::models::Ty<'ctx>,
    ) -> BlockAnd<Operand<'ctx>> {
        let callee_expr = &self.thir.exprs[callee];
        match &callee_expr.kind {
            ExprKind::Zst { id, generic_args } if self.gcx.definition_is_async(*id) => {
                let async_callee_ty = match callee_ty.kind() {
                    crate::sema::models::TyKind::FnPointer { inputs, .. } => self
                        .gcx
                        .store
                        .interners
                        .intern_ty(crate::sema::models::TyKind::FnPointer {
                            effects: Default::default(),
                            inputs,
                            output: self.gcx.async_handle_ty(),
                        }),
                    _ => self.gcx.async_handle_ty(),
                };
                block.and(Operand::Constant(Constant {
                    ty: async_callee_ty,
                    value: mir::ConstantKind::Function(
                        *id,
                        generic_args.unwrap_or(GenericArguments::empty()),
                        async_callee_ty,
                    ),
                }))
            }
            _ => self.as_operand(block, callee),
        }
    }

    fn goto_if_fallthrough(
        &mut self,
        source: BasicBlockId,
        destination: BasicBlockId,
        span: Span,
    ) -> bool {
        if self.body.basic_blocks[source].terminator.is_none() {
            self.goto(source, destination, span);
            true
        } else {
            false
        }
    }

    fn lower_match_expr(
        &mut self,
        destination: Place<'ctx>,
        mut block: BasicBlockId,
        expr_id: ExprId,
        scrutinee: ExprId,
    ) -> BlockAnd<()> {
        let expr = &self.thir.exprs[expr_id];
        let mut scrutinee_place = unpack!(block = self.as_place(block, scrutinee));
        let ExprKind::Match { arms, .. } = &expr.kind else {
            unreachable!()
        };
        if arms.iter().any(|arm| self.thir.arms[*arm].guard.is_some()) {
            // A guard may replace the source through any alias. Freeze value
            // storage before testing patterns so fallback projections remain
            // valid. Unguarded matches inspect the source directly.
            let local = self.new_temp_with_ty(self.thir.exprs[scrutinee].ty, expr.span);
            self.push_storage_live(block, local, expr.span);
            self.register_storage_cleanup(local, expr.span);
            let snapshot = Place::from_local(local);
            self.push_assign(
                block,
                snapshot.clone(),
                Rvalue::Use(Operand::Copy(scrutinee_place)),
                expr.span,
            );
            scrutinee_place = snapshot;
        }

        let tree = &self
            .thir
            .match_reports
            .get(&expr_id)
            .expect("exhaustiveness compiles every match before MIR construction")
            .tree;

        let mut var_places: FxHashMap<usize, Place<'ctx>> = FxHashMap::default();
        var_places.insert(tree.root_var.id, scrutinee_place.clone());

        let join_block = self.new_block_with_note("match-join".into());
        let mut join_has_incoming = false;
        self.lower_match_decision(
            block,
            &tree.decision,
            &destination,
            join_block,
            &mut join_has_incoming,
            &var_places,
            expr.span,
            None,
        );
        if !join_has_incoming {
            self.terminate(join_block, expr.span, TerminatorKind::Unreachable);
        }
        join_block.unit()
    }

    /// Binding copies belong to this arm, including on early exit or unwind.
    /// A successful guard passes its existing copies through to the body.
    fn lower_match_arm(
        &mut self,
        block: BasicBlockId,
        body: &thir::match_tree::Body<'ctx>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        join_has_incoming: &mut bool,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        prepared: Option<(Option<CleanupId>, CleanupScopeId)>,
    ) {
        let (saved_cleanup, saved_scope) =
            prepared.unwrap_or((self.current_cleanup, self.current_cleanup_scope));
        let block = if prepared.is_none() {
            self.current_cleanup_scope = self.fresh_cleanup_scope();
            self.bind_match_bindings(block, body.arm, &body.bindings, var_places)
                .into_block()
        } else {
            block
        };
        let arm = &self.thir.arms[body.arm];
        let block = self
            .expr_into_dest(destination.clone(), block, arm.body)
            .into_block();
        if self.body.basic_blocks[block].terminator.is_none() {
            let mut cache = FxHashMap::default();
            cache.insert(saved_cleanup, join_block);
            let cleanup = self.ensure_cleanup_path(
                self.current_cleanup,
                saved_cleanup,
                join_block,
                &mut cache,
            );
            self.goto(block, cleanup, arm.span);
            *join_has_incoming = true;
        }
        self.current_cleanup = saved_cleanup;
        self.current_cleanup_scope = saved_scope;
    }

    fn lower_match_decision(
        &mut self,
        mut block: BasicBlockId,
        decision: &thir::match_tree::Decision<'ctx>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        join_has_incoming: &mut bool,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
        condition_targets: Option<(BasicBlockId, BasicBlockId)>,
    ) {
        match decision {
            thir::match_tree::Decision::Dereference {
                source,
                target,
                next,
            } => {
                let mut referent = var_places
                    .get(&source.id)
                    .expect("structural reference source")
                    .clone();
                referent.projection.push(PlaceElem::Deref);
                if next.has_guard() {
                    // Only the read value is frozen: ordinary reference/handle
                    // bindings still retain their shared-target semantics.
                    let snapshot = self.new_temp_with_ty(target.ty, span);
                    let place = Place::from_local(snapshot);
                    self.push_assign(
                        block,
                        place.clone(),
                        Rvalue::Use(Operand::Copy(referent)),
                        span,
                    );
                    referent = place;
                }
                let mut places = var_places.clone();
                places.insert(target.id, referent);
                self.lower_match_decision(
                    block,
                    next,
                    destination,
                    join_block,
                    join_has_incoming,
                    &places,
                    span,
                    condition_targets,
                );
            }
            thir::match_tree::Decision::Success(body) => {
                self.lower_successful_match(
                    block, body, destination, join_block, join_has_incoming,
                    var_places, span, condition_targets,
                );
            }
            thir::match_tree::Decision::Failure => {
                self.terminate(block, span, TerminatorKind::Unreachable);
            }
            thir::match_tree::Decision::Guard { prepare, tests, guard: guard_expr, body, fallback } => {
                let mut saved_places;
                let var_places = if prepare.is_empty() {
                    var_places
                } else {
                    saved_places = var_places.clone();
                    for probe in prepare {
                        let value = self.match_type_value(block, &var_places[&probe.source.id],
                            probe.target, probe.result.ty, span);
                        saved_places.insert(probe.result.id, value);
                    }
                    &saved_places
                };
                let mut converted_places = None;
                let type_fallback = if tests.is_empty() {
                    None
                } else {
                    let mismatch = self.new_block_with_note("type-pattern-fallback".into());
                    let places = converted_places.insert(var_places.clone());
                    for test in tests {
                        block = self.lower_match_type_test(block, test, places, mismatch, span);
                    }
                    Some(mismatch)
                };
                let success_places = converted_places.as_ref().unwrap_or(var_places);
                let else_block = if let Some(guard_expr) = guard_expr {
                    assert!(
                        condition_targets.is_none(),
                        "binding conditions have no guarded arms"
                    );
                    let arm = &self.thir.arms[body.arm];
                    let guard_block =
                        self.new_block_with_note(format!("match-guard-{}", body.arm.index()));
                    if !self.goto_if_fallthrough(block, guard_block, span) {
                        return;
                    }
                    // Guard and body share one set of writable binding copies.
                    // Failed candidates discard those copies before the fallback.
                    let saved_cleanup = self.current_cleanup;
                    let saved_scope = self.current_cleanup_scope;
                    self.current_cleanup_scope = self.fresh_cleanup_scope();
                    block = self
                        .bind_match_bindings(guard_block, body.arm, &body.bindings, success_places)
                        .into_block();
                    let guard_operand = unpack!(block = self.as_operand(block, *guard_expr));
                    let candidate_cleanup = self.current_cleanup;
                    let candidate_scope = self.current_cleanup_scope;
                    let then_block =
                        self.new_block_with_note(format!("match-arm-{}", body.arm.index()));
                    let discard_block = self.new_block_with_note("match-guard-discard".into());
                    let else_block = type_fallback.unwrap_or_else(|| self.new_block_with_note("match-guard-fallback".into()));
                    self.terminate(
                        block,
                        arm.span,
                        TerminatorKind::if_(guard_operand, then_block, discard_block),
                    );
                    self.lower_match_arm(
                        then_block,
                        body,
                        destination,
                        join_block,
                        join_has_incoming,
                        success_places,
                        Some((saved_cleanup, saved_scope)),
                    );
                    self.current_cleanup = candidate_cleanup;
                    self.current_cleanup_scope = candidate_scope;
                    let mut cache = FxHashMap::default();
                    cache.insert(saved_cleanup, else_block);
                    let cleanup = self.ensure_cleanup_path(
                        candidate_cleanup,
                        saved_cleanup,
                        else_block,
                        &mut cache,
                    );
                    self.goto(discard_block, cleanup, arm.span);
                    self.current_cleanup = saved_cleanup;
                    self.current_cleanup_scope = saved_scope;
                    else_block
                } else {
                    self.lower_successful_match(
                        block, body,
                        destination, join_block, join_has_incoming, success_places, span,
                        condition_targets,
                    );
                    type_fallback.expect("conditional arm requires a guard or type test")
                };
                self.lower_match_decision(
                    else_block, fallback, destination, join_block, join_has_incoming,
                    var_places, span, condition_targets,
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
                            join_has_incoming,
                            var_places,
                            span,
                            condition_targets,
                        );
                    } else {
                        self.terminate(block, span, TerminatorKind::Unreachable);
                    }
                    return;
                };

                match &first_case.constructor {
                    thir::match_tree::Constructor::Tuple(_)
                    | thir::match_tree::Constructor::Struct(_) => {
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
                            join_has_incoming,
                            &case_places,
                            span,
                            condition_targets,
                        );
                    }
                    thir::match_tree::Constructor::Interval(_)
                    | thir::match_tree::Constructor::Literal(
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
                            join_has_incoming,
                            var_places,
                            span,
                            condition_targets,
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
                                | thir::match_tree::Constructor::Interval(_)
                                | thir::match_tree::Constructor::Tuple(_)
                                | thir::match_tree::Constructor::Struct(_) => {
                                    self.terminate(block, span, TerminatorKind::Unreachable);
                                    return;
                                }
                            };

                            self.lower_match_decision(
                                case_block,
                                &case.body,
                                destination,
                                join_block,
                                join_has_incoming,
                                &case_places,
                                span,
                                condition_targets,
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
                                join_has_incoming,
                                var_places,
                                span,
                                condition_targets,
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

    fn lower_successful_match(
        &mut self,
        block: BasicBlockId,
        body: &thir::match_tree::Body<'ctx>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        join_has_incoming: &mut bool,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
        condition_targets: Option<(BasicBlockId, BasicBlockId)>,
    ) {
        let arm = &self.thir.arms[body.arm];
        let arm_block = self.new_block_with_note(format!("match-arm-{}", body.arm.index()));
        if !self.goto_if_fallthrough(block, arm_block, span) {
            return;
        }
        if let Some((if_true, if_false)) = condition_targets {
            let arm_block = self
                .bind_match_bindings(arm_block, body.arm, &body.bindings, var_places)
                .into_block();
            let ExprKind::Literal(thir::Constant {
                value: thir::ConstantKind::Bool(value),
                ..
            }) = &self.thir.exprs[arm.body].kind
            else {
                panic!("binding-condition decision must end in a boolean literal");
            };
            self.goto(arm_block, if *value { if_true } else { if_false }, arm.span);
            return;
        }
        self.lower_match_arm(
            arm_block,
            body,
            destination,
            join_block,
            join_has_incoming,
            var_places,
            None,
        );
    }

    /// Use the checked cast's success tag for a bound test. A tag-only test
    /// needs no converted storage. All mismatches share the next arm.
    fn lower_match_type_test(
        &mut self,
        mut block: BasicBlockId,
        test: &thir::match_tree::TypeTest<'ctx>,
        places: &mut FxHashMap<usize, Place<'ctx>>,
        mismatch: BasicBlockId,
        span: Span,
    ) -> BasicBlockId {
        let success = self.new_block_with_note("type-pattern-success".into());
        let (place, ty) = if let Some(result) = test.prepared {
            (places[&result.id].clone(), result.ty)
        } else {
            let ty = if test.converted.is_some() {
                test.target.optional(self.gcx).0
            } else {
                self.gcx.types.bool
            };
            (self.match_type_value(block, &places[&test.source.id], test.target, ty, span), ty)
        };
        if ty == self.gcx.types.bool {
            self.terminate(block, span, TerminatorKind::if_(Operand::Copy(place), success, mismatch));
        } else {
            let TyKind::Adt(adt, _) = ty.kind() else { unreachable!("checked cast returns Optional") };
            let def = self.gcx.get_enum_definition(adt.id);
            let some = def.variants.iter().position(|v| self.gcx.symbol_eq(v.name, "some"))
                .expect("Optional.some");
            if let Some(var) = test.converted {
                self.add_variant_case_places(places, &place, def.variants[some].name,
                    thir::VariantIndex::from_usize(some), &[var]);
            }
            let discr = unpack!(block = self.enum_discriminant_operand(block, &place, span));
            self.terminate(block, span, TerminatorKind::SwitchInt {
                discr, targets: vec![(some as u128, success)], otherwise: mismatch,
            });
        }
        success
    }

    fn match_type_value(
        &mut self,
        block: BasicBlockId,
        source: &Place<'ctx>,
        target: Ty<'ctx>,
        ty: Ty<'ctx>,
        span: Span,
    ) -> Place<'ctx> {
        let result = Place::from_local(self.new_temp_with_ty(ty, span));
        let kind = if ty == self.gcx.types.bool {
            CastKind::ExistentialTypeIs { target }
        } else {
            CastKind::ExistentialTryCast { target }
        };
        self.push_assign(block, result.clone(), Rvalue::Cast {
            operand: Operand::Copy(source.clone()), ty, kind,
        }, span);
        result
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
        join_has_incoming: &mut bool,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
        condition_targets: Option<(BasicBlockId, BasicBlockId)>,
    ) {
        if cases.is_empty() {
            if let Some(fallback) = fallback {
                self.lower_match_decision(
                    block,
                    fallback,
                    destination,
                    join_block,
                    join_has_incoming,
                    var_places,
                    span,
                    condition_targets,
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
                join_has_incoming,
                var_places,
                span,
                condition_targets,
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
                block = self.build_match_test_operand(
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
                join_has_incoming,
                var_places,
                span,
                condition_targets,
            );

            block = next_block;
        }
    }

    fn build_match_test_operand(
        &mut self,
        mut block: BasicBlockId,
        branch_place: &Place<'ctx>,
        branch_ty: crate::sema::models::Ty<'ctx>,
        constructor: &thir::match_tree::Constructor,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        if let thir::match_tree::Constructor::Interval(interval) = constructor {
            // Cases partition the entire domain in ascending order. Earlier
            // tests have already excluded every value below this interval.
            let upper = *interval.end();
            let value = if matches!(branch_ty.kind(), TyKind::Rune) {
                mir::ConstantKind::Rune(char::from_u32(upper as u32).unwrap())
            } else {
                mir::ConstantKind::Integer(upper as u64)
            };
            let test = Place::from_local(self.new_temp_with_ty(self.gcx.types.bool, span));
            self.push_assign(block, test.clone(), Rvalue::BinaryOp {
                op: BinaryOperator::Leq,
                lhs: Operand::Copy(branch_place.clone()),
                rhs: Operand::Constant(Constant { ty: branch_ty, value }),
            }, span);
            return block.and(Operand::Copy(test));
        }
        let literal = match constructor {
            thir::match_tree::Constructor::Literal(key) => key,
            _ => {
                return block.and(Operand::Constant(Constant {
                    ty: self.gcx.types.bool,
                    value: mir::ConstantKind::Bool(false),
                }));
            }
        };

        if let thir::match_tree::LiteralKey::String(s) = literal {
            let string_eq_id = self.find_function_in_std("string", "stringEq", span);
            let string_eq_ty = self.gcx.get_type(string_eq_id);
            let bool_ty = match string_eq_ty.kind() {
                crate::sema::models::TyKind::FnPointer { output, .. } => output,
                _ => panic!("stringEq must be a function"),
            };
            let string_eq_func = Operand::Constant(Constant {
                ty: string_eq_ty,
                value: mir::ConstantKind::Function(string_eq_id, List::empty(), string_eq_ty),
            });
            let rhs = Operand::Constant(Constant {
                ty: branch_ty,
                value: mir::ConstantKind::String(*s),
            });
            let temp = self.new_temp_with_ty(bool_ty, span);
            let destination = Place::from_local(temp);
            let next_block = self.new_block();
            let unwind = self.call_unwind_for_callee(&string_eq_func, span);
            self.terminate(
                block,
                span,
                TerminatorKind::Call {
                    func: string_eq_func,
                    args: vec![Operand::Copy(branch_place.clone()), rhs],
                    destination: destination.clone(),
                    target: next_block,
                    unwind,
                },
            );
            block = next_block;
            return block.and(Operand::Copy(destination));
        }

        let value = match literal {
            thir::match_tree::LiteralKey::Integer(i) => mir::ConstantKind::Integer(*i),
            thir::match_tree::LiteralKey::Float(bits) => {
                mir::ConstantKind::Float(f64::from_bits(*bits))
            }
            thir::match_tree::LiteralKey::Rune(r) => mir::ConstantKind::Rune(*r),
            thir::match_tree::LiteralKey::String(_) => unreachable!(),
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
        block.and(Operand::Copy(Place::from_local(temp)))
    }

    /// Pack variadic arguments into a fixed array and pass its storage as the
    /// synthetic Span.
    fn lower_variadic_sequence(
        &mut self,
        mut block: BasicBlockId,
        args: &[ExprId],
        span_ty: Ty<'ctx>,
        elem_ty: Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        let pack_ty = self.variadic_pack_ty(elem_ty, args.len());
        let pack = self.new_temp_with_ty(pack_ty, span);
        self.push_storage_live(block, pack, span);
        self.register_storage_cleanup(pack, span);

        let mut fields = Vec::with_capacity(args.len());
        for argument in args {
            fields.push(unpack!(block = self.as_operand(block, *argument)));
        }
        self.push_assign(
            block,
            Place::from_local(pack),
            Rvalue::Aggregate {
                kind: AggregateKind::Array {
                    len: args.len(),
                    element: elem_ty,
                },
                fields: IndexVec::from_vec(fields),
            },
            span,
        );

        let TyKind::Adt(definition, generic_args) = span_ty.kind() else {
            unreachable!()
        };
        let definition = self.gcx.get_struct_definition(definition.id);
        let pointer_ty = Ty::new(
            TyKind::Pointer(elem_ty, crate::hir::Mutability::Immutable),
            self.gcx,
        );
        let pointer = self.new_temp_with_ty(pointer_ty, span);
        if args.is_empty() {
            // Empty packs never fabricate a reference to absent element storage.
            self.push_assign(
                block,
                Place::from_local(pointer),
                Rvalue::Zeroed { ty: pointer_ty },
                span,
            );
        } else {
            let whole_ref_ty = Ty::new(TyKind::Reference(pack_ty), self.gcx);
            let whole = self.new_temp_with_ty(whole_ref_ty, span);

            self.push_assign(
                block,
                Place::from_local(whole),
                Rvalue::Ref {
                    place: Place::from_local(pack),
                },
                span,
            );
            let element_ref_ty = Ty::new(TyKind::Reference(elem_ty), self.gcx);
            let first = self.new_temp_with_ty(element_ref_ty, span);

            // A nonempty inline array starts at element zero. Preserve the
            // whole-array control/dependencies while changing its data type;
            // protecting only element zero would lose other elements' debts.
            self.push_assign(
                block,
                Place::from_local(first),
                Rvalue::Cast {
                    kind: CastKind::Pointer,
                    operand: Operand::Copy(Place::from_local(whole)),
                    ty: element_ref_ty,
                },
                span,
            );
            self.push_assign(
                block,
                Place::from_local(pointer),
                Rvalue::Cast {
                    kind: CastKind::Pointer,
                    operand: Operand::Copy(Place::from_local(first)),
                    ty: pointer_ty,
                },
                span,
            );
        }
        // The slice pointer roots the entire pack allocation.
        let view_fields = vec![
            Operand::Copy(Place::from_local(pointer)),
            Operand::Constant(Constant {
                ty: self.gcx.types.uint,
                value: mir::ConstantKind::Integer(args.len() as u64),
            }),
        ];
        let view = self.new_temp_with_ty(span_ty, span);

        self.push_assign(
            block,
            Place::from_local(view),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: definition.adt_def.id,
                    variant_index: None,
                    generic_args,
                },
                fields: IndexVec::from_vec(view_fields),
            },
            span,
        );
        block.and(Operand::Copy(Place::from_local(view)))
    }

    fn lower_list_literal(
        &mut self,
        mut block: BasicBlockId,
        destination: Place<'ctx>,
        args: &[ExprId],
        list_ty: Ty<'ctx>,
        elem_ty: Ty<'ctx>,
        span: Span,
    ) -> BasicBlockId {
        // Own native storage before evaluating elements. Every append publishes
        // one initialized owner atomically; panic/cancellation drops exactly the
        // completed prefix, including across awaits in element expressions.
        let owner = self.new_temp_with_ty(list_ty, span);
        self.push_storage_live(block, owner, span);
        self.register_storage_cleanup(owner, span);

        let owner = Place::from_local(owner);
        let generics = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![GenericArgument::Type(elem_ty)]);
        let function = |builder: &Self, name| {
            let id = builder.find_function_in_std("collections", name, span);
            let ty = crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(
                builder.gcx,
                builder.gcx.get_type(id),
                generics,
            );
            Operand::Constant(Constant {
                ty,
                value: mir::ConstantKind::Function(id, generics, ty),
            })
        };
        let constructor = function(self, "__list_with_capacity");
        let append = function(self, "__list_append");
        let next = self.new_block();
        let unwind = self.call_unwind_action(span);
        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: constructor,
                args: vec![Operand::Constant(Constant {
                    ty: self.gcx.types.uint,
                    value: mir::ConstantKind::Integer(args.len() as u64),
                })],
                destination: owner.clone(),
                target: next,
                unwind,
            },
        );
        block = next;
        for expression in args {
            let value = unpack!(block = self.as_operand(block, *expression));
            let receiver_ty = Ty::new(TyKind::Reference(list_ty), self.gcx);
            let receiver = Place::from_local(self.new_temp_with_ty(receiver_ty, span));
            self.push_assign(
                block,
                receiver.clone(),
                Rvalue::Ref {
                    place: owner.clone(),
                },
                span,
            );
            let result = Place::from_local(self.new_temp_with_ty(self.gcx.types.void, span));
            let next = self.new_block();
            let unwind = self.call_unwind_action(span);
            self.terminate(
                block,
                span,
                TerminatorKind::Call {
                    func: append.clone(),
                    args: vec![Operand::Copy(receiver), value],
                    destination: result,
                    target: next,
                    unwind,
                },
            );
            block = next;
        }
        self.push_assign(block, destination, Rvalue::Use(Operand::Copy(owner)), span);
        block
    }

    fn find_function_in_std(
        &self,
        module: &str,
        name: &str,
        _span: Span,
    ) -> crate::hir::DefinitionID {
        let std_pkg = self.gcx.std_package_index().expect("std package found");
        let output = self.gcx.resolution_output(std_pkg);

        let in_module = |id: crate::hir::DefinitionID| {
            let mut current = id;
            while let Some(parent) = output.definition_to_parent.get(&current).cloned() {
                if parent == current {
                    break;
                }
                current = parent;
                if matches!(
                    output.definition_to_kind.get(&current),
                    Some(DefinitionKind::Module)
                ) {
                    if let Some(ident) = output.definition_to_ident.get(&current) {
                        if self.gcx.symbol_eq(ident.symbol, module) {
                            return true;
                        }
                    }
                }
            }
            false
        };

        // Linear scan for now (slow but works)
        let mut fallback = None;
        for (id, ident) in output.definition_to_ident.iter() {
            if self.gcx.symbol_eq(ident.symbol, name) {
                if !matches!(
                    output.definition_to_kind.get(id),
                    Some(DefinitionKind::Function)
                ) {
                    continue;
                }
                let has_sig = self
                    .gcx
                    .with_type_database(id.package(), |db| db.def_to_fn_sig.contains_key(id));
                if !has_sig {
                    continue;
                }
                if in_module(*id) {
                    return *id;
                }
                fallback = Some(*id);
            }
        }
        if let Some(id) = fallback {
            return id;
        }
        panic!(
            "Standard library function {} not found in std.{}",
            name, module
        );
    }

    fn call_unwind_for_callee(
        &mut self,
        callee: &Operand<'ctx>,
        span: Span,
    ) -> mir::CallUnwindAction {
        if self.is_nounwind_callee(callee) {
            mir::CallUnwindAction::Terminate
        } else {
            self.call_unwind_action(span)
        }
    }

    fn is_nounwind_callee(&self, callee: &Operand<'ctx>) -> bool {
        let Operand::Constant(c) = callee else {
            return false;
        };
        let mir::ConstantKind::Function(def_id, _, _) = c.value else {
            return false;
        };
        matches!(
            self.gcx.get_signature(def_id).abi,
            Some(crate::hir::Abi::Intrinsic)
        )
    }

    pub(in crate::mir::builder) fn enum_discriminant_operand(
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
            proj.push(PlaceElem::VariantDowncast { name: name, index });
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
                    true, // Match bindings are mutable for now to allow pattern binding operations
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
            // A shared or-pattern local still begins a distinct binding on
            // every alternative that reaches the arm.
            self.push_storage_live(block, local, binding.span);

            self.register_storage_cleanup(local, binding.span);

            self.push_assign(
                block,
                Place::from_local(local),
                Rvalue::Use(Operand::Copy(src_place.clone())),
                binding.span,
            );
        }
        block.unit()
    }
}

/// The collected handle object every copy of a `Task` shares.
fn task_handle_ty<'ctx>(gcx: Gcx<'ctx>) -> Ty<'ctx> {
    crate::mir::optimize::async_transform::raw_ptr_ty(
        gcx,
        gcx.types.uint8,
        crate::hir::Mutability::Mutable,
    )
}

fn task_token_place<'ctx>(gcx: Gcx<'ctx>, task_place: Place<'ctx>) -> Place<'ctx> {
    let mut projection = task_place.projection;
    projection.push(PlaceElem::Field(
        FieldIndex::from_raw(0),
        task_handle_ty(gcx),
    ));
    Place {
        local: task_place.local,
        projection,
    }
}

fn intrinsic_type_arg<'ctx, 'thir>(
    thir: &'thir thir::ThirFunction<'ctx>,
    callee: ExprId,
    index: usize,
) -> crate::sema::models::Ty<'ctx> {
    let ExprKind::Zst { generic_args, .. } = thir.exprs[callee].kind else {
        panic!("ICE: intrinsic type arg requested from non-ZST callee");
    };
    generic_args
        .unwrap_or(GenericArguments::empty())
        .get(index)
        .copied()
        .and_then(GenericArgument::ty)
        .unwrap_or_else(|| panic!("ICE: intrinsic missing type argument {index}"))
}

fn duration_secs_place<'ctx>(gcx: Gcx<'ctx>, duration_place: Place<'ctx>) -> Place<'ctx> {
    let mut projection = duration_place.projection;
    projection.push(PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.uint64));
    Place {
        local: duration_place.local,
        projection,
    }
}

fn duration_nanos_place<'ctx>(gcx: Gcx<'ctx>, duration_place: Place<'ctx>) -> Place<'ctx> {
    let mut projection = duration_place.projection;
    projection.push(PlaceElem::Field(FieldIndex::from_raw(1), gcx.types.uint32));
    Place {
        local: duration_place.local,
        projection,
    }
}

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    /// Preserve condition-success edges instead of merging a binding match into
    /// a boolean temporary and branching again. Only success initializes its
    /// pattern locals; ordinary initialization dataflow can then prove their use.
    pub(in crate::mir::builder) fn lower_condition(
        &mut self,
        mut block: BasicBlockId,
        condition: ExprId,
        if_true: BasicBlockId,
        if_false: BasicBlockId,
    ) {
        let expr = &self.thir.exprs[condition];
        match &expr.kind {
            ExprKind::Logical { op, lhs, rhs } => {
                let next = self.new_block_with_note("condition connector".into());
                match op {
                    mir::LogicalOperator::And => self.lower_condition(block, *lhs, next, if_false),
                    mir::LogicalOperator::Or => self.lower_condition(block, *lhs, if_true, next),
                }
                self.lower_condition(next, *rhs, if_true, if_false);
            }
            ExprKind::Match {
                scrutinee,
                binding_condition: true,
                ..
            } => {
                let source = unpack!(block = self.as_place(block, *scrutinee));
                let tree = &self
                    .thir
                    .match_reports
                    .get(&condition)
                    .expect("binding match has a decision tree")
                    .tree;
                let mut places = FxHashMap::default();
                places.insert(tree.root_var.id, source);
                let unused_destination = self.unit_temp_place(expr.span);
                let mut unused_join = false;
                self.lower_match_decision(
                    block,
                    &tree.decision,
                    &unused_destination,
                    if_false,
                    &mut unused_join,
                    &places,
                    expr.span,
                    Some((if_true, if_false)),
                );
            }
            _ => {
                let operand = unpack!(block = self.as_operand(block, condition));
                self.terminate(
                    block,
                    expr.span,
                    TerminatorKind::if_(operand, if_true, if_false),
                );
            }
        }
    }

    fn then_else_break(&mut self, block: BasicBlockId, condition: ExprId) -> BlockAnd<()> {
        let then_block = self.new_block_with_note("then block".into());
        let else_block = self.new_block_with_note("else block".into());
        self.lower_condition(block, condition, then_block, else_block);
        self.break_for_else(else_block, self.thir.exprs[condition].span);
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
