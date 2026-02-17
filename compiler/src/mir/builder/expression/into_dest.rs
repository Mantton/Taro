use crate::{
    compile::context::Gcx,
    mir::{
        self, AggregateKind, BasicBlockId, BinaryOperator, BlockAnd, BlockAndExtension, CastKind,
        Category, Constant, Operand, Place, PlaceElem, Rvalue, RvalueFunc, TerminatorKind,
        builder::MirBuilder,
    },
    sema::resolve::models::DefinitionKind,
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
                // Use Copy for copyable types, Move for non-copyable types
                let operand = if self.is_type_copyable(expr.ty) {
                    Operand::Copy(place)
                } else {
                    Operand::Move(place)
                };
                let rvalue = Rvalue::Use(operand);
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
                // Determine whether we need to pack variadic arguments.
                let mut variadic_split_idx = None;
                let callee_expr = &self.thir.exprs[*callee];
                let is_known_variadic = match callee_expr.kind {
                    ExprKind::Zst { id, .. } => self.gcx.get_signature(id).is_variadic,
                    _ => false,
                };

                // Use the callee type to detect variadic shape.
                let callee_ty = callee_expr.ty;

                let closure_self_param_ty =
                    if let crate::sema::models::TyKind::Closure { closure_def_id, .. } =
                        callee_ty.kind()
                    {
                        self.gcx
                            .get_signature(closure_def_id)
                            .inputs
                            .first()
                            .map(|param| param.ty)
                    } else if let crate::sema::models::TyKind::Parameter(_) = callee_ty.kind() {
                        // Check if this type parameter has Fn/FnMut/FnOnce bounds
                        if self.has_fn_trait_bound(callee_ty) {
                            // For callable type parameters, the self parameter is *const F
                            // (a pointer to the parameter type)
                            Some(self.gcx.store.interners.intern_ty(
                                crate::sema::models::TyKind::Pointer(
                                    callee_ty,
                                    crate::hir::Mutability::Immutable,
                                ),
                            ))
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                let function = if closure_self_param_ty.is_some()
                    && matches!(Category::of(&callee_expr.kind), Category::Place)
                {
                    let place = unpack!(block = self.as_place(block, *callee));
                    let by_ref = matches!(
                        closure_self_param_ty.unwrap().kind(),
                        crate::sema::models::TyKind::Pointer(..)
                            | crate::sema::models::TyKind::Reference(..)
                    );
                    if by_ref {
                        Operand::Copy(place)
                    } else {
                        Operand::Move(place)
                    }
                } else {
                    unpack!(block = self.as_local_operand(block, *callee))
                };

                // For closure calls, pass self according to the closure kind.
                let closure_self_arg: Option<Operand<'ctx>> =
                    closure_self_param_ty.and_then(|self_param_ty| match &function {
                        Operand::Copy(place) | Operand::Move(place) => {
                            let closure_place = place.clone();
                            match self_param_ty.kind() {
                                crate::sema::models::TyKind::Pointer(_, mutability)
                                | crate::sema::models::TyKind::Reference(_, mutability) => {
                                    let ptr_local = self.new_temp_with_ty(self_param_ty, expr.span);
                                    self.push_assign(
                                        block,
                                        Place::from_local(ptr_local),
                                        Rvalue::Ref {
                                            mutable: matches!(
                                                mutability,
                                                crate::hir::Mutability::Mutable
                                            ),
                                            place: closure_place,
                                        },
                                        expr.span,
                                    );
                                    Some(Operand::Copy(Place::from_local(ptr_local)))
                                }
                                _ => Some(Operand::Move(closure_place)),
                            }
                        }
                        Operand::Constant(_) => None,
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

                // Check if we're calling through a Fn bound and need to unpack tuple args.
                // This implements the "rust-call" ABI: when Args is a tuple like (T1, T2),
                // we pass individual arguments (self, t1, t2) instead of (self, (t1, t2)).
                let fn_trait_args_ty =
                    if let crate::sema::models::TyKind::Parameter(_) = callee_ty.kind() {
                        self.get_fn_trait_args_type(callee_ty)
                    } else {
                        None
                    };

                let (fixed_args, variadic_list_operand) = if let Some(split) = variadic_split_idx {
                    let (fixed, var_args) = args.split_at(split);
                    let inputs = if let crate::sema::models::TyKind::FnPointer { inputs, .. } =
                        callee_ty.kind()
                    {
                        inputs
                    } else {
                        panic!("callee must be fn pointer");
                    };
                    let list_ty = inputs[inputs.len() - 1];

                    // Extract element type T from List[T].
                    let elem_ty = if let crate::sema::models::TyKind::Adt(_, args) = list_ty.kind()
                    {
                        if let Some(crate::sema::models::GenericArgument::Type(ty)) = args.get(0) {
                            *ty
                        } else {
                            panic!("List must have generic arg");
                        }
                    } else {
                        panic!("Variadic param must be List");
                    };

                    let list_operand = unpack!(
                        block = self
                            .lower_variadic_sequence(block, var_args, list_ty, elem_ty, expr.span)
                    );

                    let fixed_operands: Vec<Operand<'ctx>> = fixed
                        .iter()
                        .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                        .collect();
                    (fixed_operands, Some(list_operand))
                } else if let Some(args_ty) = fn_trait_args_ty {
                    // Tuple-unpacking ABI for Fn trait calls.
                    // If Args is a tuple type, unpack the argument tuple into individual args.
                    if let crate::sema::models::TyKind::Tuple(elem_tys) = args_ty.kind() {
                        // Args is a tuple type - check if we have a single tuple argument to unpack
                        if args.len() == 1 {
                            let arg_expr = &self.thir.exprs[args[0]];
                            if let ExprKind::Tuple { fields } = &arg_expr.kind {
                                // Direct tuple literal - unpack its elements
                                let unpacked: Vec<Operand<'ctx>> = fields
                                    .iter()
                                    .map(|field| unpack!(block = self.as_operand(block, *field)))
                                    .collect();
                                (unpacked, None)
                            } else if matches!(
                                arg_expr.ty.kind(),
                                crate::sema::models::TyKind::Tuple(_)
                            ) {
                                // Tuple value (variable or expression) - extract elements
                                let tuple_place = unpack!(block = self.as_place(block, args[0]));
                                let unpacked: Vec<Operand<'ctx>> = elem_tys
                                    .iter()
                                    .enumerate()
                                    .map(|(i, &ty)| {
                                        let field_place = Place {
                                            local: tuple_place.local,
                                            projection: {
                                                let mut proj = tuple_place.projection.clone();
                                                proj.push(PlaceElem::Field(
                                                    FieldIndex::from_usize(i),
                                                    ty,
                                                ));
                                                proj
                                            },
                                        };
                                        if self.is_type_copyable(ty) {
                                            Operand::Copy(field_place)
                                        } else {
                                            Operand::Move(field_place)
                                        }
                                    })
                                    .collect();
                                (unpacked, None)
                            } else {
                                // Single non-tuple arg - pass as-is
                                let all_args = args
                                    .iter()
                                    .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                                    .collect();
                                (all_args, None)
                            }
                        } else {
                            // Multiple args provided directly - pass as-is
                            // This handles the case where user writes f(a, b) instead of f((a, b))
                            let all_args = args
                                .iter()
                                .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                                .collect();
                            (all_args, None)
                        }
                    } else {
                        // Args is not a tuple - pass as-is
                        let all_args = args
                            .iter()
                            .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                            .collect();
                        (all_args, None)
                    }
                } else {
                    let all_args = args
                        .iter()
                        .map(|arg| unpack!(block = self.as_operand(block, *arg)))
                        .collect();
                    (all_args, None)
                };

                // For closure calls, prepend self pointer to the argument list
                let mut final_args = Vec::new();
                if let Some(self_arg) = closure_self_arg {
                    final_args.push(self_arg);
                }
                final_args.extend(fixed_args);
                if let Some(list) = variadic_list_operand {
                    final_args.push(list);
                }

                let next = self.new_block();
                let unwind = self.call_unwind_for_callee(&function, expr.span);
                let terminator = TerminatorKind::Call {
                    func: function,
                    args: final_args,
                    destination,
                    target: next,
                    unwind,
                };
                self.terminate(block, expr.span, terminator);
                next.unit()
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
                        generic_args: adt_expression.generic_args,
                    },
                    fields,
                };
                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Deref(..) | ExprKind::Field { .. } | ExprKind::Upvar { .. } => {
                debug_assert!(matches!(Category::of(&expr.kind), Category::Place));
                let place = unpack!(block = self.as_place(block, expr_id));
                // Use Copy for copyable types, Move for non-copyable types
                let operand = if self.is_type_copyable(expr.ty) {
                    Operand::Copy(place)
                } else {
                    Operand::Move(place)
                };
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

                let rvalue = Rvalue::Aggregate {
                    kind: AggregateKind::Closure {
                        def_id: *def_id,
                        captured_generics: &[], // TODO: get from closure type
                    },
                    fields,
                };

                self.push_assign(block, destination, rvalue, expr.span);
                block.unit()
            }
            ExprKind::Tuple { .. }
            | ExprKind::Array { .. }
            | ExprKind::Repeat { .. }
            | ExprKind::Literal(..)
            | ExprKind::Unary { .. }
            | ExprKind::Binary { .. }
            | ExprKind::Cast { .. }
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
        self.apply_deref_vars(&mut var_places, &tree.deref_vars);

        let join_block = self.new_block_with_note("match-join".into());
        self.lower_match_decision(
            block,
            &tree.decision,
            &destination,
            join_block,
            &var_places,
            expr.span,
            &tree.deref_vars,
        );
        join_block.unit()
    }

    fn apply_deref_vars(
        &self,
        var_places: &mut FxHashMap<usize, Place<'ctx>>,
        deref_vars: &[thir::match_tree::DerefVar],
    ) {
        for deref_var in deref_vars {
            if var_places.contains_key(&deref_var.deref) {
                continue;
            }
            let Some(base_place) = var_places.get(&deref_var.base) else {
                continue;
            };
            let mut proj = base_place.projection.clone();
            proj.push(PlaceElem::Deref);
            var_places.insert(
                deref_var.deref,
                Place {
                    local: base_place.local,
                    projection: proj,
                },
            );
        }
    }

    fn lower_match_decision(
        &mut self,
        mut block: BasicBlockId,
        decision: &thir::match_tree::Decision<'ctx>,
        destination: &Place<'ctx>,
        join_block: BasicBlockId,
        var_places: &FxHashMap<usize, Place<'ctx>>,
        span: Span,
        deref_vars: &[thir::match_tree::DerefVar],
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
                    deref_vars,
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
                            deref_vars,
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
                        self.apply_deref_vars(&mut case_places, deref_vars);
                        self.lower_match_decision(
                            block,
                            &case.body,
                            destination,
                            join_block,
                            &case_places,
                            span,
                            deref_vars,
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
                            deref_vars,
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
                                    self.apply_deref_vars(&mut case_places, deref_vars);
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
                                deref_vars,
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
                                deref_vars,
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
        deref_vars: &[thir::match_tree::DerefVar],
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
                    deref_vars,
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
                deref_vars,
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
                deref_vars,
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

    fn lower_variadic_sequence(
        &mut self,
        mut block: BasicBlockId,
        args: &[ExprId],
        list_ty: crate::sema::models::Ty<'ctx>,
        elem_ty: crate::sema::models::Ty<'ctx>,
        span: Span,
    ) -> BlockAnd<Operand<'ctx>> {
        let count = args.len();
        let usize_ty = self.gcx.types.uint;

        let makebuf_id = self.find_function_in_std("mem", "__gc__makebuf", span);
        let desc_fn_id = self.find_function_in_std("intrinsic", "__intrinsic_gc_desc", span);
        let ptr_add_id = self.find_function_in_std("intrinsic", "__intrinsic_ptr_add", span);

        // 1. Call __intrinsic_gc_desc[T]().
        let generics = vec![crate::sema::models::GenericArgument::Type(elem_ty)];
        let generics = self.gcx.store.interners.intern_generic_args(generics);
        let desc_fn_ty = self.gcx.get_type(desc_fn_id);
        let desc_output = match desc_fn_ty.kind() {
            crate::sema::models::TyKind::FnPointer { output, .. } => output,
            _ => panic!("__intrinsic_gc_desc must be a function"),
        };
        let desc_func_op = Operand::Constant(Constant {
            ty: desc_fn_ty,
            value: mir::ConstantKind::Function(desc_fn_id, generics, desc_fn_ty),
        });

        let next_block = self.new_block();
        // `desc_output` is a raw pointer (*const GcDesc).
        let desc_dest = Place::from_local(self.new_temp_with_ty(desc_output, span));

        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: desc_func_op,
                args: vec![],
                destination: desc_dest.clone(),
                target: next_block,
                unwind: mir::CallUnwindAction::Terminate,
            },
        );
        block = next_block;

        // 2. Call __gc__makebuf(desc, count, count)
        let makebuf_fn_ty = self.gcx.get_type(makebuf_id);
        let makebuf_output = match makebuf_fn_ty.kind() {
            crate::sema::models::TyKind::FnPointer { output, .. } => output,
            _ => panic!("__gc__makebuf must be a function"),
        };

        let len_const = Operand::Constant(Constant {
            ty: usize_ty,
            value: mir::ConstantKind::Integer(count as u64),
        });

        let makebuf_generic_args = self.gcx.store.interners.intern_generic_args(vec![]);
        let makebuf_func = Operand::Constant(Constant {
            ty: makebuf_fn_ty,
            value: mir::ConstantKind::Function(makebuf_id, makebuf_generic_args, makebuf_fn_ty),
        });

        let buf_ptr_dest = Place::from_local(self.new_temp_with_ty(makebuf_output, span));
        let next_block_2 = self.new_block();
        let makebuf_unwind = self.call_unwind_action(span);

        self.terminate(
            block,
            span,
            TerminatorKind::Call {
                func: makebuf_func,
                args: vec![
                    Operand::Copy(desc_dest),
                    len_const.clone(),
                    len_const.clone(),
                ],
                destination: buf_ptr_dest.clone(),
                target: next_block_2,
                unwind: makebuf_unwind,
            },
        );
        block = next_block_2;

        // 3. Cast *mut u8 to *mut T.
        let ptr_t_ty = crate::sema::models::Ty::new(
            crate::sema::models::TyKind::Pointer(elem_ty, crate::hir::Mutability::Mutable),
            self.gcx,
        );
        let buf_ptr_t = self.new_temp_with_ty(ptr_t_ty, span);

        self.push_assign(
            block,
            Place::from_local(buf_ptr_t),
            Rvalue::Cast {
                kind: CastKind::Pointer,
                operand: Operand::Copy(buf_ptr_dest.clone()),
                ty: ptr_t_ty,
            },
            span,
        );

        // 4. Fill buffer.
        let ptr_add_generics = self
            .gcx
            .store
            .interners
            .intern_generic_args(vec![crate::sema::models::GenericArgument::Type(elem_ty)]);

        let ptr_add_ty = self.gcx.get_type(ptr_add_id);

        let ptr_add_func = Operand::Constant(Constant {
            ty: ptr_add_ty,
            value: mir::ConstantKind::Function(ptr_add_id, ptr_add_generics, ptr_add_ty),
        });

        for (i, arg_expr_id) in args.iter().enumerate() {
            let arg_operand = unpack!(block = self.as_operand(block, *arg_expr_id));

            let offset_ptr_place = if i == 0 {
                Place::from_local(buf_ptr_t)
            } else {
                let next_block_loop = self.new_block();
                let temp_ptr = self.new_temp_with_ty(ptr_t_ty, span);
                let idx_op = Operand::Constant(Constant {
                    ty: usize_ty,
                    value: mir::ConstantKind::Integer(i as u64),
                });

                self.terminate(
                    block,
                    span,
                    TerminatorKind::Call {
                        func: ptr_add_func.clone(),
                        args: vec![Operand::Copy(Place::from_local(buf_ptr_t)), idx_op],
                        destination: Place::from_local(temp_ptr),
                        target: next_block_loop,
                        unwind: mir::CallUnwindAction::Terminate,
                    },
                );
                block = next_block_loop;
                Place::from_local(temp_ptr)
            };

            let dest = Place {
                local: offset_ptr_place.local,
                projection: vec![PlaceElem::Deref],
            };
            self.push_assign(block, dest, Rvalue::Use(arg_operand), span);
        }

        // 5. Aggregate List { buffer, len, cap }.
        let fields = IndexVec::from_vec(vec![
            Operand::Copy(buf_ptr_dest),
            len_const.clone(),
            len_const.clone(),
        ]);

        let (list_def_id, generic_args) =
            if let crate::sema::models::TyKind::Adt(def, args) = list_ty.kind() {
                (def.id, args)
            } else {
                unreachable!()
            };

        let list_temp = self.new_temp_with_ty(list_ty, span);

        self.push_assign(
            block,
            Place::from_local(list_temp),
            Rvalue::Aggregate {
                kind: AggregateKind::Adt {
                    def_id: list_def_id,
                    variant_index: None,
                    generic_args,
                },
                fields,
            },
            span,
        );

        block.and(Operand::Move(Place::from_local(list_temp)))
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
            while let Some(parent) = output.definition_to_parent.get(&current).copied() {
                if parent == current {
                    break;
                }
                current = parent;
                if matches!(
                    output.definition_to_kind.get(&current),
                    Some(DefinitionKind::Module)
                ) {
                    if let Some(ident) = output.definition_to_ident.get(&current) {
                        if ident.symbol.as_str() == module {
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
            if ident.symbol.as_str() == name {
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

            let is_deref_place = src_place
                .projection
                .iter()
                .any(|p| matches!(p, PlaceElem::Deref));
            if matches!(binding.mode, crate::hir::BindingMode::ByValue) && is_deref_place {
                self.place_bindings.insert(binding.local, src_place.clone());
                continue;
            }

            // Generate the appropriate rvalue based on binding mode
            let rvalue = match binding.mode {
                crate::hir::BindingMode::ByValue => {
                    // Use Copy for copyable types, Move for non-copyable types
                    let operand = if self.is_type_copyable(binding.ty) {
                        Operand::Copy(src_place.clone())
                    } else {
                        Operand::Move(src_place.clone())
                    };
                    Rvalue::Use(operand)
                }
                crate::hir::BindingMode::ByRef(mutability) => {
                    // Take a reference to the place
                    Rvalue::Ref {
                        mutable: mutability == crate::hir::Mutability::Mutable,
                        place: src_place.clone(),
                    }
                }
            };

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
