//! A partially initialized class has payload storage, but no public receiver
//! handle to publish. Field operations remain available; whole-self
//! access is forbidden even when a generic helper could accept the payload.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    mir::{
        Body, LocalId, LocalKind, MirPhase, Operand, Place, PlaceElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    sema::models::SyntheticDefinitionKind,
};

pub fn validate<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    if body.phase == MirPhase::Lowered {
        return Ok(());
    }
    let convenience = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&body.owner)
        .is_some_and(|definition| {
            matches!(
                definition.kind,
                SyntheticDefinitionKind::ClassConvenienceInitializer { .. }
            )
        });
    if convenience {
        return validate_convenience_delegation(gcx, body);
    }
    let payload_initializer = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&body.owner)
        .is_some_and(|definition| {
            matches!(
                definition.kind,
                SyntheticDefinitionKind::ClassPayloadInitializer { .. }
            )
        });
    if !payload_initializer {
        return Ok(());
    }
    let generated_decoder = gcx
        .store
        .synthetic_definitions
        .borrow()
        .get(&body.owner)
        .and_then(|definition| match definition.kind {
            SyntheticDefinitionKind::ClassPayloadInitializer { initializer, .. } => {
                Some(initializer)
            }
            _ => None,
        })
        .is_some_and(|initializer| {
            matches!(
                gcx.store
                    .synthetic_definitions
                    .borrow()
                    .get(&initializer)
                    .map(|value| value.kind),
                Some(SyntheticDefinitionKind::ClassDecodingInitializer { .. })
            )
        });
    // A derived decoder constructs a complete aggregate from decoded locals;
    // it has no partial self place. Ordinary MIR initialization checks apply.
    if generated_decoder {
        return Ok(());
    }
    let Some(root) = body
        .locals
        .iter_enumerated()
        .find_map(|(id, local)| (local.kind == LocalKind::ConstructorSelf).then_some(id))
    else {
        gcx.dcx().emit_error(
            "class payload initializer requires private construction storage".into(),
            None,
        );
        return gcx.dcx().ok();
    };
    if gcx
        .class_for_payload(body.locals[root].ty)
        .is_some_and(|class| gcx.class_base(class).is_some())
    {
        validate_base_first(gcx, body, root);
    }
    let whole = |place: &Place<'_>| place.local == root && place.projection.is_empty();
    let report = |span| {
        gcx.dcx().emit_error("cannot copy, capture, pass, or replace self during class initialization; access its fields instead".into(), Some(span))
    };
    let operand = |value: &Operand<'_>, span| {
        if value.place().is_some_and(&whole) {
            report(span);
        }
    };
    let rvalue = |value: &Rvalue<'_>, span| {
        if matches!(
            value,
            Rvalue::Cast {
                kind: crate::mir::CastKind::ClassObjectOwner,
                ..
            }
        ) {
            return;
        }
        value.for_each_operand(|value| operand(value, span));
        match value {
            Rvalue::Ref { place, .. } | Rvalue::CopyValue { source: place } if whole(place) => {
                report(span)
            }
            _ => {}
        }
    };
    for block in &body.basic_blocks {
        for statement in &block.statements {
            let destination = match &statement.kind {
                StatementKind::Assign(destination, value) => {
                    rvalue(value, statement.span);
                    Some(destination)
                }

                _ => None,
            };
            if destination.is_some_and(&whole) {
                report(statement.span);
            }
        }
        if let Some(terminator) = &block.terminator {
            match &terminator.kind {
                TerminatorKind::Call {
                    func,
                    args,
                    destination,
                    ..
                } => {
                    operand(func, terminator.span);
                    for argument in args {
                        operand(argument, terminator.span);
                    }
                    if whole(destination) {
                        report(terminator.span);
                    }
                }
                TerminatorKind::SwitchInt { discr, .. } => operand(discr, terminator.span),
                _ => {}
            }
        }
    }
    gcx.dcx().ok()
}

/// Defaults and explicit field operations require a successfully completed
/// base level on every incoming path. A call initializes the prefix only on
/// its normal edge; unwinding never marks it complete.
fn validate_base_first<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>, root: LocalId) {
    let analysis = super::initialization::Initialization::compute(gcx, body);
    let Some(&base) = analysis.paths.children(analysis.paths.root(root)).first() else {
        return;
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(mut state) = analysis.incoming[block.index()].clone() else {
            continue;
        };
        let check = |place: &Place<'_>, initialized: bool, base_destination: bool, span| {
            if initialized || place.local != root || place.projection.is_empty() {
                return;
            }
            if base_destination
                && matches!(place.projection.as_slice(), [PlaceElem::Field(index, _)] if index.index() == 0)
            {
                return;
            }
            gcx.dcx().emit_error(
                "initialize the base with super.init before accessing self fields".into(),
                Some(span),
            );
        };
        for statement in &data.statements {
            let initialized = state.is_initialized(base);
            match &statement.kind {
                StatementKind::Assign(destination, value) => {
                    check(destination, initialized, true, statement.span);
                    value.for_each_place(|place| check(place, initialized, false, statement.span));
                }

                _ => {}
            }
            analysis
                .paths
                .transfer_statement(&mut state, &statement.kind);
        }
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call {
                args, destination, ..
            } = &terminator.kind
        {
            check(
                destination,
                state.is_initialized(base),
                true,
                terminator.span,
            );
            for argument in args {
                if let Some(place) = argument.place() {
                    check(place, state.is_initialized(base), false, terminator.span);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        mir::{
            Rvalue, Statement,
            test_support::{minimal_body, push_temp},
        },
        sema::models::SyntheticDefinition,
        thir::FieldIndex,
    };

    #[test]
    fn construction_policy_checks_owned_and_borrowed_whole_self_operations() {
        crate::test_support::analyze_script(
            "struct Record { value: int32 }\nfunc main() {}",
            |package, gcx| {
                let class = package.root.declarations[0].id;
                let ty = gcx.get_type(class);
                for borrowing in [false, true] {
                    let mut body = minimal_body(gcx);
                    body.locals[body.return_local].ty = ty;
                    body.locals[body.return_local].kind = LocalKind::ConstructorSelf;
                    body.owner = package.root.declarations[1].id;
                    let signature = gcx.get_signature(body.owner);
                    let id = gcx.allocate_synthetic_id(gcx.package_index());
                    gcx.register_synthetic_definition(
                        id,
                        SyntheticDefinition {
                            kind: SyntheticDefinitionKind::ClassPayloadInitializer {
                                class,
                                initializer: body.owner,
                            },
                            name: gcx.intern_symbol("test$classInit"),
                            generics: gcx.generics_of(body.owner),
                            signature,
                            span: body.locals[body.return_local].span,
                        },
                    );
                    body.owner = id;
                    let temp_ty = if borrowing {
                        crate::sema::models::Ty::new(
                            crate::sema::models::TyKind::Reference(ty),
                            gcx,
                        )
                    } else {
                        ty
                    };
                    let temp = push_temp(&mut body, temp_ty);
                    let field = Place {
                        local: body.return_local,
                        projection: vec![PlaceElem::Field(
                            FieldIndex::from_raw(0),
                            gcx.types.int32,
                        )],
                    };
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            kind: StatementKind::Assign(
                                field,
                                Rvalue::Use(Operand::Constant(crate::mir::Constant {
                                    ty: gcx.types.int32,
                                    value: crate::mir::ConstantKind::Integer(1),
                                })),
                            ),
                            span: body.locals[temp].span,
                        });
                    if !borrowing {
                        assert!(
                            validate(gcx, &body).is_ok(),
                            "direct field initialization remains valid"
                        );
                    }
                    let value = if borrowing {
                        Rvalue::Ref {
                            place: Place::return_place(),
                        }
                    } else {
                        Rvalue::Use(Operand::Copy(Place::return_place()))
                    };
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            kind: StatementKind::Assign(Place::from_local(temp), value),
                            span: body.locals[temp].span,
                        });
                    assert!(
                        validate(gcx, &body).is_err(),
                        "owned MIR must not bypass initialization restrictions"
                    );
                    gcx.dcx().take_recorded_diagnostics();
                }
            },
        );
    }
    #[test]
    fn class_level_completion_waits_for_the_final_normal_return() {
        for (fields, initialized) in [
            ("value: int32", true),
            ("value: int32; other: int32", false),
            ("", true),
        ] {
            let source = format!("struct Record {{ {fields} }}\nfunc main() {{}}");
            crate::test_support::analyze_script(&source, |package, gcx| {
                let mut body = minimal_body(gcx);
                body.owner = package.root.declarations[1].id;
                body.locals[body.return_local].ty = gcx.get_type(package.root.declarations[0].id);
                body.locals[body.return_local].kind = LocalKind::ConstructorSelf;
                let span = body.locals[body.return_local].span;
                let id = gcx.allocate_synthetic_id(gcx.package_index());
                gcx.register_synthetic_definition(
                    id,
                    SyntheticDefinition {
                        kind: SyntheticDefinitionKind::ClassPayloadInitializer {
                            class: package.root.declarations[0].id,
                            initializer: body.owner,
                        },
                        name: gcx.intern_symbol("test$classLevel"),
                        generics: gcx.generics_of(body.owner),
                        signature: gcx.get_signature(body.owner),
                        span,
                    },
                );
                body.owner = id;
                if !fields.is_empty() {
                    body.basic_blocks[body.start_block]
                        .statements
                        .push(Statement {
                            kind: StatementKind::Assign(
                                Place {
                                    local: body.return_local,
                                    projection: vec![PlaceElem::Field(
                                        FieldIndex::from_raw(0),
                                        gcx.types.int32,
                                    )],
                                },
                                Rvalue::Use(Operand::Constant(crate::mir::Constant {
                                    ty: gcx.types.int32,
                                    value: crate::mir::ConstantKind::Integer(1),
                                })),
                            ),
                            span,
                        });
                }
                let normal = body.basic_blocks.push(crate::mir::BasicBlockData {
                    note: None,
                    statements: vec![],
                    terminator: Some(crate::mir::Terminator {
                        kind: TerminatorKind::Return,
                        span,
                    }),
                });
                let failure = body.basic_blocks.push(crate::mir::BasicBlockData {
                    note: None,
                    statements: vec![],
                    terminator: Some(crate::mir::Terminator {
                        kind: TerminatorKind::ResumeUnwind,
                        span,
                    }),
                });
                body.basic_blocks[body.start_block].terminator = Some(crate::mir::Terminator {
                    span,
                    kind: TerminatorKind::SwitchInt {
                        discr: Operand::Constant(crate::mir::Constant {
                            ty: gcx.types.bool,
                            value: crate::mir::ConstantKind::Bool(true),
                        }),
                        targets: vec![(1, normal)],
                        otherwise: failure,
                    },
                });
                crate::mir::analysis::constructor::complete(gcx, &mut body);
                let markers = |block: crate::mir::BasicBlockId| {
                    body.basic_blocks[block].statements.iter().filter(|statement| matches!(statement.kind, StatementKind::SetInitialized(local) if local == body.return_local)).count()
                };
                assert_eq!(
                    markers(body.start_block),
                    0,
                    "filling fields does not complete a class level"
                );
                assert_eq!(markers(failure), 0, "failure skips this level's hook");
                assert_eq!(
                    markers(normal),
                    usize::from(initialized),
                    "only a complete final return arms the level"
                );
            });
        }
    }
}

/// A delegation initializes self only on its normal edge. Joining paths keeps
/// both possible counts; loops cannot turn a second delegation into assignment.
/// A Result error may exit before delegation. Its successful implicit return
/// reads self, so ordinary definite-initialization still requires delegation.
fn validate_convenience_delegation(gcx: Gcx<'_>, body: &Body<'_>) -> CompileResult<()> {
    let delegation = |terminator: &TerminatorKind<'_>| match terminator {
        TerminatorKind::Call {
            func: Operand::Constant(constant),
            ..
        } => match constant.value {
            crate::mir::ConstantKind::Function(id, ..) => gcx
                .store
                .synthetic_definitions
                .borrow()
                .get(&id)
                .is_some_and(|definition| {
                    matches!(
                        definition.kind,
                        SyntheticDefinitionKind::ClassInitializerDispatch { .. }
                            | SyntheticDefinitionKind::ClassConvenienceInitializer { .. }
                    )
                }),
            _ => false,
        },
        _ => false,
    };
    let mut incoming = vec![0u8; body.basic_blocks.len()];
    incoming[body.start_block.index()] = 1;
    let mut queue = std::collections::VecDeque::from([body.start_block]);
    while let Some(block) = queue.pop_front() {
        let state = incoming[block.index()];
        let Some(terminator) = &body.basic_blocks[block].terminator else {
            continue;
        };
        for successor in terminator.kind.successors() {
            let normal_delegation = delegation(&terminator.kind)
                && matches!(terminator.kind, TerminatorKind::Call { target, .. } if target == successor);
            let next = if normal_delegation {
                (if state & 1 != 0 { 2 } else { 0 }) | (if state & 6 != 0 { 4 } else { 0 })
            } else {
                state
            };
            let old = incoming[successor.index()];
            incoming[successor.index()] |= next;
            if incoming[successor.index()] != old {
                queue.push_back(successor);
            }
        }
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let state = incoming[block.index()];
        let Some(terminator) = &data.terminator else {
            continue;
        };
        if state == 0 {
            continue;
        }
        if delegation(&terminator.kind) && state & 6 != 0 {
            gcx.dcx().emit_error(
                "convenience initializer must delegate only once".into(),
                Some(terminator.span),
            );
        }
        if matches!(terminator.kind, TerminatorKind::Return)
            && state != 2
            && gcx
                .result_parts(gcx.get_signature(body.owner).output)
                .is_none()
        {
            gcx.dcx().emit_error(
                "convenience initializer must delegate with self.init on every returning path"
                    .into(),
                Some(terminator.span),
            );
        }
    }
    gcx.dcx().ok()
}
