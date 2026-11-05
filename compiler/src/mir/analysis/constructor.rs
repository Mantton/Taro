//! Private value-constructor storage and one-time readonly initialization.
//! The frontend creates this storage without a caller receiver parameter;
//! every successful exit returns a fully initialized value. Result errors
//! never expose the partial construction storage.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::Mutability,
    mir::{Body, LocalKind, Place, PlaceElem, Rvalue, StatementKind, TerminatorKind},
    sema::{
        models::{AdtKind, TyKind},
        tycheck::utils::normalize_aliases,
    },
};

/// Assignment privilege is limited to a directly named field, never to a
/// mutable borrow or to an immutable field nested inside another value.
pub fn readonly_field<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    place: &Place<'ctx>,
) -> Option<usize> {
    let local = &body.locals[place.local];
    if local.kind != LocalKind::ConstructorSelf || !local.mutable {
        return None;
    }
    let [PlaceElem::Field(index, _)] = place.projection.as_slice() else {
        return None;
    };
    let TyKind::Adt(def, _) = normalize_aliases(gcx, local.ty).kind() else {
        return None;
    };
    if def.kind != AdtKind::Struct {
        return None;
    }
    let definition = gcx.try_get_struct_definition(def.id)?;
    (definition.fields.get(index.index())?.mutability == Mutability::Immutable
        || (index.index() == 0
            && gcx
                .class_for_payload(local.ty)
                .is_some_and(|class| gcx.class_base(class).is_some())))
    .then_some(index.index())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        mir::{
            BasicBlockData, Constant, ConstantKind, LocalId, Operand, Rvalue, Statement,
            Terminator,
            test_support::{minimal_body, push_temp},
        },
        thir::FieldIndex,
    };

    fn owner<'ctx>(gcx: Gcx<'ctx>, ty: crate::sema::models::Ty<'ctx>) -> (Body<'ctx>, LocalId) {
        let mut body = minimal_body(gcx);
        let owner = push_temp(&mut body, ty);
        body.locals[owner].kind = LocalKind::ConstructorSelf;
        (body, owner)
    }
    fn store<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>, owner: LocalId) -> Statement<'ctx> {
        Statement {
            span: body.locals[owner].span,
            kind: StatementKind::Assign(
                Place {
                    local: owner,
                    projection: vec![PlaceElem::Field(FieldIndex::from_raw(0), gcx.types.int32)],
                },
                Rvalue::Use(Operand::Constant(Constant {
                    ty: gcx.types.int32,
                    value: ConstantKind::Integer(1),
                })),
            ),
        }
    }
    fn block<'ctx>(
        body: &mut Body<'ctx>,
        statements: Vec<Statement<'ctx>>,
        kind: TerminatorKind<'ctx>,
    ) -> crate::mir::BasicBlockId {
        let span = body.locals[body.return_local].span;
        body.basic_blocks.push(BasicBlockData {
            note: None,
            statements,
            terminator: Some(Terminator { span, kind }),
        })
    }

    #[test]
    fn readonly_constructor_fields_allow_one_write_but_never_mutable_borrowing() {
        crate::test_support::analyze_script(
            "struct Record { readonly value: int32 }\nfunc main() {}",
            |package, gcx| {
                let (mut body, owner) = owner(gcx, gcx.get_type(package.root.declarations[0].id));
                let first = store(gcx, &body, owner);
                let StatementKind::Assign(place, _) = &first.kind else {
                    unreachable!()
                };
                assert_eq!(readonly_field(gcx, &body, place), Some(0));
                assert!(!crate::mir::analysis::mutability::is_place_mutable(
                    gcx, &body, place
                ));
                body.basic_blocks[body.start_block]
                    .statements
                    .push(first.clone());
                assert!(validate(gcx, &body).is_ok());
                body.basic_blocks[body.start_block].statements.push(first);
                assert!(validate(gcx, &body).is_err());
            },
        );
    }

    #[test]
    fn one_initialized_branch_cannot_be_overwritten_after_the_join() {
        crate::test_support::analyze_script(
            "struct Record { readonly value: int32 }\nfunc main() {}",
            |package, gcx| {
                let (mut body, owner) = owner(gcx, gcx.get_type(package.root.declarations[0].id));
                let statement = store(gcx, &body, owner);
                let join = block(&mut body, vec![statement.clone()], TerminatorKind::Return);
                let left = block(
                    &mut body,
                    vec![statement],
                    TerminatorKind::Goto { target: join },
                );
                let right = block(&mut body, vec![], TerminatorKind::Goto { target: join });
                let span = body.locals[owner].span;
                body.basic_blocks[body.start_block].terminator = Some(Terminator {
                    span,
                    kind: TerminatorKind::SwitchInt {
                        discr: Operand::Constant(Constant {
                            ty: gcx.types.bool,
                            value: ConstantKind::Bool(true),
                        }),
                        targets: vec![(1, left)],
                        otherwise: right,
                    },
                });
                assert!(validate(gcx, &body).is_err());
            },
        );
    }

    #[test]
    fn g34_references_into_constructor_storage_are_rejected() {
        for expression in ["&self.value", "self.value.exposed()"] {
            let source = format!(
                "struct Record {{ value: int32 }}\nextend Record {{ init() {{ self.value = 1; save({expression}) }} }}\nfunc save(_ value: &int32) {{}}\ninterface Exposed {{ func exposed() -> &int32; }}\nconform &int32 to Exposed {{ func exposed() -> &int32 {{ self }}; }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir(&source, |bodies, gcx| {
                let mut constructors = 0;
                for body in bodies {
                    if body.locals[body.return_local].kind != LocalKind::ConstructorSelf {
                        continue;
                    }
                    constructors += 1;
                    assert!(validate(gcx, &body).is_err());
                }
                assert!(constructors > 0);
                assert!(
                    gcx.dcx()
                        .take_recorded_diagnostics()
                        .iter()
                        .any(|diagnostic| diagnostic
                            .message
                            .contains("cannot take references to self"))
                );
            });
        }
    }

    #[test]
    fn g34_constructor_can_reference_independent_storage() {
        for statements in [
            "self.value = pointer; self.other = &*self.value",
            "self.value = pointer; copied := self.value; self.other = &*copied",
        ] {
            let source = format!(
                "struct Record {{ value: &int32; other: &int32 }}\nextend Record {{ init(_ pointer: &int32) {{ {statements} }} }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir(&source, |bodies, gcx| {
                for body in bodies {
                    assert!(validate(gcx, &body).is_ok());
                }
            });
        }
    }

    #[test]
    fn g34_constructor_completion_follows_the_successful_body_exit() {
        for statements in [
            "self.first = 1; self.second = 2; checkpoint()",
            "self.first = 1; self.second = makeSecond()",
        ] {
            let source = format!(
                "extern \"C\" {{ func checkpoint(); func makeSecond() -> int32; }}\nstruct Record {{ first: int32; second: int32 }}\nextend Record {{ init() {{ {statements} }} }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir(&source, |bodies, gcx| {
                let mut checked = 0;
                for body in bodies {
                    if body.locals[body.return_local].kind != LocalKind::ConstructorSelf {
                        continue;
                    }
                    checked += 1;
                    let mut completions = 0;
                    for block in &body.basic_blocks {
                        for statement in &block.statements {
                            if matches!(statement.kind, StatementKind::SetInitialized(local) if local == body.return_local)
                            {
                                completions += 1;
                                assert!(
                                    block.terminator.as_ref().is_some_and(|terminator| matches!(
                                        terminator.kind,
                                        TerminatorKind::Return
                                    )),
                                    "completion must follow all possibly panicking calls: {statements}"
                                );
                            }
                        }
                    }
                    assert_eq!(completions, 1, "a successful constructor completes once");
                    assert!(super::validate(gcx, &body).is_ok());
                }
                assert!(checked > 0);
            });
        }
    }

    #[test]
    fn complete_field_sets_publish_on_return_and_missing_fields_do_not() {
        crate::test_support::analyze_script(
            "struct Record { readonly value: int32; other: int32 }\nfunc main() {}",
            |package, gcx| {
                let (mut body, owner) = owner(gcx, gcx.get_type(package.root.declarations[0].id));
                let first = store(gcx, &body, owner);
                body.basic_blocks[body.start_block]
                    .statements
                    .push(first.clone());
                complete(gcx, &mut body);
                let markers = |body: &Body<'_>| {
                    body.basic_blocks.iter().flat_map(|block| &block.statements)
                .filter(|statement| matches!(statement.kind, StatementKind::SetInitialized(local) if local == owner)).count()
                };
                assert_eq!(
                    markers(&body),
                    0,
                    "the unmentioned second field is still uninitialized"
                );
                let mut second = first;
                let StatementKind::Assign(place, _) = &mut second.kind else {
                    unreachable!()
                };
                place.projection = vec![PlaceElem::Field(FieldIndex::from_raw(1), gcx.types.int32)];
                body.basic_blocks[body.start_block].statements.push(second);
                complete(gcx, &mut body);
                assert_eq!(markers(&body), 1);
                complete(gcx, &mut body);
                assert_eq!(
                    markers(&body),
                    1,
                    "revisiting canonical initializer storage is idempotent"
                );
            },
        );
    }

    #[test]
    fn loops_require_a_new_storage_lifetime_before_reinitializing_readonly_fields() {
        for fresh in [false, true] {
            crate::test_support::analyze_script(
                "struct Record { readonly value: int32 }\nfunc main() {}",
                |package, gcx| {
                    let (mut body, owner) =
                        owner(gcx, gcx.get_type(package.root.declarations[0].id));
                    let mut statements = vec![];
                    if fresh {
                        statements.push(Statement {
                            span: body.locals[owner].span,
                            kind: StatementKind::StorageLive(owner),
                        });
                    }
                    statements.push(store(gcx, &body, owner));
                    let entry = body.start_block;
                    let cycle = block(
                        &mut body,
                        statements,
                        TerminatorKind::Goto { target: entry },
                    );
                    let span = body.locals[owner].span;
                    body.basic_blocks[entry].terminator = Some(Terminator {
                        span,
                        kind: TerminatorKind::Goto { target: cycle },
                    });
                    assert_eq!(validate(gcx, &body).is_ok(), fresh);
                },
            );
        }
    }
}

fn destination<'a, 'ctx>(statement: &'a StatementKind<'ctx>) -> Option<&'a Place<'ctx>> {
    match statement {
        StatementKind::Assign(place, _) => Some(place),

        _ => None,
    }
}

/// May-written bits union at joins: a write is forbidden if *any* incoming
/// path previously initialized that readonly field. An ordinary must-init
/// analysis cannot prove this rule at a partially initialized branch join.
pub fn validate<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    // Constructor storage is a private value until initialization returns.
    // Explicit references, receiver autoref and reference captures all reach
    // this check as Ref. Dereferencing a stored reference selects independent
    // storage and does not take the address of a constructor field.
    if body.phase != crate::mir::MirPhase::Lowered {
        for block in &body.basic_blocks {
            for statement in &block.statements {
                if let StatementKind::Assign(_, Rvalue::Ref { place }) = &statement.kind
                    && body.locals[place.local].kind == LocalKind::ConstructorSelf
                    && !place.projection.contains(&PlaceElem::Deref)
                {
                    gcx.dcx().emit_error(
                        "cannot take references to self or its fields during initialization".into(),
                        Some(statement.span),
                    );
                }
            }
        }
        gcx.dcx().ok()?;
    }
    let slots: Vec<_> = body
        .locals
        .iter_enumerated()
        .filter_map(|(local, declaration)| {
            if declaration.kind != LocalKind::ConstructorSelf {
                return None;
            }
            let TyKind::Adt(def, _) = normalize_aliases(gcx, declaration.ty).kind() else {
                return None;
            };
            if def.kind != AdtKind::Struct {
                return None;
            }
            Some(
                gcx.get_struct_definition(def.id)
                    .fields
                    .iter()
                    .enumerate()
                    .filter(|(index, field)| {
                        field.mutability == Mutability::Immutable
                            || (*index == 0
                                && gcx
                                    .class_for_payload(declaration.ty)
                                    .is_some_and(|class| gcx.class_base(class).is_some()))
                    })
                    .map(|(index, _)| (local, index))
                    .collect::<Vec<_>>(),
            )
        })
        .flatten()
        .collect();
    if slots.is_empty() {
        return Ok(());
    }
    let write = |state: &mut Vec<bool>, place: &Place<'ctx>| {
        for (slot, &(local, field)) in slots.iter().enumerate() {
            if place.local == local
                && (place.projection.is_empty()
                    || matches!(place.projection.first(), Some(PlaceElem::Field(index, _)) if index.index() == field))
            {
                state[slot] = true;
            }
        }
    };
    let transfer = |state: &mut Vec<bool>, statement: &StatementKind<'ctx>| {
        if let StatementKind::StorageLive(local) | StatementKind::StorageDead(local) = statement {
            for (slot, &(owner, _)) in slots.iter().enumerate() {
                if owner == *local {
                    state[slot] = false;
                }
            }
        } else if let Some(place) = destination(statement) {
            write(state, place);
        }
    };
    let mut incoming = vec![None; body.basic_blocks.len()];
    incoming[body.start_block.index()] = Some(vec![false; slots.len()]);
    let mut pending = vec![body.start_block];
    while let Some(block) = pending.pop() {
        let mut state = incoming[block.index()].clone().unwrap();
        for statement in &body.basic_blocks[block].statements {
            transfer(&mut state, &statement.kind);
        }
        let Some(terminator) = &body.basic_blocks[block].terminator else {
            continue;
        };
        for successor in terminator.kind.successors() {
            let mut edge = state.clone();
            if let TerminatorKind::Call {
                destination,
                target,
                ..
            } = &terminator.kind
                && successor == *target
            {
                write(&mut edge, destination);
            }
            let changed = match &mut incoming[successor.index()] {
                None => {
                    incoming[successor.index()] = Some(edge);
                    true
                }
                Some(existing) => {
                    let mut changed = false;
                    for (old, new) in existing.iter_mut().zip(edge) {
                        changed |= !*old && new;
                        *old |= new;
                    }
                    changed
                }
            };
            if changed && !pending.contains(&successor) {
                pending.push(successor);
            }
        }
    }
    let check = |state: &[bool], place: &Place<'ctx>, span| {
        if let Some(field) = readonly_field(gcx, body, place)
            && slots.iter().enumerate().any(|(slot, &(local, index))| {
                local == place.local && index == field && state[slot]
            })
        {
            let base = field == 0
                && gcx
                    .class_for_payload(body.locals[place.local].ty)
                    .is_some_and(|class| gcx.class_base(class).is_some());
            gcx.dcx().emit_error(
                if base {
                    "super.init may initialize the base only once"
                } else {
                    "a readonly field can only be initialized once"
                }
                .into(),
                Some(span),
            );
        }
    };
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(mut state) = incoming[block.index()].clone() else {
            continue;
        };
        for statement in &data.statements {
            if let Some(place) = destination(&statement.kind) {
                check(&state, place, statement.span);
            }
            transfer(&mut state, &statement.kind);
        }
        if let Some(terminator) = &data.terminator
            && let TerminatorKind::Call { destination, .. } = &terminator.kind
        {
            check(&state, destination, terminator.span);
        }
    }
    gcx.dcx().ok()
}

/// Construction completes after its body and defers return normally.
/// Field-sensitive analysis proves intermediate accesses; zero-safe GC roots
/// protect partial storage. There is no destructor cleanup to arm early.
pub fn complete<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) {
    let owners: Vec<_> = body
        .locals
        .iter_enumerated()
        .filter_map(|(local, declaration)| {
            (declaration.kind == LocalKind::ConstructorSelf).then_some(local)
        })
        .collect();
    if owners.is_empty() {
        return;
    }
    let analysis = super::initialization::Initialization::compute(gcx, body);
    for block in body.basic_blocks.indices().collect::<Vec<_>>() {
        let data = &body.basic_blocks[block];
        let Some(terminator) = &data.terminator else {
            continue;
        };
        if !matches!(terminator.kind, TerminatorKind::Return) {
            continue;
        }
        let Some(mut state) = analysis.incoming[block.index()].clone() else {
            continue;
        };
        for statement in &data.statements {
            analysis
                .paths
                .transfer_statement(&mut state, &statement.kind);
        }
        let span = terminator.span;
        let completed: Vec<_> = owners.iter().copied().filter(|owner| {
            analysis.paths.construction_ready(&state, analysis.paths.root(*owner))
                && !data.statements.iter().any(|statement| {
                    matches!(statement.kind, StatementKind::SetInitialized(existing) if existing == *owner)
                })
        }).collect();
        for owner in completed {
            body.basic_blocks[block]
                .statements
                .push(crate::mir::Statement {
                    kind: StatementKind::SetInitialized(owner),
                    span,
                });
        }
    }
}
