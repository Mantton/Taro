//! Forwarding for async functions that only return another call's result.
//!
//! Closure adapters, witness thunks and wrappers such as
//! `func a(x: T) async -> U { return await b(x) }` have nothing to do between
//! calling and returning. Such a function's constructor can return the callee's
//! handle, sparing a frame, a root lease and one poll at every suspension.
//!
//! Skipping its frame moves what precedes the call from the first poll to the
//! constructor, and leaves nothing to run afterwards. So this applies only when
//! nothing can observe the difference:
//!
//! - Only values that can't change are read: those this call owns, and what a
//!   closure captured from an immutable binding. Reading anything else through a
//!   reference could see a later write, since a spawned task starts after its
//!   spawner continues.
//! - The callee is a compiled async function, whose constructor only stores its
//!   inputs. A runtime waitable's constructor can depend on the task running it.
//! - No cleanup runs on any exit, and the result is returned unconverted.
use super::*;

/// Replace `body` with a constructor that returns its callee's handle, when
/// that is unobservable. Otherwise `body` is left as it was.
pub(super) fn forward_tail_await<'ctx>(gcx: Gcx<'ctx>, body: &mut Body<'ctx>) -> bool {
    if body.escape_locals.iter().any(|escapes| *escapes) {
        return false;
    }
    let Some(call_block) = tail_await_call(gcx, body) else {
        return false;
    };
    let return_local = body.return_local;
    let span = body_span(body);
    let return_block = body.basic_blocks.push(BasicBlockData {
        note: Some("forwarded-await-ret".into()),
        statements: vec![],
        terminator: Some(Terminator {
            kind: TerminatorKind::Return,
            span,
        }),
    });
    let terminator = body.basic_blocks[call_block]
        .terminator
        .as_mut()
        .expect("recognized call block has a terminator");
    let TerminatorKind::Call {
        destination,
        target,
        ..
    } = &mut terminator.kind
    else {
        unreachable!("recognized call block ends in a call");
    };
    *destination = Place::from_local(return_local);
    *target = return_block;
    body.locals[return_local].ty = gcx.async_handle_ty();
    body.escape_locals = Vec::new();
    body.is_async = false;
    true
}

/// What the code before the call may read without the read's timing showing.
struct Readable<'a> {
    /// Locals holding this call's own values: parameters, then its temporaries.
    locals: FxHashSet<LocalId>,
    /// A closure's environment, with the fields capturing immutable bindings.
    environment: Option<(LocalId, &'a [FieldIndex])>,
}

impl Readable<'_> {
    fn place(&self, place: &Place<'_>) -> bool {
        if !self.locals.contains(&place.local) {
            return false;
        }
        let only_fields = |elems: &[PlaceElem<'_>]| {
            elems
                .iter()
                .all(|elem| matches!(elem, PlaceElem::Field(..)))
        };
        if only_fields(&place.projection) {
            return true;
        }
        if let (
            Some((environment, immutable)),
            [PlaceElem::Field(field, _), PlaceElem::Deref, rest @ ..],
        ) = (self.environment, place.projection.as_slice())
        {
            return place.local == environment && immutable.contains(field) && only_fields(rest);
        }
        false
    }

    fn operand(&self, operand: &Operand<'_>) -> bool {
        match operand {
            Operand::Copy(place) => self.place(place),
            Operand::CopyWith(..) => false,
            Operand::Constant(_) => true,
        }
    }

    fn rvalue(&self, value: &Rvalue<'_>) -> bool {
        match value {
            Rvalue::Use(operand) => self.operand(operand),
            Rvalue::CopyValue { source } => self.place(source),
            Rvalue::Aggregate { fields, .. } => fields.iter().all(|field| self.operand(field)),
            // Reborrowing a held reference copies it, without reading its target.
            Rvalue::Ref { place } => match place.projection.split_last() {
                Some((PlaceElem::Deref, prefix)) => {
                    self.locals.contains(&place.local)
                        && prefix
                            .iter()
                            .all(|elem| matches!(elem, PlaceElem::Field(..)))
                }
                _ => false,
            },
            _ => false,
        }
    }
}

fn tail_await_call<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> Option<BasicBlockId> {
    let params: Vec<LocalId> = body
        .locals
        .iter_enumerated()
        .filter_map(|(local, decl)| matches!(decl.kind, LocalKind::Param).then_some(local))
        .collect();
    let immutable_captures: Vec<FieldIndex> = gcx
        .get_closure_captures(body.owner)
        .map(|captures| {
            captures
                .captures
                .iter()
                .filter(|capture| capture.source_immutable)
                .map(|capture| capture.field_index)
                .collect()
        })
        .unwrap_or_default();
    let mut readable = Readable {
        locals: params.iter().copied().collect(),
        environment: params
            .first()
            .map(|env| (*env, immutable_captures.as_slice())),
    };
    let is_input = |local: LocalId| params.contains(&local) || local == body.return_local;

    // Everything before the call just prepares its arguments.
    let mut visited = FxHashSet::default();
    let mut block = body.start_block;
    let call_block = loop {
        if !visited.insert(block) {
            return None;
        }
        let data = &body.basic_blocks[block];
        for statement in &data.statements {
            match &statement.kind {
                StatementKind::Assign(place, value) => {
                    let whole = place.projection.is_empty();
                    let fields_only = place
                        .projection
                        .iter()
                        .all(|elem| matches!(elem, PlaceElem::Field(..)));
                    if is_input(place.local)
                        || !fields_only
                        || (whole && readable.locals.contains(&place.local))
                        || !readable.rvalue(value)
                    {
                        return None;
                    }
                    readable.locals.insert(place.local);
                }
                other if is_marker(other) => {}
                _ => return None,
            }
        }
        match &data.terminator.as_ref()?.kind {
            TerminatorKind::Goto { target } => block = *target,
            TerminatorKind::Call { .. } => break block,
            _ => return None,
        }
    };

    let TerminatorKind::Call {
        func,
        args,
        destination,
        target,
        unwind,
    } = &body.basic_blocks[call_block].terminator.as_ref()?.kind
    else {
        return None;
    };
    if !callee_has_pure_constructor(gcx, func, &readable)
        || !args.iter().all(|arg| readable.operand(arg))
        || !destination.projection.is_empty()
        || !unwinds_without_cleanup(body, *unwind)
    {
        return None;
    }

    // The awaited handle is the call's, and awaiting it is all that follows.
    let data = &body.basic_blocks[*target];
    if !data.statements.iter().all(|s| is_marker(&s.kind)) {
        return None;
    }
    let TerminatorKind::Yield {
        value,
        resume,
        resume_arg,
        no_result: None,
        cancel,
        cancel_complete,
        unwind,
    } = &data.terminator.as_ref()?.kind
    else {
        return None;
    };
    let handle = match value {
        Operand::Copy(place) => place,
        _ => return None,
    };
    // A void result has nothing to return, so it needn't reach the return local.
    let returns_result = resume_arg.local == body.return_local
        || (body.locals[body.return_local].ty == gcx.types.void
            && body.locals[resume_arg.local].ty == gcx.types.void);
    if handle != destination
        || !resume_arg.projection.is_empty()
        || !returns_result
        || !unwinds_without_cleanup(body, *unwind)
    {
        return None;
    }
    let ends_in = |start: BasicBlockId, end: fn(&TerminatorKind<'ctx>) -> bool| {
        let (last, kind) = follow_markers(body, start)?;
        end(kind).then_some(last)
    };
    ends_in(*resume, |kind| matches!(kind, TerminatorKind::Return))?;
    let cancelled = ends_in(*cancel, |kind| matches!(kind, TerminatorKind::Unreachable))?;
    (cancelled == *cancel_complete).then_some(call_block)
}

/// Walk blocks containing nothing observable, to the first real terminator.
fn follow_markers<'a, 'ctx>(
    body: &'a Body<'ctx>,
    start: BasicBlockId,
) -> Option<(BasicBlockId, &'a TerminatorKind<'ctx>)> {
    let mut visited = FxHashSet::default();
    let mut block = start;
    loop {
        if !visited.insert(block) {
            return None;
        }
        let data = &body.basic_blocks[block];
        if !data.statements.iter().all(|s| is_marker(&s.kind)) {
            return None;
        }
        let kind = &data.terminator.as_ref()?.kind;
        match kind {
            TerminatorKind::Goto { target } => block = *target,
            _ => return Some((block, kind)),
        }
    }
}

fn unwinds_without_cleanup(body: &Body<'_>, unwind: CallUnwindAction) -> bool {
    match unwind {
        CallUnwindAction::Terminate => true,
        CallUnwindAction::Cleanup(block) => follow_markers(body, block)
            .is_some_and(|(_, kind)| matches!(kind, TerminatorKind::ResumeUnwind)),
    }
}

fn is_marker(statement: &StatementKind<'_>) -> bool {
    matches!(
        statement,
        StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Nop
            | StatementKind::SourceScope(_)
            | StatementKind::SetInitialized(_)
    )
}

fn callee_has_pure_constructor<'ctx>(
    gcx: Gcx<'ctx>,
    func: &Operand<'ctx>,
    readable: &Readable<'_>,
) -> bool {
    match func {
        Operand::Constant(constant) => match constant.value {
            ConstantKind::Function(def_id, _, _) => {
                gcx.definition_is_async(def_id) && gcx.get_signature(def_id).abi.is_none()
            }
            _ => false,
        },
        // A closure or function value: source can only name compiled async code.
        operand => readable.operand(operand),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mir::test_support::{minimal_body, with_test_gcx};

    /// `async (env: T) -> T { let t = <value>; return await env(t) }`.
    fn wrapper<'ctx>(
        gcx: Gcx<'ctx>,
        value: impl FnOnce(LocalId) -> Rvalue<'ctx>,
    ) -> (Body<'ctx>, BasicBlockId) {
        let mut body = minimal_body(gcx);
        body.is_async = true;
        let span = body_span(&body);
        let int = gcx.types.int32;
        body.locals[body.return_local].ty = int;
        let parameter = push_local(&mut body, int, LocalKind::Param, false, None, span);
        let argument = push_local(&mut body, int, LocalKind::Temp, true, None, span);
        let handle = push_local(
            &mut body,
            gcx.async_handle_ty(),
            LocalKind::Temp,
            true,
            None,
            span,
        );
        let block = |statements, kind| BasicBlockData {
            note: None,
            statements,
            terminator: Some(Terminator { kind, span }),
        };
        let done = body
            .basic_blocks
            .push(block(vec![], TerminatorKind::Return));
        let cleanup = body
            .basic_blocks
            .push(block(vec![], TerminatorKind::ResumeUnwind));
        let cancelled = body
            .basic_blocks
            .push(block(vec![], TerminatorKind::Unreachable));
        let cancel = body.basic_blocks.push(block(
            vec![Statement {
                kind: StatementKind::StorageDead(parameter),
                span,
            }],
            TerminatorKind::Goto { target: cancelled },
        ));
        let await_block = body.basic_blocks.push(block(
            vec![],
            TerminatorKind::Yield {
                value: Operand::Copy(Place::from_local(handle)),
                resume: done,
                resume_arg: Place::from_local(body.return_local),
                no_result: None,
                cancel,
                cancel_complete: cancelled,
                unwind: CallUnwindAction::Cleanup(cleanup),
            },
        ));
        let entry = body.basic_blocks.push(block(
            vec![Statement {
                kind: StatementKind::Assign(Place::from_local(argument), value(parameter)),
                span,
            }],
            TerminatorKind::Call {
                func: Operand::Copy(Place::from_local(parameter)),
                args: vec![Operand::Copy(Place::from_local(argument))],
                destination: Place::from_local(handle),
                target: await_block,
                unwind: CallUnwindAction::Cleanup(cleanup),
            },
        ));
        body.start_block = entry;
        (body, await_block)
    }

    fn read<'ctx>(local: LocalId) -> Rvalue<'ctx> {
        Rvalue::Use(Operand::Copy(Place::from_local(local)))
    }

    #[test]
    fn a_plain_wrapper_returns_its_callees_handle() {
        with_test_gcx(|gcx| {
            let (mut body, _) = wrapper(gcx, read);
            assert!(forward_tail_await(gcx, &mut body));
            assert!(!body.is_async);
            assert_eq!(body.locals[body.return_local].ty, gcx.async_handle_ty());
            let call = &body.basic_blocks[body.start_block];
            let TerminatorKind::Call { destination, .. } = &call.terminator.as_ref().unwrap().kind
            else {
                panic!("the constructor still calls its callee");
            };
            assert_eq!(destination.local, body.return_local);
        });
    }

    #[test]
    fn a_void_wrapper_forwards_whatever_local_receives_its_result() {
        with_test_gcx(|gcx| {
            let (mut body, await_block) = wrapper(gcx, read);
            let span = body_span(&body);
            let void = gcx.types.void;
            body.locals[body.return_local].ty = void;
            let result = push_local(&mut body, void, LocalKind::Temp, true, None, span);
            let TerminatorKind::Yield { resume_arg, .. } = &mut body.basic_blocks[await_block]
                .terminator
                .as_mut()
                .unwrap()
                .kind
            else {
                panic!("wrapper awaits");
            };
            *resume_arg = Place::from_local(result);
            assert!(forward_tail_await(gcx, &mut body));
        });
    }

    #[test]
    fn reading_through_a_reference_keeps_the_frame() {
        // A later write would be visible to a read at first poll, but not to one
        // moved into the constructor.
        with_test_gcx(|gcx| {
            let (mut body, _) = wrapper(gcx, |parameter| {
                Rvalue::Use(Operand::Copy(Place {
                    local: parameter,
                    projection: vec![PlaceElem::Deref],
                }))
            });
            assert!(!forward_tail_await(gcx, &mut body));
            assert!(body.is_async);
        });
    }

    #[test]
    fn taking_a_locals_address_keeps_the_frame() {
        with_test_gcx(|gcx| {
            let (mut body, _) = wrapper(gcx, |parameter| Rvalue::Ref {
                place: Place::from_local(parameter),
            });
            assert!(!forward_tail_await(gcx, &mut body));
        });
    }

    #[test]
    fn work_after_the_await_keeps_the_frame() {
        with_test_gcx(|gcx| {
            let (mut body, await_block) = wrapper(gcx, read);
            let TerminatorKind::Yield { resume, .. } = body.basic_blocks[await_block]
                .terminator
                .as_ref()
                .unwrap()
                .kind
            else {
                panic!("wrapper awaits");
            };
            let span = body_span(&body);
            let value = Operand::Copy(Place::from_local(body.return_local));
            body.basic_blocks[resume].statements.push(Statement {
                kind: StatementKind::KeepAlive(value),
                span,
            });
            assert!(!forward_tail_await(gcx, &mut body));
        });
    }

    #[test]
    fn a_result_stored_elsewhere_keeps_the_frame() {
        with_test_gcx(|gcx| {
            let (mut body, await_block) = wrapper(gcx, read);
            let span = body_span(&body);
            let other = push_local(
                &mut body,
                gcx.types.int32,
                LocalKind::Temp,
                true,
                None,
                span,
            );
            let TerminatorKind::Yield { resume_arg, .. } = &mut body.basic_blocks[await_block]
                .terminator
                .as_mut()
                .unwrap()
                .kind
            else {
                panic!("wrapper awaits");
            };
            *resume_arg = Place::from_local(other);
            assert!(!forward_tail_await(gcx, &mut body));
        });
    }
}
