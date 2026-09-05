use super::{BasicBlockId, CallUnwindAction, LocalId, Operand, Place, TerminatorKind};

fn block(index: usize) -> BasicBlockId {
    BasicBlockId::from_usize(index)
}

fn place() -> Place<'static> {
    Place::from_local(LocalId::from_usize(0))
}

#[test]
fn successors_preserve_switch_order_and_duplicate_edges() {
    let branch = TerminatorKind::SwitchInt {
        discr: Operand::Copy(place()),
        targets: vec![(1, block(2)), (2, block(1)), (3, block(2))],
        otherwise: block(3),
    };
    assert_eq!(
        branch.successors(),
        vec![block(2), block(1), block(2), block(3)]
    );
}

#[test]
fn successors_include_call_cleanup_but_not_termination() {
    for (unwind, expected) in [
        (CallUnwindAction::Terminate, vec![block(1)]),
        (
            CallUnwindAction::Cleanup(block(2)),
            vec![block(1), block(2)],
        ),
    ] {
        let call = TerminatorKind::Call {
            func: Operand::Copy(place()),
            args: Vec::new(),
            devirt_hint: None,
            destination: place(),
            target: block(1),
            unwind,
        };
        assert_eq!(call.successors(), expected);
    }
    assert_eq!(
        TerminatorKind::Goto { target: block(1) }.successors(),
        vec![block(1)]
    );
    for exit in [
        TerminatorKind::Return,
        TerminatorKind::ResumeUnwind,
        TerminatorKind::Unreachable,
        TerminatorKind::UnresolvedGoto,
    ] {
        assert!(exit.successors().is_empty());
    }
}

#[test]
fn successors_include_yield_cancellation_and_unwind_not_completion_marker() {
    for (unwind, expected) in [
        (CallUnwindAction::Terminate, vec![block(1), block(2)]),
        (
            CallUnwindAction::Cleanup(block(3)),
            vec![block(1), block(2), block(3)],
        ),
    ] {
        let suspend = TerminatorKind::Yield {
            value: Operand::Copy(place()),
            resume: block(1),
            resume_arg: place(),
            cancel: block(2),
            cancel_complete: block(4),
            unwind,
        };
        assert_eq!(suspend.successors(), expected);
    }
}
