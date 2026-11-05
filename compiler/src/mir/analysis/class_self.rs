//! An owned `Self` result in an inheritable class promises the receiver's
//! dynamic class, not merely its statically declared base. Prove that promise
//! on source MIR, before virtual dispatch or ownership lowering obscures it.
//! The analysis tracks handle identity, immutable constructor descriptors and
//! aliases to local handle slots. Unknown calls may replace referenced slots;
//! ordinary class receivers copy the object handle. Joins retain only facts
//! true on every reachable incoming edge.
use crate::{
    compile::context::Gcx,
    error::CompileResult,
    hir::DefinitionKind,
    mir::{
        Body, ConstantKind, LocalId, MirPhase, Operand, Place, PlaceElem, Rvalue, StatementKind,
        TerminatorKind,
    },
    sema::{
        models::{SyntheticDefinitionKind, Ty, TyKind},
        tycheck::utils::{instantiate::instantiate_ty_with_args, normalize_aliases},
    },
};
use std::collections::VecDeque;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Origin {
    Unknown,
    Handle,
    ReceiverSlot,
    Descriptor,
    FutureHandle,
    Alias(LocalId),
}
type State = Vec<Origin>;

fn read(state: &State, place: &Place<'_>) -> Origin {
    let mut value = state[place.local.index()];
    for projection in &place.projection {
        value = match (projection, value) {
            (PlaceElem::Deref, Origin::ReceiverSlot) => Origin::Handle,
            (PlaceElem::Deref, Origin::Alias(local)) => state[local.index()],
            _ => Origin::Unknown,
        };
    }
    value
}
fn operand(state: &State, value: &Operand<'_>) -> Origin {
    value
        .place()
        .map(|place| read(state, place))
        .unwrap_or(Origin::Unknown)
}
fn borrow(state: &State, place: &Place<'_>) -> Origin {
    if place.projection.is_empty() {
        return Origin::Alias(place.local);
    }
    if place.projection == [PlaceElem::Deref] {
        return match state[place.local.index()] {
            Origin::ReceiverSlot => Origin::ReceiverSlot,
            Origin::Alias(local) => Origin::Alias(local),
            _ => Origin::Unknown,
        };
    }
    Origin::Unknown
}
fn write(state: &mut State, place: &Place<'_>, value: Origin) {
    if place.projection.is_empty() {
        state[place.local.index()] = value;
    } else if place.projection == [PlaceElem::Deref]
        && let Origin::Alias(local) = state[place.local.index()]
    {
        state[local.index()] = value;
    } else {
        // Storing a reference in projected/opaque aggregate storage loses its
        // precise alias path, so no receiver-type proof may survive through it.
        invalidate(state, value);
    }
}
fn invalidate(state: &mut State, origin: Origin) {
    let mut current = origin;
    for _ in 0..state.len() {
        let Origin::Alias(local) = current else {
            break;
        };
        current = std::mem::replace(&mut state[local.index()], Origin::Unknown);
    }
}
fn rvalue(state: &mut State, value: &Rvalue<'_>) -> Origin {
    match value {
        Rvalue::Use(value) | Rvalue::Cast { operand: value, .. } => operand(state, value),
        Rvalue::CopyValue { source } => read(state, source),
        Rvalue::Ref { place } => borrow(state, place),
        Rvalue::Aggregate { fields, .. } => {
            for field in fields {
                invalidate(state, operand(state, field));
            }
            Origin::Unknown
        }
        _ => Origin::Unknown,
    }
}
fn statement(state: &mut State, statement: &StatementKind<'_>) {
    match statement {
        StatementKind::Assign(destination, value) => {
            let value = rvalue(state, value);
            write(state, destination, value);
        }

        StatementKind::StorageLive(local) | StatementKind::StorageDead(local) => {
            state[local.index()] = Origin::Unknown;
        }
        _ => {}
    }
}

fn call<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    state: &mut State,
    function: &Operand<'ctx>,
    args: &[Operand<'ctx>],
    conditional_self: Option<Ty<'ctx>>,
) -> Origin {
    let constant = match function {
        Operand::Constant(constant) => Some(constant),
        _ => None,
    };
    let target = constant.and_then(|constant| match constant.value {
        ConstantKind::Function(id, arguments, _) => Some((id, arguments)),
        _ => None,
    });
    let mut result = Origin::Unknown;
    let mut receiver_contract = false;
    if let Some((id, arguments)) = target {
        let kind = gcx
            .store
            .synthetic_definitions
            .borrow()
            .get(&id)
            .map(|entry| entry.kind);
        match kind {
            Some(SyntheticDefinitionKind::ClassObjectDescriptor { .. })
                if args
                    .first()
                    .is_some_and(|arg| operand(state, arg) == Origin::Handle) =>
            {
                result = Origin::Descriptor;
            }
            Some(SyntheticDefinitionKind::ClassInitializerDispatch { initializer })
                if args
                    .first()
                    .is_some_and(|arg| operand(state, arg) == Origin::Descriptor)
                    && gcx
                        .class_initializer(gcx.get_signature(initializer).output, initializer)
                        .is_some_and(|entry| entry.is_required) =>
            {
                result = Origin::Handle;
            }
            _ => {}
        }
        let signature = gcx.get_signature(id);
        if let Some(input) = signature.inputs.first()
            && input.name.as_str() == "self"
        {
            let ty = instantiate_ty_with_args(gcx, input.ty, arguments);
            let class = match normalize_aliases(gcx, ty).kind() {
                TyKind::Reference(class) => class,
                _ => ty,
            };
            receiver_contract = gcx
                .definition_parent(id)
                .and_then(|parent| gcx.get_impl_target_ty(parent))
                .is_some_and(|owner| gcx.is_class_type(owner));
            if let Some(source) = gcx.class_default_source(id) {
                // An exact-body alias skips witness selection. Its checked
                // conditional promise, rather than its synthetic parent,
                // authorizes forwarding the actual receiver's dynamic class.
                receiver_contract = gcx
                    .class_default_contract(source)
                    .is_some_and(|proof| proof.preserves_dynamic_self == Some(true));
            }
            let mut returns_self = gcx
                .class_method(class, id)
                .is_some_and(|method| method.returns_self);
            receiver_contract |= gcx.class_method(class, id).is_some();
            if let Some(source) = gcx.class_default_source(id) {
                returns_self = gcx
                    .class_default_contract(source)
                    .is_some_and(|proof| proof.preserves_dynamic_self == Some(true));
            }
            if conditional_self == Some(class)
                && gcx.definition_parent(id).is_some_and(|parent| {
                    gcx.try_definition_kind(parent) == Some(crate::hir::DefinitionKind::Interface)
                })
            {
                // Class adoption separately proves every selected receiver
                // implementation. Only a direct declared Self result carries
                // its dynamic-class promise; substituting some other generic
                // result parameter with Self does not create that promise.
                receiver_contract = true;
                let formal_self = match normalize_aliases(gcx, input.ty).kind() {
                    TyKind::Reference(inner) => inner,
                    _ => input.ty,
                };
                returns_self = normalize_aliases(gcx, signature.output) == formal_self;
            }
            if receiver_contract
                && returns_self
                && let Some(value) = args.first()
            {
                let receiver = match operand(state, value) {
                    Origin::ReceiverSlot => Origin::Handle,
                    Origin::Alias(local) => state[local.index()],
                    value => value,
                };
                if receiver == Origin::Handle {
                    result = if gcx.definition_is_async(id) {
                        Origin::FutureHandle
                    } else {
                        Origin::Handle
                    };
                }
            }
        }
    }
    // A helper can retarget an ordinary mutable handle slot. Invalidate the
    // pointed-to storage, not copies of its old strong handle held elsewhere.
    for (index, arg) in args.iter().enumerate() {
        if index == 0 && receiver_contract {
            continue;
        }
        if let Some(place) = arg.place()
            && matches!(
                normalize_aliases(gcx, body.place_ty(gcx, place)).kind(),
                TyKind::Reference(_)
            )
            && let Origin::Alias(local) = operand(state, arg)
        {
            invalidate(state, Origin::Alias(local));
        }
    }
    result
}

pub fn validate<'ctx>(gcx: Gcx<'ctx>, body: &Body<'ctx>) -> CompileResult<()> {
    if body.phase == MirPhase::Lowered
        || gcx.get_closure_captures(body.owner).is_some()
        || !matches!(
            gcx.try_definition_kind(body.owner),
            Some(crate::hir::DefinitionKind::AssociatedFunction)
        )
    {
        return Ok(());
    }
    let Some(class) = gcx
        .get_signature(body.owner)
        .inputs
        .first()
        .filter(|input| input.name.as_str() == "self")
        .map(|input| match normalize_aliases(gcx, input.ty).kind() {
            TyKind::Reference(inner) => inner,
            _ => input.ty,
        })
    else {
        return Ok(());
    };
    if !gcx
        .class_method(class, body.owner)
        .is_some_and(|method| method.returns_self)
        || gcx.class_info(class).is_some_and(|info| info.is_final)
    {
        return Ok(());
    }
    let signature = gcx.get_signature(body.owner);
    let Some((index, input)) = signature
        .inputs
        .iter()
        .enumerate()
        .find(|(_, input)| input.name.as_str() == "self")
    else {
        return Ok(());
    };
    for span in invalid_returns(
        gcx,
        body,
        index,
        matches!(
            normalize_aliases(gcx, input.ty).kind(),
            TyKind::Reference(..)
        ),
        None,
    ) {
        gcx.dcx().emit_error("owned Self result must preserve the receiver's dynamic class; return self, required Self construction, or a proven Self result on that receiver".into(), Some(span));
    }
    gcx.dcx().ok()
}

/// Conditional proof for an interface default or universal receiver body.
/// Failure leaves ordinary struct callers valid. A non-final class must
/// establish this promise for every selected directly Self-returning witness;
/// an explicit Rhs result does not acquire that promise merely by equaling T.
pub(crate) fn default_preserves_dynamic_self<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
) -> Option<bool> {
    if body.phase == MirPhase::Lowered {
        return None;
    }
    conditional_receiver_owner(gcx, body.owner)?;
    let signature = gcx.get_signature(body.owner);
    let input = signature.inputs.first()?;
    if input.name.as_str() != "self" {
        return None;
    }
    let ty = normalize_aliases(gcx, input.ty);
    let (self_ty, borrowed) = match ty.kind() {
        TyKind::Reference(inner) => (inner, true),
        _ => (ty, false),
    };
    if normalize_aliases(gcx, signature.output) != self_ty {
        return None;
    }
    Some(invalid_returns(gcx, body, 0, borrowed, Some(self_ty)).is_empty())
}

fn invalid_returns<'ctx>(
    gcx: Gcx<'ctx>,
    body: &Body<'ctx>,
    index: usize,
    borrowed: bool,
    conditional_self: Option<Ty<'ctx>>,
) -> Vec<crate::span::Span> {
    let mut initial = vec![Origin::Unknown; body.locals.len()];
    initial[index + 1] = if borrowed {
        Origin::ReceiverSlot
    } else {
        Origin::Handle
    };
    let mut states: Vec<Option<State>> = vec![None; body.basic_blocks.len()];
    states[body.start_block.index()] = Some(initial);
    let mut pending = VecDeque::from([body.start_block]);
    while let Some(block) = pending.pop_front() {
        let mut state = states[block.index()].as_ref().unwrap().clone();
        let data = &body.basic_blocks[block];
        for operation in &data.statements {
            statement(&mut state, &operation.kind);
        }
        let Some(terminator) = &data.terminator else {
            continue;
        };
        let (destination, result) = match &terminator.kind {
            TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => {
                let result = call(gcx, body, &mut state, func, args, conditional_self);
                (Some(destination), result)
            }
            TerminatorKind::Yield {
                value, resume_arg, ..
            } => (
                Some(resume_arg),
                if operand(&state, value) == Origin::FutureHandle {
                    Origin::Handle
                } else {
                    Origin::Unknown
                },
            ),
            _ => (None, Origin::Unknown),
        };
        for successor in terminator.kind.successors() {
            let mut edge = state.clone();
            let success = match &terminator.kind {
                TerminatorKind::Call { target, .. } => successor == *target,
                TerminatorKind::Yield { resume, .. } => successor == *resume,
                _ => false,
            };
            if success && let Some(destination) = destination {
                write(&mut edge, destination, result);
            }
            let slot = &mut states[successor.index()];
            if let Some(previous) = slot {
                let mut changed = false;
                for (previous, next) in previous.iter_mut().zip(edge) {
                    if *previous != next && *previous != Origin::Unknown {
                        *previous = Origin::Unknown;
                        changed = true;
                    }
                }
                if changed {
                    pending.push_back(successor);
                }
            } else {
                *slot = Some(edge);
                pending.push_back(successor);
            }
        }
    }
    let mut violations = Vec::new();
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let Some(mut state) = states[block.index()].clone() else {
            continue;
        };
        for operation in &data.statements {
            statement(&mut state, &operation.kind);
        }
        if let Some(terminator) = &data.terminator
            && matches!(terminator.kind, TerminatorKind::Return)
            && state[body.return_local.index()] != Origin::Handle
        {
            violations.push(terminator.span);
        }
    }
    violations
}

#[cfg(test)]
mod tests {
    fn check(body: &str, valid: bool) {
        let source = format!(
            "struct Handle {{ owner: *const uint8 }}\nnamespace runtime {{ func __classAllocatePayload[T](_ value: T) -> script::Handle {{ script::Handle {{ owner: unsafe {{ 0 as *const uint8 }} }} }}; }}\nnamespace intrinsic {{ func __intrinsic_class_from_handle[T](_ handle: script::Handle) -> T {{ loop {{}} }}; }}\nclass Base {{ value: int32 }}\nextend Base {{ public required init(_ value: int32) {{ self.value = value }};\nfunc target(_ other: Base, _ flag: bool) -> Self {{ {body} }}; }}\nfunc replace(_ slot: &Base, _ other: Base) {{ *slot = other }}\nfunc main() {{}}\n"
        );
        // The fixture stops at built MIR, so run this source validation directly.
        let errors = crate::test_support::analyze_native_class_fixture(
            &source,
            &[],
            &[(crate::hir::StdItem::ClassHandle, "Handle")],
            |_, bodies, gcx| {
                for body in &bodies {
                    let _ = super::validate(gcx, body);
                }
                gcx.dcx().take_recorded_diagnostics()
            },
        );
        assert_eq!(errors.is_empty(), valid, "{body}: {errors:#?}");
        if !valid {
            assert!(
                errors
                    .iter()
                    .any(|error| error.message.contains("dynamic class")),
                "{errors:#?}"
            );
        }
    }
    #[test]
    fn conditional_default_self_proof_does_not_reject_valid_struct_defaults() {
        for (body, valid) in [
            ("self", true),
            ("same := self; same", true),
            ("self.identity()", true),
            ("if flag { return self }; self.identity()", true),
            ("other", false),
            ("if flag { return self }; other", false),
            ("var same = self; replace(&same, other); same", false),
        ] {
            let source = format!(
                "interface Factory {{ func identity() -> Self; func target(_ other: Self, _ flag: bool) -> Self {{ {body} }}; }}\nfunc replace[T](_ slot: &T, _ value: T) {{ *slot = value }}\nfunc main() {{}}"
            );
            crate::test_support::analyze_script_built_mir_with_items(
                &source,
                &[],
                |bodies, gcx| {
                    let body = bodies
                        .iter()
                        .find(|body| gcx.definition_ident(body.owner).symbol.as_str() == "target")
                        .unwrap();
                    assert_eq!(
                        super::default_preserves_dynamic_self(gcx, body),
                        Some(valid)
                    );
                    assert!(
                        !gcx.dcx().has_error(),
                        "a conditional class proof is not an additional struct requirement"
                    );
                },
            );
        }
    }

    #[test]
    fn self_results_preserve_identity_across_locals_branches_and_required_construction() {
        for body in [
            "self",
            "Self(7)",
            "same := self; same",
            "if flag { return self }; Self(9)",
            "var same = self; if flag { same = Self(9) }; same",
            "var same = self; snapshot := same; replace(&same, other); snapshot",
        ] {
            check(body, true);
        }
    }
    #[test]
    fn self_results_cannot_hide_unrelated_objects_in_parameters_fields_or_mutated_slots() {
        for body in [
            "other",
            "Base(7)",
            "if flag { return self }; other",
            "var same = self; if flag { same = other }; same",
            "var same = self; replace(&same, other); same",
            "var same = self; alias := &same; replace(alias, other); same",
        ] {
            check(body, false);
        }
    }
}

pub(crate) fn conditional_receiver_owner(
    gcx: Gcx<'_>,
    method: crate::hir::DefinitionID,
) -> Option<()> {
    // Generated cleanup/clone helpers have their own verified generation
    // contracts and need not have a source resolution output at all.
    let resolution = gcx.try_resolution_output(method.package())?;
    if !matches!(
        resolution.definition_to_kind.get(&method),
        Some(DefinitionKind::AssociatedFunction)
    ) {
        return None;
    }
    let parent = gcx.definition_parent(method)?;
    if gcx.try_definition_kind(parent) == Some(DefinitionKind::Interface) {
        return Some(());
    }
    let target = normalize_aliases(gcx, gcx.get_impl_target_ty(parent)?);
    matches!(target.kind(), TyKind::Parameter(_)).then_some(())
}

pub(crate) fn validate_instance<'ctx>(
    gcx: Gcx<'ctx>,
    method: crate::hir::DefinitionID,
    arguments: crate::sema::models::GenericArguments<'ctx>,
) -> CompileResult<()> {
    if conditional_receiver_owner(gcx, method).is_none() {
        return Ok(());
    }
    let signature = gcx.get_signature(method);
    let Some(input) = signature
        .inputs
        .first()
        .filter(|input| input.name.as_str() == "self")
    else {
        return Ok(());
    };
    let receiver = normalize_aliases(gcx, instantiate_ty_with_args(gcx, input.ty, arguments));
    let class = receiver;
    if gcx.class_info(class).is_some_and(|info| !info.is_final)
        && crate::sema::impl_engine::class_receiver_requires_dynamic_self(gcx, method)
        && !gcx
            .class_default_contract(method)
            .is_some_and(|proof| proof.preserves_dynamic_self == Some(true))
    {
        gcx.dcx().emit_error("a non-final class Self witness requires a checked subclass-preserving implementation; this generic body may return an unrelated class object".into(), Some(gcx.definition_ident(method).span));
    }
    gcx.dcx().ok()
}
