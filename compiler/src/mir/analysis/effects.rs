use crate::{
    compile::context::Gcx,
    hir::Abi,
    mir::{CallEffect, ConstantKind, Operand},
    runtime_abi::{RuntimeCallEffect, call_effect_for_symbol},
};

/// Classify a MIR call from its language ABI and the exhaustive runtime ABI
/// registry. Indirect and virtual calls conservatively enter Taro code; runtime
/// callbacks may reenter it and blocking calls have an explicit declaration.
/// These classifications control diagnostics and native-boundary validation,
/// never allocation reachability or object lifetime.
pub fn classify_call_effect(gcx: Gcx<'_>, function: &Operand<'_>) -> Result<CallEffect, String> {
    let Operand::Constant(constant) = function else {
        return Ok(CallEffect::Taro);
    };
    let ConstantKind::Function(definition, _, _) = constant.value else {
        return Ok(CallEffect::Taro);
    };

    if crate::sema::lowering::statics::referenced_storage(gcx, definition).is_some() {
        return Ok(CallEffect::Callback);
    }
    match gcx.get_signature(definition).abi {
        Some(Abi::Intrinsic | Abi::C) => Ok(CallEffect::Direct),
        Some(Abi::Blocking) => Ok(CallEffect::Blocking),
        Some(Abi::Runtime) => {
            let symbol = gcx.definition_symbol_or_fallback(definition);
            let symbol = gcx.symbol_text(symbol);
            let effect = call_effect_for_symbol(symbol.as_str()).ok_or_else(|| {
                format!("runtime ABI entry `{symbol}` is missing a call effect classification")
            })?;
            Ok(match effect {
                RuntimeCallEffect::Direct => CallEffect::Direct,
                RuntimeCallEffect::Callback => CallEffect::Callback,
                RuntimeCallEffect::Blocking => CallEffect::Blocking,
            })
        }
        None => Ok(CallEffect::Taro),
    }
}

/// A straight-line wrapper around one pointer-offset intrinsic has no native
/// operation beyond the intrinsic itself and pointer casts. Inlining removes
/// its call rather than growing machine code; when outlined, it also needs no
/// GC entry poll. Keep this deliberately narrower than general call effects:
/// memory accesses, allocations, arbitrary intrinsics and cycles do not qualify.
pub(crate) fn is_pointer_offset_wrapper<'ctx>(
    gcx: Gcx<'ctx>,
    body: &crate::mir::Body<'ctx>,
) -> bool {
    is_single_intrinsic_wrapper(
        gcx,
        body,
        crate::sema::models::GenericArguments::empty(),
        IntrinsicWrapper::Offset,
    )
}

/// An explicitly inlined integer load forwarder replaces its call with one
/// machine load. Check concrete types: aggregate reads can require traced copy
/// operations and do not qualify. This permits zero-growth inlining only;
/// outlined reads retain their ordinary GC entry poll.
pub(crate) fn is_scalar_pointer_read_wrapper<'ctx>(
    gcx: Gcx<'ctx>,
    body: &crate::mir::Body<'ctx>,
    args: crate::sema::models::GenericArguments<'ctx>,
) -> bool {
    is_single_intrinsic_wrapper(gcx, body, args, IntrinsicWrapper::ScalarRead)
}

/// String header getters replace a call with one field load. This allowance
/// applies only to inlining; outlined getters retain normal safepoints.
pub(crate) fn is_string_header_wrapper<'ctx>(
    gcx: Gcx<'ctx>,
    body: &crate::mir::Body<'ctx>,
    args: crate::sema::models::GenericArguments<'ctx>,
) -> bool {
    is_single_intrinsic_wrapper(gcx, body, args, IntrinsicWrapper::StringHeader)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum IntrinsicWrapper {
    Offset,
    ScalarRead,
    StringHeader,
}

fn is_single_intrinsic_wrapper<'ctx>(
    gcx: Gcx<'ctx>,
    body: &crate::mir::Body<'ctx>,
    args: crate::sema::models::GenericArguments<'ctx>,
    wrapper: IntrinsicWrapper,
) -> bool {
    use crate::mir::{CastKind, Rvalue, StatementKind, TerminatorKind};
    use crate::sema::models::TyKind;
    let concrete =
        |ty| crate::sema::tycheck::utils::instantiate::instantiate_ty_with_args(gcx, ty, args);
    if body.is_async
        || body.escape_locals.iter().any(|escapes| *escapes)
        || body.locals.iter().any(|local| {
            let ty = concrete(local.ty);
            ty != gcx.types.void
                && !matches!(ty.kind(), TyKind::Pointer(..) | TyKind::Int(_) | TyKind::UInt(_))
                && !(wrapper == IntrinsicWrapper::StringHeader
                    && (ty == gcx.types.string
                        || matches!(ty.kind(), TyKind::Reference(inner) if inner == gcx.types.string)))
        })
    {
        return false;
    }
    let local_operand = |operand: &Operand<'_>| match operand {
        Operand::Copy(place) => place.projection.is_empty(),
        Operand::CopyWith(..) => false,
        Operand::Constant(constant) => matches!(
            constant.value,
            ConstantKind::Integer(_) | ConstantKind::Unit
        ),
    };
    let mut block = body.start_block;
    let mut remaining_blocks = body.basic_blocks.len();
    let mut budget = 32_usize;
    let mut intrinsic_calls = 0;
    loop {
        let Some(remaining) = remaining_blocks.checked_sub(1) else {
            return false;
        };
        remaining_blocks = remaining;
        let data = &body.basic_blocks[block];
        for statement in &data.statements {
            match &statement.kind {
                StatementKind::SourceScope(_)
                | StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::SetInitialized(_)
                | StatementKind::KeepAlive(_)
                | StatementKind::Nop => continue,
                StatementKind::Assign(destination, value) if destination.projection.is_empty() => {
                    let allowed = match value {
                        Rvalue::Use(operand) => local_operand(operand),
                        // Canonical MIR normalizes assignments to CopyValue.
                        // Eligible values are scalars or immutable string headers.
                        Rvalue::CopyValue { source } => source.projection.is_empty(),
                        Rvalue::Ref { place } => {
                            wrapper == IntrinsicWrapper::StringHeader
                                && place.projection.is_empty()
                                && concrete(body.locals[place.local].ty) == gcx.types.string
                        }
                        Rvalue::Cast {
                            operand,
                            ty,
                            kind: CastKind::Pointer | CastKind::Numeric,
                        } => {
                            matches!(ty.kind(), TyKind::Pointer(..))
                                && matches!(operand, Operand::Copy(place)
                                if place.projection.is_empty()
                                    && matches!(body.locals[place.local].ty.kind(), TyKind::Pointer(..)))
                        }
                        _ => false,
                    };
                    if !allowed {
                        return false;
                    }
                }
                _ => return false,
            }
            let Some(remaining) = budget.checked_sub(1) else {
                return false;
            };
            budget = remaining;
        }
        let Some(terminator) = &data.terminator else {
            return false;
        };
        block = match &terminator.kind {
            TerminatorKind::Return => return intrinsic_calls == 1,
            TerminatorKind::Goto { target } => *target,
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let Operand::Constant(constant) = func else {
                    return false;
                };
                let ConstantKind::Function(definition, _, _) = constant.value else {
                    return false;
                };
                let name = gcx.definition_symbol_or_fallback(definition);
                let name = gcx.symbol_text(name);
                let allowed = if wrapper == IntrinsicWrapper::StringHeader {
                    matches!(
                        name.as_str(),
                        "__intrinsic_string_len" | "__intrinsic_string_data"
                    )
                } else if wrapper == IntrinsicWrapper::ScalarRead {
                    name.as_str() == "__intrinsic_ptr_read"
                        && matches!(
                            concrete(body.locals[destination.local].ty).kind(),
                            TyKind::Int(_) | TyKind::UInt(_)
                        )
                } else {
                    matches!(
                        name.as_str(),
                        "__intrinsic_ptr_add"
                            | "__intrinsic_ptr_sub"
                            | "__intrinsic_ptr_offset"
                            | "__intrinsic_ptr_byte_add"
                            | "__intrinsic_ptr_byte_sub"
                    )
                };
                if gcx.get_signature(definition).abi != Some(Abi::Intrinsic)
                    || !allowed
                    || !destination.projection.is_empty()
                    || !args.iter().all(local_operand)
                {
                    return false;
                }
                intrinsic_calls += 1;
                if intrinsic_calls != 1 {
                    return false;
                }
                *target
            }
            _ => return false,
        };
    }
}

#[cfg(test)]
mod pointer_wrapper_tests {
    use super::{is_pointer_offset_wrapper, is_scalar_pointer_read_wrapper};
    use crate::mir::{
        StatementKind,
        optimize::{MirPass, gc_safepoints::InsertSafepoints},
    };

    #[test]
    fn header_forwarders_exclude_transforms_other_intrinsics_and_calls() {
        let source = r#"
extern "taro_intrinsic" {
    func __intrinsic_string_len(_ value: &string) -> usize
    func __intrinsic_string_data(_ value: &string) -> *const uint8
    unsafe func __intrinsic_string_slice(_ value: &string, _ start: usize, _ count: usize) -> string
}
func length(_ value: string) -> usize { __intrinsic_string_len(&value) }
func data(_ value: string) -> *const uint8 { __intrinsic_string_data(&value) }
func changed(_ value: string) -> usize { __intrinsic_string_len(&value) + (1 as usize) }
func slice(_ value: string) -> string { unsafe { __intrinsic_string_slice(&value, 0 as usize, 0 as usize) } }
func chain(_ value: string) -> usize { length(value) }
func main() {}
"#;
        crate::test_support::analyze_script_built_mir(source, |bodies, gcx| {
            for mut body in bodies {
                let name = gcx.definition_ident(body.owner).symbol;
                if name.as_str() == "main" {
                    continue;
                }
                assert!(crate::mir::optimize::run_local_passes(gcx, &mut body).is_ok());
                assert_eq!(
                    super::is_string_header_wrapper(
                        gcx,
                        &body,
                        crate::sema::models::GenericArguments::empty()
                    ),
                    matches!(name.as_str(), "length" | "data"),
                    "{name}: {}",
                    crate::mir::test_support::pretty_body(gcx, &body)
                );
            }
        });
    }

    #[test]
    fn pointer_wrapper_safety_rejects_reads_stores_calls_cycles_and_chains() {
        let source = r#"
extern "taro_intrinsic" {
    func __intrinsic_ptr_add[T](_ ptr: *T, _ count: usize) -> *T
    unsafe func __intrinsic_ptr_read[T](_ ptr: *T) -> T
}
func pointer(_ ptr: *mut int32) -> *mut int32 {
    unsafe { __intrinsic_ptr_add(ptr as *int32, 1 as usize) as *mut int32 }
}
func read(_ ptr: *int32) -> int32 { unsafe { __intrinsic_ptr_read(ptr) } }
func readReference(_ ptr: *&int32) -> &int32 { unsafe { __intrinsic_ptr_read(ptr) } }
func genericRead[T](_ ptr: *T) -> T { unsafe { __intrinsic_ptr_read(ptr) } }
func store(_ ptr: *mut int32) -> *mut int32 {
    unsafe { *ptr = 7; __intrinsic_ptr_add(ptr as *int32, 1 as usize) as *mut int32 }
}
func opaque(_ ptr: *mut int32) -> *mut int32 { pointer(ptr) }
func chain(_ ptr: *int32) -> *int32 {
    unsafe { __intrinsic_ptr_add(__intrinsic_ptr_add(ptr, 1 as usize), 1 as usize) }
}
func cycle(_ ptr: *int32, _ count: usize) -> *int32 {
    var value = ptr
    var index: usize = 0
    while index < count { value = unsafe { __intrinsic_ptr_add(value, 1 as usize) }; index += 1 }
    value
}
func main() {}
"#;
        crate::test_support::analyze_script_built_mir(source, |bodies, gcx| {
            for mut body in bodies {
                let name = gcx.definition_ident(body.owner).symbol;
                if name.as_str() == "main" {
                    continue;
                }
                let expected = name.as_str() == "pointer";
                assert!(crate::mir::optimize::run_local_passes(gcx, &mut body).is_ok());
                assert_eq!(
                    is_pointer_offset_wrapper(gcx, &body),
                    expected,
                    "{name}: {}",
                    crate::mir::test_support::pretty_body(gcx, &body)
                );
                assert_eq!(
                    is_scalar_pointer_read_wrapper(
                        gcx,
                        &body,
                        crate::sema::models::GenericArguments::empty()
                    ),
                    name.as_str() == "read",
                    "only a concrete integer load qualifies: {name}"
                );
                InsertSafepoints
                    .run(gcx, &mut body)
                    .unwrap_or_else(|_| panic!("safepoints: {name}"));
                let polls = body
                    .basic_blocks
                    .iter()
                    .flat_map(|block| &block.statements)
                    .filter(|statement| matches!(statement.kind, StatementKind::GcSafepoint(_)))
                    .count();
                assert_eq!(polls == 0, expected, "{name}: {polls} polls");
            }
        });
    }
}
