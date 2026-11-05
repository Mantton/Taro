//! C scalar extension attributes are ABI contracts, including on invokes and
//! compiler-generated wire facades. Linux AArch64 deliberately provides none.
use super::*;
use crate::sema::models::{IntTy, UIntTy};
use inkwell::values::{AsValueRef, InstructionOpcode, InstructionValue};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Extension {
    location: AttributeLoc,
    width: u32,
    signed: bool,
}

fn target_requires_extensions(triple: &str) -> bool {
    (triple.starts_with("x86_64-")
        && (triple.contains("apple-darwin") || triple.contains("-linux-")))
        || ((triple.starts_with("aarch64-") || triple.starts_with("arm64-"))
            && triple.contains("apple-darwin"))
}

fn narrow(ty: &str, location: AttributeLoc) -> Option<Extension> {
    let (width, signed) = match ty.trim() {
        "bool" => (1, false),
        "u8" => (8, false),
        "i8" => (8, true),
        "u16" => (16, false),
        "i16" => (16, true),
        _ => return None,
    };
    Some(Extension {
        location,
        width,
        signed,
    })
}

pub(super) fn source<'ctx>(
    gcx: Gcx<'ctx>,
    inputs: &[Ty<'ctx>],
    output: Ty<'ctx>,
) -> Vec<Extension> {
    if !target_requires_extensions(&gcx.store.target_layout.triple_string()) {
        return vec![];
    }
    let name = |ty: Ty<'ctx>| match crate::sema::tycheck::utils::normalize_aliases(gcx, ty).kind() {
        TyKind::Bool => "bool",
        TyKind::Int(IntTy::I8) => "i8",
        TyKind::Int(IntTy::I16) => "i16",
        TyKind::UInt(UIntTy::U8) => "u8",
        TyKind::UInt(UIntTy::U16) => "u16",
        _ => "",
    };
    inputs
        .iter()
        .enumerate()
        .filter_map(|(index, ty)| narrow(name(*ty), AttributeLoc::Param(index as u32)))
        .chain(narrow(name(output), AttributeLoc::Return))
        .collect()
}

fn install<'llvm>(
    context: &'llvm Context,
    function: FunctionValue<'llvm>,
    extensions: &[Extension],
) -> Result<(), String> {
    for extension in extensions {
        let ty = match extension.location {
            AttributeLoc::Param(index) => function
                .get_type()
                .get_param_types()
                .get(index as usize)
                .copied(),
            AttributeLoc::Return => function.get_type().get_return_type().map(Into::into),
            _ => unreachable!(),
        };
        if !matches!(ty, Some(inkwell::types::BasicMetadataTypeEnum::IntType(ty)) if ty.get_bit_width() == extension.width)
        {
            return Err(format!(
                "C scalar ABI width mismatch for {} at {:?}",
                function.get_name().to_string_lossy(),
                extension.location
            ));
        }
        let name = if extension.signed {
            "signext"
        } else {
            "zeroext"
        };
        let opposite = if extension.signed {
            "zeroext"
        } else {
            "signext"
        };
        function.remove_enum_attribute(
            extension.location,
            Attribute::get_named_enum_kind_id(opposite),
        );
        function.add_attribute(
            extension.location,
            context.create_enum_attribute(Attribute::get_named_enum_kind_id(name), 0),
        );
    }
    Ok(())
}

pub(super) fn install_source<'llvm>(
    context: &'llvm Context,
    function: FunctionValue<'llvm>,
    extensions: &[Extension],
) {
    install(context, function, extensions)
        .expect("source C signature and its lowered scalar positions must agree");
}

fn call_site(instruction: InstructionValue<'_>) -> Option<CallSiteValue<'_>> {
    matches!(
        instruction.get_opcode(),
        InstructionOpcode::Call | InstructionOpcode::Invoke
    )
    .then(|| {
        // Both instructions are LLVM CallBase values. Inkwell's TryFrom
        // currently recognizes Call only, so handle Invoke explicitly.
        unsafe { CallSiteValue::new(instruction.as_value_ref()) }
    })
}

/// Parse only the outer parameter list; callback signatures may contain their
/// own commas/arrows. The canonical registry remains the source of signedness.
fn runtime_extensions(signature: &str) -> Vec<Extension> {
    if !signature.starts_with('(') {
        return vec![];
    }
    let mut nested = 0;
    let mut start = 1;
    let mut parameters = Vec::new();
    for (index, byte) in signature.bytes().enumerate().skip(1) {
        match byte {
            b'(' => nested += 1,
            b')' if nested != 0 => nested -= 1,
            b',' if nested == 0 => {
                parameters.push(&signature[start..index]);
                start = index + 1;
            }
            b')' => {
                if start != index {
                    parameters.push(&signature[start..index]);
                }
                let mut extensions: Vec<_> = parameters
                    .iter()
                    .enumerate()
                    .filter_map(|(index, ty)| narrow(ty, AttributeLoc::Param(index as u32)))
                    .collect();
                if let Some(output) = signature[index + 1..].strip_prefix("->") {
                    extensions.extend(narrow(output, AttributeLoc::Return));
                }
                return extensions;
            }
            _ => {}
        }
    }
    vec![]
}

/// Run after lazy bodies and again after entry/harness generation. Only known
/// runtime declarations or explicit source externs acquire these attributes;
/// ordinary Taro function/virtual-call conventions remain unchanged.
pub(super) fn finalize(emitter: &Emitter<'_, '_>) -> CompileResult<()> {
    if !target_requires_extensions(&emitter.gcx.store.target_layout.triple_string()) {
        return Ok(());
    }
    for function in emitter.module.get_functions() {
        if let Some(signature) =
            crate::runtime_abi::signature_for_symbol(&function.get_name().to_string_lossy())
        {
            install(emitter.context, function, &runtime_extensions(&signature)).map_err(
                |error| {
                    emitter.gcx.dcx().emit_error(error, None);
                    crate::error::ReportedError
                },
            )?;
        }
    }
    for (instance, (function, _)) in &emitter.functions {
        if let Some(definition) = emitter
            .gcx
            .store
            .synthetic_definitions
            .borrow()
            .get(&instance.def_id())
            && definition.kind == crate::sema::models::SyntheticDefinitionKind::AsyncPoll
        {
            crate::mir::optimize::async_transform::validate_poll_declaration(
                emitter.gcx,
                definition,
            )
            .map_err(|error| {
                emitter.gcx.dcx().emit_error(error, None);
                crate::error::ReportedError
            })?;
            install(
                emitter.context,
                *function,
                &[Extension {
                    location: AttributeLoc::Return,
                    width: 8,
                    signed: false,
                }],
            )
            .map_err(|error| {
                emitter.gcx.dcx().emit_error(error, None);
                crate::error::ReportedError
            })?;
        }
    }
    for function in emitter.module.get_functions() {
        for block in function.get_basic_blocks() {
            for instruction in block.get_instructions() {
                let Some(call) = call_site(instruction) else {
                    continue;
                };
                let Some(callee) = call.get_called_fn_value() else {
                    continue;
                };
                for location in std::iter::once(AttributeLoc::Return)
                    .chain((0..callee.count_params()).map(AttributeLoc::Param))
                {
                    for name in ["signext", "zeroext"] {
                        if let Some(attribute) = callee
                            .get_enum_attribute(location, Attribute::get_named_enum_kind_id(name))
                        {
                            call.add_attribute(location, attribute);
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn generated_test_harness_uses_the_exact_runtime_scalar_contract() {
        crate::test_support::analyze_native_class_fixture(
            "func main() {}",
            &[],
            &[],
            |_, _, gcx| {
                let context = Context::create();
                let emitter = Emitter::new(
                    &context,
                    context.create_module("test-harness-abi"),
                    context.create_builder(),
                    gcx,
                )
                .unwrap_or_else(|_| panic!("emitter"));
                let status = emitter.declare_test_panic_status_fn();
                let finish = emitter.declare_test_panic_finish_fn();
                assert_eq!(
                    crate::runtime_abi::signature_for_symbol("__rt__test_panic_status").as_deref(),
                    Some("(bool,bool,*const u8,usize)->u8")
                );
                assert_eq!(
                    crate::runtime_abi::signature_for_symbol("__rt__test_panic_finish").as_deref(),
                    Some("(u8,*const u8,usize)->void")
                );
                assert_eq!(status.count_params(), 4);
                assert_eq!(finish.count_params(), 3);
                finalize(&emitter).unwrap_or_else(|_| {
                    panic!("harness ABI: {:#?}", gcx.dcx().take_recorded_diagnostics())
                });
                let requires = target_requires_extensions(&gcx.store.target_layout.triple_string());
                let id = Attribute::get_named_enum_kind_id("zeroext");
                for location in [
                    AttributeLoc::Return,
                    AttributeLoc::Param(0),
                    AttributeLoc::Param(1),
                ] {
                    assert_eq!(status.get_enum_attribute(location, id).is_some(), requires);
                }
                assert_eq!(
                    finish
                        .get_enum_attribute(AttributeLoc::Param(0), id)
                        .is_some(),
                    requires
                );
                emitter.module.verify().unwrap();
            },
        );
    }

    #[test]
    fn extension_rules_follow_the_reviewed_clang_target_abis() {
        for triple in [
            "arm64-apple-darwin",
            "aarch64-apple-darwin",
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
        ] {
            assert!(target_requires_extensions(triple));
        }
        for triple in [
            "aarch64-unknown-linux-gnu",
            "riscv64-unknown-linux-gnu",
            "wasm32-unknown-unknown",
            "x86_64-pc-windows-msvc",
        ] {
            assert!(!target_requires_extensions(triple));
        }
        let extensions = runtime_extensions("(fn(i32,u8)->void,*const u8,bool,i16)->u8");
        assert_eq!(
            extensions,
            vec![
                Extension {
                    location: AttributeLoc::Param(2),
                    width: 1,
                    signed: false
                },
                Extension {
                    location: AttributeLoc::Param(3),
                    width: 16,
                    signed: true
                },
                Extension {
                    location: AttributeLoc::Return,
                    width: 8,
                    signed: false
                }
            ]
        );
    }
}
