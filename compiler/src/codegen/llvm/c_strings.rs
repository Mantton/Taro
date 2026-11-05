//! Native string headers follow the platform C ABI, not LLVM's default
//! aggregate splitting. SysV x86-64 rolls a two-word header wholly onto the
//! stack when fewer than two integer argument registers remain. In particular,
//! task-group spawn has three scalars followed by two strings: its second
//! string must use `byval`, leaving the last register for the following scalar.

use super::*;
use crate::sema::models::Ty;
use inkwell::types::AnyType;

#[derive(Clone, Copy)]
enum Argument {
    Integer,
    Float,
    String,
    Ignore,
}

fn stack_strings(arguments: &[Argument]) -> Vec<bool> {
    let mut remaining = 6_usize;
    arguments
        .iter()
        .map(|argument| match argument {
            Argument::String if remaining < 2 => true,
            Argument::String => {
                remaining -= 2;
                false
            }
            Argument::Integer => {
                remaining = remaining.saturating_sub(1);
                false
            }
            Argument::Float | Argument::Ignore => false,
        })
        .collect()
}

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn classify_native_string_arguments(&self, fn_abi: &mut abi::FnAbi<'gcx>) {
        let triple = self.target_machine.get_triple();
        let triple = triple.as_str().to_str().unwrap_or("");
        if !triple.starts_with("x86_64-")
            || !(triple.contains("linux") || triple.contains("darwin"))
        {
            return;
        }
        // This is the scalar/string wire used by native runtime services.
        // General foreign aggregates need their own full C ABI classification;
        // do not guess their register use or hidden return arguments here.
        let classify = |ty: Ty<'gcx>| {
            let ty = crate::sema::tycheck::utils::normalize_aliases(self.gcx, ty);
            if matches!(ty.kind(), TyKind::String) {
                return Some(Argument::String);
            }
            match self.lower_ty(ty) {
                None => Some(Argument::Ignore),
                Some(BasicTypeEnum::IntType(int)) if int.get_bit_width() <= 64 => {
                    Some(Argument::Integer)
                }
                Some(BasicTypeEnum::PointerType(_)) => Some(Argument::Integer),
                Some(BasicTypeEnum::FloatType(_)) => Some(Argument::Float),
                _ => None,
            }
        };
        if classify(fn_abi.ret.ty).is_none() {
            return;
        }
        let Some(arguments) = fn_abi
            .args
            .iter()
            .map(|argument| classify(argument.ty))
            .collect::<Option<Vec<_>>>()
        else {
            return;
        };
        for (argument, byval) in fn_abi.args.iter_mut().zip(stack_strings(&arguments)) {
            if byval {
                argument.mode = abi::PassMode::Indirect { align: 8, size: 16 };
                argument.byval = true;
            }
        }
    }

    pub(super) fn native_string_argument_attributes(
        &self,
        fn_abi: &abi::FnAbi<'gcx>,
    ) -> Vec<(AttributeLoc, Attribute)> {
        let mut attributes = Vec::new();
        let mut index = u32::from(matches!(fn_abi.ret.mode, abi::PassMode::Indirect { .. }));
        for argument in &fn_abi.args {
            if matches!(argument.mode, abi::PassMode::Ignore) {
                continue;
            }
            if argument.byval {
                let ty = self.lower_ty(argument.ty).expect("native string layout");
                let byval = self.context.create_type_attribute(
                    Attribute::get_named_enum_kind_id("byval"),
                    ty.as_any_type_enum(),
                );
                let align = self
                    .context
                    .create_enum_attribute(Attribute::get_named_enum_kind_id("align"), 8);
                attributes.push((AttributeLoc::Param(index), byval));
                attributes.push((AttributeLoc::Param(index), align));
            }
            index += 1;
        }
        attributes
    }

    pub(super) fn install_native_string_call_attributes(
        &self,
        fn_abi: &abi::FnAbi<'gcx>,
        call: CallSiteValue<'llvm>,
    ) {
        for (location, attribute) in self.native_string_argument_attributes(fn_abi) {
            call.add_attribute(location, attribute);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::{Argument::*, stack_strings};

    #[test]
    fn sysv_native_string_stack_contract_is_installed_on_declaration_and_call() {
        use inkwell::targets::{InitializationConfig, Target, TargetTriple};
        crate::test_support::with_test_gcx(|gcx| {
            let context = Context::create();
            let mut emitter = Emitter::new(
                &context,
                context.create_module("native-string-wire"),
                context.create_builder(),
                gcx,
            )
            .unwrap_or_else(|_| panic!("emitter"));
            Target::initialize_all(&InitializationConfig::default());
            let triple = TargetTriple::create("x86_64-unknown-linux-gnu");
            emitter.target_machine = Target::from_triple(&triple)
                .unwrap()
                .create_target_machine(
                    &triple,
                    "generic",
                    "",
                    inkwell::OptimizationLevel::None,
                    inkwell::targets::RelocMode::Default,
                    inkwell::targets::CodeModel::Default,
                )
                .unwrap();
            emitter.target_data = emitter.target_machine.get_target_data();
            let word = gcx.types.uint;
            let mut abi = abi::compute_fn_abi_from_tys(
                &[
                    word,
                    word,
                    word,
                    gcx.types.string,
                    gcx.types.string,
                    word,
                    word,
                ],
                word,
                false,
                |ty| emitter.type_layout(ty),
                abi::AbiPolicy {
                    enable_indirect_returns: false,
                    indirect_return_threshold_bytes: 0,
                    enable_indirect_args: false,
                    indirect_arg_threshold_bytes: 0,
                },
            );
            emitter.classify_native_string_arguments(&mut abi);
            assert!(!abi.args[3].byval);
            assert!(abi.args[4].byval);
            let signature = emitter.lower_fn_abi(&abi);
            let native = emitter.module.add_function("native", signature, None);
            for (location, attribute) in emitter.native_string_argument_attributes(&abi) {
                native.add_attribute(location, attribute);
            }
            let caller = emitter.module.add_function("caller", signature, None);
            emitter
                .builder
                .position_at_end(context.append_basic_block(caller, "entry"));
            let args: Vec<_> = caller.get_param_iter().map(Into::into).collect();
            let call = emitter.builder.build_call(native, &args, "result").unwrap();
            emitter.install_native_string_call_attributes(&abi, call);
            emitter
                .builder
                .build_return(Some(&call.try_as_basic_value().basic().unwrap()))
                .unwrap();
            emitter.module.verify().unwrap();
            let ir = emitter.module.print_to_string().to_string();
            // Clang's SysV signature places the entire second header on the
            // stack and leaves r9 available to the following source-line word.
            assert_eq!(
                ir.matches("byval(%_stringHeader) align 8").count(),
                2,
                "{ir}"
            );
        });
    }

    #[test]
    fn sysv_string_rollback_preserves_the_last_integer_register() {
        assert_eq!(
            stack_strings(&[Integer, Integer, Integer, String, String, Integer, String]),
            [false, false, false, false, true, false, true],
        );
        assert_eq!(
            stack_strings(&[Integer, Integer, String, String, Integer]),
            [false, false, false, false, false],
        );
    }

    #[test]
    fn sysv_float_and_empty_arguments_do_not_consume_integer_registers() {
        assert_eq!(
            stack_strings(&[String, Float, String, Ignore, String, String]),
            [false, false, false, false, false, true],
        );
    }
}
