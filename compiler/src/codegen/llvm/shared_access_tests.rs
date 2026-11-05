//! Shared-memory accesses keep each pointer word single-copy (G25).
use super::*;

fn emit(check: impl for<'llvm> FnOnce(&Emitter<'llvm, '_>, PointerValue<'llvm>)) -> String {
    let mut ir = String::new();
    crate::test_support::analyze_script("func main() {}", |_, gcx| {
        let context = Context::create();
        let emitter = Emitter::new(
            &context,
            context.create_module("shared-access"),
            context.create_builder(),
            gcx,
        )
        .unwrap_or_else(|_| panic!("shared access emitter"));
        let pointer_ty = context.ptr_type(AddressSpace::default());
        let function = emitter.module.add_function(
            "shared_access_fixture",
            context.void_type().fn_type(&[pointer_ty.into()], false),
            None,
        );
        let entry = context.append_basic_block(function, "entry");
        emitter.builder.position_at_end(entry);
        let target = function.get_first_param().unwrap().into_pointer_value();
        check(&emitter, target);
        emitter.builder.build_return(None).unwrap();
        emitter.module.verify().expect("valid shared access module");
        emitter
            .module
            .run_passes(
                "default<O2>",
                &emitter.target_machine,
                PassBuilderOptions::create(),
            )
            .expect("optimize shared access module");
        ir = emitter.module.print_to_string().to_string();
    });
    ir
}

#[test]
fn class_handles_store_their_pointer_with_one_unordered_access() {
    let ir = emit(|emitter, target| {
        let pointer_ty = emitter.context.ptr_type(AddressSpace::default());
        let handle_ty = emitter.context.struct_type(&[pointer_ty.into()], false);
        let handle = handle_ty.const_named_struct(&[pointer_ty.const_null().into()]);
        emitter.build_shared_store(target, handle.into());
    });
    assert!(
        ir.contains("store atomic ptr null, ptr %0 unordered, align 8"),
        "{ir}"
    );
}

#[test]
fn multiword_values_split_only_their_pointer_words() {
    let ir = emit(|emitter, target| {
        let pointer_ty = emitter.context.ptr_type(AddressSpace::default());
        let string_ty = emitter
            .context
            .struct_type(&[pointer_ty.into(), emitter.usize_ty.into()], false);
        let loaded = emitter.build_shared_load(string_ty.into(), target, "string");
        let copy = unsafe {
            emitter
                .builder
                .build_in_bounds_gep(
                    string_ty,
                    target,
                    &[emitter.usize_ty.const_int(1, false)],
                    "copy",
                )
                .unwrap()
        };
        emitter.build_shared_store(copy, loaded);
    });
    assert!(
        ir.contains("load atomic ptr, ptr %0 unordered, align 8"),
        "{ir}"
    );
    assert!(ir.contains("store atomic ptr"), "{ir}");
    assert!(!ir.contains("atomic i64"), "{ir}");
}

#[test]
fn large_pointer_aggregates_copy_words_atomically() {
    let ir = emit(|emitter, target| {
        let pointer_ty = emitter.context.ptr_type(AddressSpace::default());
        let array_ty = pointer_ty.array_type(32);
        let loaded = emitter.build_shared_load(array_ty.into(), target, "array");
        emitter.build_shared_store(target, loaded);
    });
    assert!(
        ir.contains("@llvm.memmove.element.unordered.atomic"),
        "{ir}"
    );
    assert!(ir.contains("i32 8)"), "{ir}");
}

#[test]
fn pointer_free_values_keep_plain_accesses() {
    let ir = emit(|emitter, target| {
        let array_ty = emitter.usize_ty.array_type(32);
        let loaded = emitter.build_shared_load(array_ty.into(), target, "words");
        emitter.build_shared_store(target, loaded);
    });
    assert!(!ir.contains("atomic"), "{ir}");
}
