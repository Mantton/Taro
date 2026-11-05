//! Main's two-word immutable string values. GC/native producers use the same
//! wire; mutable or native-owned byte storage is copied explicitly by std.
use super::*;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn string_constant_header(
        &self,
        ty: StructType<'llvm>,
        data: PointerValue<'llvm>,
        length: IntValue<'llvm>,
    ) -> inkwell::values::StructValue<'llvm> {
        let fields = vec![data.into(), length.into()];
        ty.const_named_struct(&fields)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gc_strings_share_mains_two_word_native_wire_without_owner_symbols() {
        crate::test_support::analyze_script("func main() {}", |_, gcx| {
            let context = Context::create();
            let module = context.create_module("gc-string-contract");
            let mut emitter = Emitter::new(&context, module, context.create_builder(), gcx)
                .unwrap_or_else(|_| panic!("GC string emitter"));
            let header = emitter
                .lower_ty(gcx.types.string)
                .unwrap()
                .into_struct_type();
            assert_eq!(header.count_fields(), 2);
            assert_eq!(
                emitter.target_data.get_abi_size(&header),
                2 * emitter.target_data.get_pointer_byte_size(None) as u64
            );
            emitter.module.verify().unwrap();
            assert!(
                !emitter
                    .module
                    .print_to_string()
                    .to_string()
                    .contains("immutable_bytes")
            );
            assert!(
                emitter
                    .gc_copy_layout_nodes_for_ty(gcx.types.string)
                    .is_empty(),
                "ordinary string copies are bitwise"
            );
        });
    }
}
