//! Immutable two-word strings and their shared foreign-call wire.
use super::*;
use inkwell::values::StructValue;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    /// Wrap an immutable byte range. Safe copying constructors allocate in std.
    pub(super) fn string_value_from_parts(
        &mut self,
        data: PointerValue<'llvm>,
        len: IntValue<'llvm>,
    ) -> StructValue<'llvm> {
        {
            // As on main, this trusted intrinsic only wraps existing bytes.
            // Safe copying constructors allocate explicitly in std.
            let header = string_header_ty(self.context, &self.target_data);
            let value = self
                .builder
                .build_insert_value(header.get_undef(), data, 0, "string_data")
                .unwrap();
            return self
                .builder
                .build_insert_value(value, len, 1, "string_length")
                .unwrap()
                .into_struct_value();
        }
    }

    /// Trusted slicing primitive. The standard library validates byte bounds;
    /// this operation only offsets the shared view.
    pub(super) fn lower_intrinsic_string_slice(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let value = self
            .eval_operand(body, locals, &args[0])?
            .expect("slice string borrow");
        let address = self.reference_data(value);
        let start = self
            .eval_operand(body, locals, &args[1])?
            .expect("slice start")
            .into_int_value();
        let count = self
            .eval_operand(body, locals, &args[2])?
            .expect("slice count")
            .into_int_value();
        let header = string_header_ty(self.context, &self.target_data);
        let source = self
            .builder
            .build_load(header, address, "slice_source")
            .unwrap()
            .into_struct_value();
        let data = self
            .builder
            .build_extract_value(source, 0, "slice_data")
            .unwrap()
            .into_pointer_value();
        let data = unsafe {
            self.builder
                .build_gep(self.context.i8_type(), data, &[start], "slice_offset")
                .unwrap()
        };
        let result = self
            .builder
            .build_insert_value(source, data, 0, "slice_result")
            .unwrap();
        let result = self
            .builder
            .build_insert_value(result, count, 1, "slice_length")
            .unwrap()
            .into_struct_value();
        self.store_place(destination, body, locals, result.into())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn blocking_declarations_and_string_aliases_use_the_borrowed_native_wire() {
        crate::test_support::analyze_script(
            r#"type Text = string;
extern "blocking" { func native_env(_ name: Text, _ value: string) -> int32; }
func main() {}"#,
            |package, gcx| {
                let context = Context::create();
                let module = context.create_module("blocking-string-wire");
                let mut emitter = Emitter::new(&context, module, context.create_builder(), gcx)
                    .unwrap_or_else(|_| panic!("blocking emitter"));
                let declaration = package
                    .root
                    .declarations
                    .iter()
                    .find(|item| gcx.symbol_text(item.identifier.symbol).as_str() == "native_env")
                    .unwrap();
                let facade = emitter.declare_foreign_function(declaration.id);
                assert_eq!(facade.get_name().to_str().unwrap(), "native_env");
                for parameter in facade.get_type().get_param_types() {
                    assert_eq!(parameter.into_struct_type().count_fields(), 2);
                }
                let native = emitter.module.get_function("native_env").unwrap();
                for parameter in native.get_type().get_param_types() {
                    assert_eq!(
                        parameter.into_struct_type().count_fields(),
                        2,
                        "blocking native services borrow data/length, never an owning header"
                    );
                }
                emitter.module.verify().unwrap();
            },
        );
    }
    #[test]
    fn foreign_references_use_the_gc_pointer_wire_directly() {
        crate::test_support::analyze_script(
            "extern \"C\" { unsafe func reference_echo(_ value: &int32) -> &int32; }\nfunc main() {}",
            |package, gcx| {
                let context = Context::create();
                let module = context.create_module("foreign-reference-wire");
                let mut emitter = Emitter::new(&context, module, context.create_builder(), gcx)
                    .unwrap_or_else(|_| panic!("foreign reference emitter"));
                let declaration = package
                    .root
                    .declarations
                    .iter()
                    .find(|item| gcx.symbol_text(item.identifier.symbol).as_str() == "reference_echo")
                    .unwrap();
                let function = emitter.declare_foreign_function(declaration.id);
                let pointer = context.ptr_type(AddressSpace::default());
                assert_eq!(function.get_name().to_str().unwrap(), "reference_echo");
                assert_eq!(function.get_type().get_param_types(), [pointer.into()]);
                assert_eq!(function.get_type().get_return_type(), Some(pointer.into()));
                assert_eq!(function.count_basic_blocks(), 0);
                assert!(
                    !emitter
                        .module
                        .print_to_string()
                        .to_string()
                        .contains("__rt__borrow_")
                );
                emitter.module.verify().unwrap();
            },
        );
    }
}
