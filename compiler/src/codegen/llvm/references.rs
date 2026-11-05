//! GC references carry the referent address; static initialization also records
//! a source location for recursive-initializer diagnostics.
use super::*;
impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn lexical_reference(&self, data: PointerValue<'llvm>) -> BasicValueEnum<'llvm> {
        data.into()
    }
    pub(super) fn reference_data(&self, value: BasicValueEnum<'llvm>) -> PointerValue<'llvm> {
        value.into_pointer_value()
    }
    pub(super) fn source_descriptor(
        &self,
        builder: &Builder<'llvm>,
        span: crate::span::Span,
    ) -> PointerValue<'llvm> {
        let pointer = self.context.ptr_type(AddressSpace::default());
        let file = self
            .gcx
            .dcx()
            .file_path(span.file)
            .map(|path| path.to_string_lossy().into_owned())
            .unwrap_or_else(|| "<runtime declaration>".to_owned());
        let file_data = builder
            .build_global_string_ptr(&file, "runtime_source_file")
            .unwrap();
        let source_ty = self.context.struct_type(
            &[
                pointer.into(),
                self.usize_ty.into(),
                self.context.i32_type().into(),
                self.context.i32_type().into(),
            ],
            false,
        );
        let source_value = source_ty.const_named_struct(&[
            file_data.as_pointer_value().into(),
            self.usize_ty.const_int(file.len() as u64, false).into(),
            self.context
                .i32_type()
                .const_int((span.start.line + 1) as u64, false)
                .into(),
            self.context
                .i32_type()
                .const_int((span.start.offset + 1) as u64, false)
                .into(),
        ]);
        let source_global = self.module.add_global(source_ty, None, "runtime_source");
        source_global.set_initializer(&source_value);
        source_global.set_constant(true);
        source_global.set_linkage(Linkage::Private);
        source_global.as_pointer_value()
    }
}
