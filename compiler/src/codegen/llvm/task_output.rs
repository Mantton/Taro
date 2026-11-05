//! Layout and tracing metadata for a task result kept in collected storage.
use super::*;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    pub(super) fn lower_intrinsic_task_output_descriptor(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        call_args: GenericArguments<'gcx>,
        args: &[Operand<'gcx>],
        destination: &Place<'gcx>,
    ) -> CompileResult<()> {
        let gcx = self.gcx;
        let diagnostic_span = self
            .current_span
            .or(Some(body.locals[destination.local].span));
        let error = |message: &str| {
            gcx.dcx().emit_error(message.into(), diagnostic_span);
            crate::error::ReportedError
        };
        let Some(crate::sema::models::GenericArgument::Type(ty)) = call_args.get(0) else {
            return Err(error("task output descriptor requires its output type"));
        };
        let ty = self.mono_ty(*ty);
        if !args.is_empty() {
            return Err(error("task output descriptor takes no arguments"));
        }
        let descriptor = self.gc_descriptor_for(ty);
        self.store_place(destination, body, locals, descriptor.into())
    }
}
