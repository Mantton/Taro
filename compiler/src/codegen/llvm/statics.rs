//! Lazy publication of process-long static storage.
//! Initializer callbacks forward into the typed value constructors. No source value
//! can observe zero/partially initialized storage, even on failure or recursion.
use super::*;

impl<'llvm, 'gcx> Emitter<'llvm, 'gcx> {
    fn static_state(&self, storage: hir::DefinitionID) -> PointerValue<'llvm> {
        let name = format!("{}__init_state", mangle(self.gcx, storage));
        self.module
            .get_global(&name)
            .unwrap_or_else(|| {
                let global = self.module.add_global(
                    self.context.ptr_type(AddressSpace::default()),
                    None,
                    &name,
                );
                global.set_linkage(Linkage::LinkOnceODR);
                global
                    .set_initializer(&self.context.ptr_type(AddressSpace::default()).const_null());
                global
            })
            .as_pointer_value()
    }

    fn static_callback(&mut self, storage: hir::DefinitionID) -> FunctionValue<'llvm> {
        let name = format!("{}__initialize", mangle(self.gcx, storage));
        if let Some(function) = self.module.get_function(&name) {
            return function;
        }
        let ptr = self.context.ptr_type(AddressSpace::default());
        let function = self.module.add_function(
            &name,
            self.context.void_type().fn_type(&[ptr.into()], false),
            Some(Linkage::LinkOnceODR),
        );
        self.preserve_diagnostic_frame(function);
        let builder = self.context.create_builder();
        builder.position_at_end(self.context.append_basic_block(function, "initialize"));
        let id = self.gcx.static_initializer_function(storage);
        let (target, abi) =
            self.instance_function_with_abi(Instance::item(id, GenericArguments::empty()));
        let data = function.get_first_param().unwrap().into_pointer_value();
        let mut arguments = Vec::new();
        if matches!(abi.ret.mode, abi::PassMode::Indirect { .. }) {
            arguments.push(data.into());
        }
        // This callback has no owners or local references before the typed
        // callee enters; preserve its forwarding frame for caller stack maps.
        let result = builder
            .build_call(target, &arguments, "initialized_value")
            .unwrap();
        if matches!(abi.ret.mode, abi::PassMode::Direct) {
            builder
                .build_store(data, result.try_as_basic_value().basic().unwrap())
                .unwrap();
        }
        builder.build_return(None).unwrap();
        function
    }

    pub(super) fn try_lower_static_reference(
        &mut self,
        body: &mir::Body<'gcx>,
        locals: &mut [LocalStorage<'llvm>],
        function: &Operand<'gcx>,
        destination: &Place<'gcx>,
        normal: BasicBlock<'llvm>,
        unwind: Option<BasicBlock<'llvm>>,
        span: crate::span::Span,
    ) -> CompileResult<bool> {
        let Operand::Constant(mir::Constant {
            value: mir::ConstantKind::Function(id, ..),
            ..
        }) = function
        else {
            return Ok(false);
        };
        let Some(storage) = crate::sema::lowering::statics::referenced_storage(self.gcx, *id)
        else {
            return Ok(false);
        };
        let ptr = self.context.ptr_type(AddressSpace::default());
        let data = self.global_variable_address(storage);
        let state = self.static_state(storage);
        let initialize = self
            .static_callback(storage)
            .as_global_value()
            .as_pointer_value();
        let source = self.source_descriptor(&self.builder, span);
        let runtime = self
            .module
            .get_function("__rt__static_initialize")
            .unwrap_or_else(|| {
                self.module.add_function(
                    "__rt__static_initialize",
                    self.context
                        .void_type()
                        .fn_type(&[ptr.into(), ptr.into(), ptr.into(), ptr.into()], false),
                    Some(Linkage::External),
                )
            });
        self.emit_source_typed_gc_stack_map(span, StackMapSiteKind::Call);
        self.emit_call_maybe_unwind(
            CallTarget::Direct(runtime),
            &[state.into(), data.into(), initialize.into(), source.into()],
            unwind,
            "static_initialize",
        )?;
        {
            // A GC reference to an initialized static is its address; there
            // is no access control.
            self.store_place(destination, body, locals, data.into())?;
            self.builder.build_unconditional_branch(normal).unwrap();
            return Ok(true);
        }
    }
}
