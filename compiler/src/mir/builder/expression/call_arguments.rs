//! Argument evaluation and ABI arrangement are separate operations. Hoist a
//! reordered call's values once, then let ordinary/native lowering consume the
//! prepared values in parameter order. The scope is a lowering override, not a
//! new source cleanup scope; nested calls restore the enclosing override.
use crate::{
    mir::{BasicBlockId, BlockAnd, Operand, Place, builder::MirBuilder},
    span::Span,
    thir::{ExprId, ExprKind},
    unpack,
};

impl<'ctx, 'thir> MirBuilder<'ctx, 'thir> {
    pub(super) fn prepared_argument_operand(
        &mut self,
        _block: BasicBlockId,
        expression: ExprId,
    ) -> Option<Operand<'ctx>> {
        let place = self.prepared_call_arguments.get(&expression)?.clone();
        Some(Operand::Copy(place))
    }

    pub(super) fn with_call_arguments_in_order(
        &mut self,
        mut block: BasicBlockId,
        args: &[ExprId],
        order: Option<&[usize]>,
        lower: impl FnOnce(&mut Self, BasicBlockId) -> BlockAnd<()>,
    ) -> BlockAnd<()> {
        let Some(order) = order else {
            return lower(self, block);
        };
        assert_eq!(
            order.len(),
            args.len(),
            "call evaluation must visit every argument"
        );
        let mut visited = vec![false; args.len()];
        let saved = self.prepared_call_arguments.clone();
        for &index in order {
            let seen = visited
                .get_mut(index)
                .expect("call evaluation argument index");
            assert!(!*seen, "call argument evaluated more than once");
            *seen = true;
            let local = unpack!(block = self.as_temp(block, args[index]));
            // Later default expressions may borrow an earlier prepared value
            // to select its hidden concrete type. Expose each snapshot now,
            // without re-evaluating or moving its source expression again.
            self.prepared_call_arguments
                .insert(args[index], Place::from_local(local));
        }
        let result = lower(self, block);
        self.prepared_call_arguments = saved;
        result
    }

    pub(super) fn lower_ordered_call_into_dest(
        &mut self,
        destination: Place<'ctx>,
        block: BasicBlockId,
        callee: ExprId,
        args: &[ExprId],
        order: Option<&[usize]>,
        is_async: bool,
        span: Span,
    ) -> BlockAnd<()> {
        if order.is_some() {
            // Only statically resolved calls carry label/default arrangement.
            // Their function constant has no effects before receiver/arguments.
            // Dynamic callable evaluation keeps its existing ordinary path.
            assert!(
                matches!(self.thir.exprs[callee].kind, ExprKind::Zst { .. }),
                "reordered call must resolve its callee before argument lowering"
            );
        }
        self.with_call_arguments_in_order(block, args, order, |this, block| {
            this.lower_call_into_dest(destination, block, callee, args, is_async, span)
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        compile::context::Gcx,
        hir::DefinitionID,
        mir::{Constant, ConstantKind, Operand, TerminatorKind},
    };

    fn entry_calls(gcx: Gcx<'_>) -> Vec<DefinitionID> {
        let module = gcx
            .store
            .inline_mir_packages
            .borrow()
            .get(&gcx.package_index())
            .copied()
            .unwrap();
        let body = module.functions.get(&module.entry.unwrap()).unwrap();
        let mut block = body.start_block;
        let mut seen = rustc_hash::FxHashSet::default();
        let mut result = Vec::new();
        loop {
            assert!(seen.insert(block), "linear fixture has a CFG cycle");
            match &body.basic_blocks[block].terminator.as_ref().unwrap().kind {
                TerminatorKind::Call {
                    func:
                        Operand::Constant(Constant {
                            value: ConstantKind::Function(id, ..),
                            ..
                        }),
                    target,
                    ..
                } => {
                    result.push(*id);
                    block = *target;
                }
                TerminatorKind::Goto { target } => block = *target,
                TerminatorKind::Return => break,
                other => panic!("unexpected linear fixture terminator: {other:?}"),
            }
        }
        result
    }

    #[test]
    fn named_calls_evaluate_supplied_arguments_in_source_order() {
        crate::test_support::check_script(
            "func left() -> int32 { 3 }\nfunc right() -> int32 { 7 }\nfunc pair(left: int32, right: int32) -> int32 { left + right }\nfunc main() { result := pair(right: right(), left: left()) }",
            |_, gcx| {
                let calls: Vec<_> = entry_calls(gcx)
                    .into_iter()
                    .map(|id| gcx.definition_ident(id).symbol.as_str().to_string())
                    .collect();
                assert_eq!(calls, ["right", "left", "pair"]);
            },
        );
    }

    #[test]
    fn omitted_defaults_run_after_supplied_arguments_in_declaration_order() {
        crate::test_support::check_script(
            "func left() -> int32 { 3 }\nfunc right() -> int32 { 7 }\nfunc defaultValue() -> int32 { 9 }\nfunc triple(first: int32 = defaultValue(), middle: int32, last: int32) -> int32 { first + middle + last }\nfunc main() { result := triple(last: right(), middle: left()) }",
            |package, gcx| {
                let find = |name: &str| {
                    package
                        .root
                        .declarations
                        .iter()
                        .find(|declaration| declaration.identifier.symbol.as_str() == name)
                        .unwrap()
                        .id
                };
                let triple = find("triple");
                let provider = gcx.get_signature(triple).inputs[0]
                    .default_provider
                    .unwrap();
                assert_eq!(
                    entry_calls(gcx),
                    [find("right"), find("left"), provider, triple]
                );
            },
        );
    }
}
