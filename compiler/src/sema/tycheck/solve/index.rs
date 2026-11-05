//! Native subscripts use ordinary restricted method selection. Reads select
//! the getter; the checker validates the chosen declaration's other capabilities.
use super::{ConstraintSolver, IndexAccessGoalData, MethodCallData, SolverResult};
use crate::sema::error::TypeError;

impl<'ctx> ConstraintSolver<'ctx> {
    pub(super) fn solve_index_access(
        &mut self,
        data: IndexAccessGoalData<'ctx>,
    ) -> SolverResult<'ctx> {
        let receiver = self.structurally_resolve(data.receiver);
        if receiver.is_infer() {
            return SolverResult::Deferred;
        }
        if receiver.is_error() || data.keys.iter().any(|key| key.ty.is_error()) {
            return self.solve_equality(data.span, data.output, self.gcx().types.error);
        }
        let access = crate::compile::context::NativeSubscriptAccess::Get;
        let mut result = self.solve_native_subscript_call(
            MethodCallData {
                receiver_addressable: data.receiver_addressable,
                selected: None,
                node_id: data.nodes.call,
                receiver,
                reciever_span: data.span,
                reciever_node: data.nodes.receiver,
                is_unsafe_context: false,
                name: crate::span::Identifier {
                    symbol: self.gcx().intern_symbol(access.method_name()),
                    span: data.span,
                },
                arguments: data.keys,
                result: data.output,
                method_ty: data.method_ty,
                prefer_async: false,
                span: data.span,
            },
            access,
        );
        if let SolverResult::Error(errors) = &mut result {
            for error in errors {
                if let TypeError::NoSuchMember { name, .. } = &mut error.value {
                    *name = self.gcx().intern_symbol("subscript");
                }
            }
        }
        result
    }
}

#[cfg(test)]
mod tests;
