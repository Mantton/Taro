use taroc_hir::DefinitionID;

use crate::{
    check::context::func::FnCtx,
    ty::{Ty, TyKind},
    utils::{instantiate_ty_with_args, labeled_signature_to_ty},
};

impl<'rcx, 'ctx> FnCtx<'rcx, 'ctx> {
    pub fn resolve_overloaded_function(
        &self,
        candidates: &[taroc_hir::DefinitionID],
        args: &[taroc_hir::ExpressionArgument],
        expected_return_ty: Option<Ty<'ctx>>,
        call_expr: &taroc_hir::Expression,
        check_labels: bool,
    ) -> Ty<'ctx> {
        for candidate in candidates {
            let result = self.evaluate_function_overload_candidate(
                *candidate,
                args,
                call_expr,
                expected_return_ty,
                check_labels,
            );

            match result {
                Ok(_) => println!("Valid Candidate"),
                Err(_) => println!("Invalid Candidate"),
            }
        }

        return self.error_ty();
    }

    fn evaluate_function_overload_candidate(
        &self,
        fn_id: DefinitionID,
        args: &[taroc_hir::ExpressionArgument],
        call_expr: &taroc_hir::Expression,
        expected_return_ty: Option<Ty<'ctx>>,
        check_labels: bool,
    ) -> Result<(), ()> {
        let signature = self.gcx.fn_signature(fn_id);
        let instantiated_args = self.fresh_args_for_def(fn_id, call_expr.span);
        let fn_signature_ty = labeled_signature_to_ty(signature, self.gcx);
        let fn_signature_ty =
            instantiate_ty_with_args(self.gcx, fn_signature_ty, instantiated_args);

        let (signature_inputs, signature_output) = match fn_signature_ty.kind() {
            TyKind::Function { inputs, output, .. } => (inputs, output),
            _ => unreachable!("non function type"),
        };

        // Arguments, TODO: Variadic
        let candidate_parameter_count = signature.inputs.len();
        let min_parameter_count = signature.min_parameter_count();
        let provided_argument_count = args.len();
        let is_valid_argument_count = (min_parameter_count..=candidate_parameter_count)
            .contains(&provided_argument_count)
            || (signature.is_variadic && provided_argument_count >= min_parameter_count);

        if !is_valid_argument_count {
            return Err(()); // Arity Mismatch
        }

        let mut arg_index = 0;
        for (index, parameter) in signature.inputs.iter().enumerate() {
            let is_last = index == signature.inputs.len() - 1;
            let parameter_ty = signature_inputs[index];

            // is variadic
            if is_last && signature.is_variadic {
            } else if arg_index < args.len() {
                let argument = &args[arg_index];

                // Labels
                if check_labels {
                    if parameter.label != argument.label.as_ref().map(|f| f.identifier.symbol) {
                        return Err(()); // Label Mismatch
                    }
                    // TODO: Check labels
                }

                let arg_ty = self.check_expression(&argument.expression);
                println!(
                    "Provided: {}\nExpected: {}\n",
                    arg_ty.format(self.gcx),
                    parameter_ty.format(self.gcx)
                );

                let coercion_result = self.coerce(&argument.expression, arg_ty, parameter_ty);

                match coercion_result {
                    Ok(_) => {}
                    Err(_) => return Err(()),
                }

                arg_index += 1;
            } else if parameter.has_default {
                continue; // parameter has default value, skip
            } else {
                return Err(()); // required parameter but no arugment provided
            }
        }

        if arg_index < args.len() {
            unreachable!("ICE: Bad Logic")
        }

        if let Some(expected_ret_ty) = expected_return_ty {
            let coercion_result = self.coerce(call_expr, signature_output, expected_ret_ty);

            match coercion_result {
                Ok(_) => {}
                Err(_) => return Err(()),
            }
        }

        return Ok(());
    }
}
