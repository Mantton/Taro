use super::package::Actor;

impl Actor<'_> {
    pub fn lower_function(&mut self, func: taroc_ast::Function) -> taroc_hir::Function {
        taroc_hir::Function {
            generics: self.lower_generics(func.generics),
            signature: self.lower_function_signature(func.signature),
            block: self.lower_optional(func.block, |a, b| a.lower_block(b)),
        }
    }

    fn lower_function_signature(
        &mut self,
        sg: taroc_ast::FunctionSignature,
    ) -> taroc_hir::FunctionSignature {
        taroc_hir::FunctionSignature {
            span: sg.span,
            prototype: self.lower_function_prototype(sg.prototype),
            is_async: sg.is_async,
        }
    }

    fn lower_function_prototype(
        &mut self,
        pt: taroc_ast::FunctionPrototype,
    ) -> taroc_hir::FunctionPrototype {
        taroc_hir::FunctionPrototype {
            inputs: self.lower_sequence(pt.inputs, |a, p| a.lower_function_parameter(p)),
            output: self.lower_optional(pt.output, |a, ty| a.lower_type(ty)),
        }
    }

    fn lower_function_parameter(
        &mut self,
        param: taroc_ast::FunctionParameter,
    ) -> taroc_hir::FunctionParameter {
        taroc_hir::FunctionParameter {
            id: self.next(),
            attributes: self.lower_attributes(param.attributes),
            label: self.lower_optional(param.label, |a, label| a.lower_label(label)),
            name: param.name.clone(),
            annotated_type: self.lower_type(param.annotated_type),
            default_value: self
                .lower_optional(param.default_value, |a, expr| a.lower_expression(expr)),
            is_variadic: param.is_variadic,
            span: param.span,
        }
    }
}

impl Actor<'_> {
    pub fn lower_label(&mut self, label: taroc_ast::Label) -> taroc_hir::Label {
        taroc_hir::Label {
            identifier: label.identifier.clone(),
            span: label.span,
        }
    }
}
