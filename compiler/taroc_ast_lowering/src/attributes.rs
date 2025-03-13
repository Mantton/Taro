use super::package::Actor;

impl Actor<'_> {
    pub fn lower_attributes(
        &mut self,
        attributes: taroc_ast::AttributeList,
    ) -> taroc_hir::AttributeList {
        attributes
            .into_iter()
            .map(|attr| self.lower_attribute(attr))
            .collect()
    }
    pub fn lower_attribute(&mut self, attribute: taroc_ast::Attribute) -> taroc_hir::Attribute {
        taroc_hir::Attribute {
            identifier: attribute.identifier,
        }
    }
}
