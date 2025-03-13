use super::package::Actor;

impl Actor<'_> {
    pub fn lower_sequence<T, F, V>(&mut self, items: Vec<T>, mut action: F) -> Vec<V>
    where
        F: FnMut(&mut Actor, T) -> V,
    {
        let mut result = Vec::new();
        for item in items.into_iter() {
            let value = action(self, item);
            result.push(value);
        }

        return result;
    }

    pub fn lower_optional<T, F, V>(&mut self, item: Option<T>, mut action: F) -> Option<V>
    where
        F: FnMut(&mut Actor, T) -> V,
    {
        if let Some(item) = item {
            return Some(action(self, item));
        } else {
            None
        }
    }

    pub fn lower_visibility(&mut self, node: taroc_ast::Visibility) -> taroc_hir::Visibility {
        taroc_hir::Visibility {
            span: node.span,
            level: taroc_hir::VisibilityLevel::Public,
        }
    }
}
