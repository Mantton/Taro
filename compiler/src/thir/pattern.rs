use crate::{
    compile::context::GlobalContext,
    hir,
    thir::{FieldPattern, Pattern, PatternKind},
};

pub fn pattern_from_hir<'ctx>(gcx: GlobalContext<'ctx>, pattern: &hir::Pattern) -> Pattern<'ctx> {
    let mut ctx = PatternLoweringContext { gcx };
    ctx.lower_pattern(pattern)
}

struct PatternLoweringContext<'ctx> {
    gcx: GlobalContext<'ctx>,
}

impl<'ctx> PatternLoweringContext<'ctx> {
    fn lower_pattern(&mut self, pattern: &hir::Pattern) -> Pattern<'ctx> {
        self.lower_pattern_unadjusted(pattern)
    }

    fn lower_pattern_unadjusted(&mut self, pattern: &hir::Pattern) -> Pattern<'ctx> {
        let ty = self.gcx.get_node_type(pattern.id);
        let span = pattern.span;

        let kind = match &pattern.kind {
            hir::PatternKind::Wildcard => PatternKind::Wild,
            hir::PatternKind::Identifier(name) => PatternKind::Binding {
                name: name.symbol,
                local: pattern.id,
                ty,
                mutable: false,
            },
            hir::PatternKind::Tuple(pats, _) => {
                let subpatterns = pats
                    .iter()
                    .enumerate()
                    .map(|(index, p)| FieldPattern {
                        index,
                        pattern: self.lower_pattern(p),
                    })
                    .collect();
                PatternKind::Leaf { subpatterns }
            }
            _ => unimplemented!(
                "Pattern lowering for {:?} not implemented yet",
                pattern.kind
            ),
        };

        Pattern { ty, span, kind }
    }
}
