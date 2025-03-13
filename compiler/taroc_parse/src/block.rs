use taroc_ast::{Block, StatementKind};

use super::package::{Parser, R};

impl Parser {
    pub fn parse_block(&mut self) -> R<Block> {
        let lo = self.lo_span();
        let mut has_declarations = false;
        let statements = self.parse_block_sequence(|p| {
            let s = p.parse_statement()?;
            has_declarations = has_declarations || matches!(s.kind, StatementKind::Declaration(..));
            Ok(s)
        })?;

        Ok(Block {
            statements,
            span: lo.to(self.hi_span()),
            has_declarations,
        })
    }
}
