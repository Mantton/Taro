use std::{collections::VecDeque, vec};

use taroc_ast::{Declaration, DeclarationContext};
use taroc_context::{GlobalContext, WithDiagnostics};
use taroc_error::{CompileError, CompileResult};
use taroc_span::SpannedMessage;

use super::restrictions::Restrictions;
pub type R<T> = Result<T, SpannedMessage>;
type ParserResult = WithDiagnostics<Vec<Declaration>>;

pub fn parse_package(
    package: taroc_lexer::Package,
    context: GlobalContext,
) -> CompileResult<taroc_ast::Package> {
    let root = parse_module(package.root, context);
    let package = taroc_ast::Package { root };
    if context.diagnostics.has_errors() {
        Err(CompileError::Reported)
    } else {
        Ok(package)
    }
}

pub fn parse_module(module: taroc_lexer::Module, context: GlobalContext) -> taroc_ast::Module {
    let name = module.name;
    let mut files = vec![];

    for file in module.files {
        let file = parse_file(file, context);
        files.push(file);
    }

    taroc_ast::Module { name, files }
}

pub fn parse_file(file: taroc_lexer::File, context: GlobalContext) -> taroc_ast::File {
    let id = file.file;
    let parser = Parser::new(file);
    let result = parser.parse();
    let declarations = result.export(context);
    taroc_ast::File {
        declarations,
        file: id,
    }
}

pub struct Parser {
    pub file: taroc_lexer::File,
    pub cursor: usize,
    pub restrictions: Restrictions,
    pub anchors: VecDeque<usize>,
    pub result: ParserResult,
}

impl Parser {
    pub fn new(file: taroc_lexer::File) -> Parser {
        Parser {
            file,
            cursor: 0,
            restrictions: Restrictions::empty(),
            anchors: VecDeque::new(),
            result: Default::default(),
        }
    }
}

impl Parser {
    pub fn parse(mut self) -> ParserResult {
        let result = self.top_level();

        match result {
            Err(err) => self.result.error(err),
            _ => {}
        }

        self.result
    }

    fn top_level(&mut self) -> R<()> {
        while !self.is_at_end() {
            let Some(item) = self.parse_declaration(false, DeclarationContext::Module)? else {
                break;
            };
            self.result.value.push(item);
        }

        if !self.is_at_end() {
            let msg = format!(
                "expected top-level declaration, found '{}' instead",
                self.current_kind()
            );
            let err = SpannedMessage::new(msg, self.current_token_span());
            Err(err)
        } else {
            Ok(())
        }
    }
}

#[macro_export]
macro_rules! make_parser {
    ($content:expr) => {{
        let lexer = taroc_lexer::Lexer::new($content.into(), taroc_span::FileID::new(0));
        let file = lexer.tokenize().expect("tokens");
        let parser = $crate::package::Parser::new(file);
        parser
    }};
}
