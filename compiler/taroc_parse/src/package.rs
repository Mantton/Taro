use super::restrictions::Restrictions;
use std::{collections::VecDeque, vec};
use taroc_ast::Declaration;
use taroc_error::{CompileError, CompileResult};
use taroc_sema::{GlobalContext, WithDiagnostics};
use taroc_span::SpannedMessage;

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
    let mut submodules = vec![];

    for file in module.files {
        let file = parse_file(file, context);
        files.push(file);
    }

    for module in module.submodules {
        let module = parse_module(module, context);
        submodules.push(module);
    }

    taroc_ast::Module {
        name,
        files,
        submodules,
    }
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
    pub angle_depth: usize, //  how many '<' are currently open?
}

impl Parser {
    pub fn new(file: taroc_lexer::File) -> Parser {
        Parser {
            file,
            cursor: 0,
            restrictions: Restrictions::empty(),
            anchors: VecDeque::new(),
            result: Default::default(),
            angle_depth: 0,
        }
    }
}

impl Parser {
    pub fn parse(mut self) -> ParserResult {
        let result = self.parse_module_declarations();
        match result {
            Err(err) => self.result.error(err),
            Ok(data) => self.result.value = data,
        }
        self.result
    }
}

#[macro_export]
macro_rules! make_parser {
    ($content:expr) => {{
        let id = taroc_span::register_test_file!($content);
        $crate::make_parser!($content, id)
    }};
    ($content:expr, $id:expr) => {{
        let lexer = taroc_lexer::Lexer::new($content.into(), $id);
        let file = lexer.tokenize().expect("tokens");
        $crate::package::Parser::new(file)
    }};
}
