use taroc_ast::{DeclarationKind, ModuleKind};
use taroc_context::GlobalContext;
use taroc_error::{CompileError, CompileResult};
use taroc_lexer::tokenize_module;
use taroc_parse::parse_module;
use taroc_span::{Identifier, with_session_globals};

pub fn run(package: &mut taroc_ast::Package, context: GlobalContext) -> CompileResult<()> {
    expand_module(&mut package.root, context)
}

fn expand_module(module: &mut taroc_ast::Module, context: GlobalContext) -> CompileResult<()> {
    let mut any_failure = false;

    for file in module.files.iter_mut() {
        let x = expand_file(file, context);
        if x {
            any_failure = true;
        }
    }

    if any_failure {
        return Err(CompileError::Reported);
    }

    context.diagnostics.report()
}

fn expand_file(file: &mut taroc_ast::File, context: GlobalContext) -> bool {
    let mut any_failure = false;

    for decl in file.declarations.iter_mut() {
        match &mut decl.kind {
            DeclarationKind::Module(kind) => match kind {
                ModuleKind::Unloaded => {
                    let module = perform_expansion(decl.identifier, context);

                    let module = if let Some(module) = module {
                        module
                    } else {
                        any_failure = true;
                        taroc_ast::Module {
                            files: vec![],
                            name: decl.identifier.symbol,
                        }
                    };

                    *kind = ModuleKind::Loaded(module);
                }
                _ => {}
            },
            _ => {}
        }
    }

    return any_failure;
}

fn perform_expansion(ident: Identifier, context: GlobalContext) -> Option<taroc_ast::Module> {
    let file = with_session_globals(|session| session.get_file(ident.span.file));
    // Directory Path
    let path = file
        .path()
        .parent()
        .map(|path| path.join(ident.symbol.as_str()));
    let Some(path) = path else {
        unreachable!("file path must always resolve to a parent")
    };

    let path = match path.canonicalize() {
        Ok(path) => path,
        Err(err) => {
            let message = format!("failed to resolve path '{:?}', {}", path, err);
            context.diagnostics.error(message, ident.span);
            return None;
        }
    };

    if !path.exists() || !path.is_dir() {
        let message = format!(
            "failed to resolve directory path, path does not exist or is not a directory '{:?}'",
            path
        );
        context.diagnostics.error(message, ident.span);
        return None;
    }

    // Stage 2: Tokenize
    let package = tokenize_module(&path, false, context);
    let package = match package {
        Ok(tokenized) => tokenized,
        Err(CompileError::Reported) => {
            let message = format!("Failed to expand Module '{}'", ident.symbol);
            context.diagnostics.error(message, ident.span);
            return None;
        }
        Err(CompileError::Message(e)) => {
            let message = format!("Failed to expand Module '{}', {}", ident.symbol, e);
            context.diagnostics.error(message, ident.span);
            return None;
        }
    };

    // Stage 3: Generate AST
    let mut package = parse_module(package, context);

    if context.diagnostics.has_errors() {
        let message = format!("Failed to expand Module '{}'", ident.symbol);
        context.diagnostics.error(message, ident.span);
        context.diagnostics.reset_errors();
        return None;
    };

    // Stage 4: Populate
    let _ = expand_module(&mut package, context);
    Some(package)
}
