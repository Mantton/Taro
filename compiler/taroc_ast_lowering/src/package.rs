use taroc_context::GlobalContext;
use taroc_error::CompileResult;
use taroc_hir::{NodeID, NodeTagger};

pub fn run(
    package: taroc_ast::Package,
    context: GlobalContext,
) -> CompileResult<taroc_hir::Package> {
    let mut actor = Actor::new(context);
    let package = actor.lower_package(package);
    context.diagnostics.report()?;
    return Ok(package);
}

pub struct Actor<'ctx> {
    pub tagger: NodeTagger,
    pub context: GlobalContext<'ctx>,
}

impl Actor<'_> {
    fn new<'a>(context: GlobalContext<'a>) -> Actor<'a> {
        Actor {
            tagger: NodeTagger::new(),
            context,
        }
    }

    pub fn next(&mut self) -> NodeID {
        self.tagger.next()
    }
}

impl Actor<'_> {
    pub fn lower_package(&mut self, package: taroc_ast::Package) -> taroc_hir::Package {
        let root = self.lower_module(package.root);
        return taroc_hir::Package { root };
    }

    pub fn lower_module(&mut self, module: taroc_ast::Module) -> taroc_hir::Module {
        let id = self.next();
        let files = module
            .files
            .into_iter()
            .map(|file| self.lower_file(file))
            .collect();

        let submodules = module
            .submodules
            .into_iter()
            .map(|file| self.lower_module(file))
            .collect();

        taroc_hir::Module {
            name: module.name,
            id,
            files,
            submodules,
        }
    }

    pub fn lower_file(&mut self, file: taroc_ast::File) -> taroc_hir::File {
        let declarations = file
            .declarations
            .into_iter()
            .map(|node| self.lower_declaration(node))
            .collect();

        taroc_hir::File {
            declarations,
            id: file.file,
        }
    }
}
