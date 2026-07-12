use crate::{
    compile::{config::BuildProfile, context::GlobalContext},
    mir,
    span::{FileID, Span},
};
use inkwell::{
    context::Context,
    debug_info::{
        AsDIScope, DICompileUnit, DIFile, DIFlags, DIFlagsConstants, DILexicalBlock, DISubprogram,
        DWARFEmissionKind, DWARFSourceLanguage, DebugInfoBuilder, debug_metadata_version,
    },
    module::{FlagBehavior, Module},
    values::FunctionValue,
};
use rustc_hash::FxHashMap;
use std::path::{Path, PathBuf};

/// Line-table-only debug state for one LLVM module.
pub(super) struct DebugContext<'llvm> {
    builder: DebugInfoBuilder<'llvm>,
    compile_unit: DICompileUnit<'llvm>,
    files: FxHashMap<FileID, DIFile<'llvm>>,
    current_function: Option<FunctionDebugState<'llvm>>,
}

struct FunctionDebugState<'llvm> {
    subprogram: DISubprogram<'llvm>,
    primary_file: FileID,
    alternate_file_scopes: FxHashMap<FileID, DILexicalBlock<'llvm>>,
}

impl<'llvm> DebugContext<'llvm> {
    pub(super) fn new(
        context: &'llvm Context,
        module: &Module<'llvm>,
        gcx: GlobalContext<'_>,
    ) -> Self {
        module.add_basic_value_flag(
            "Debug Info Version",
            FlagBehavior::Warning,
            context
                .i32_type()
                .const_int(debug_metadata_version() as u64, false),
        );
        // DWARF v4 is understood by the deployment targets supported by Taro
        // and avoids relying on a platform-specific LLVM default.
        module.add_basic_value_flag(
            "Dwarf Version",
            FlagBehavior::Warning,
            context.i32_type().const_int(4, false),
        );

        let mappings = gcx.dcx().all_file_mappings();
        // Dependency metadata may register files before the package currently
        // being emitted. Prefer a file inside this package so the compile-unit
        // identity does not accidentally point at std or another dependency.
        let default_mapping = mappings
            .iter()
            .find(|(_, path)| path == &gcx.config.src || path.starts_with(&gcx.config.src))
            .cloned();
        let default_path = default_mapping
            .as_ref()
            .map(|(_, path)| path.clone())
            .unwrap_or_else(|| gcx.config.src.clone());
        let (filename, directory) = debug_path_parts(&default_path);
        let (builder, compile_unit) = module.create_debug_info_builder(
            true,
            DWARFSourceLanguage::Rust,
            &filename,
            &directory,
            "Taro compiler",
            matches!(gcx.config.profile, BuildProfile::Release),
            "",
            0,
            "",
            DWARFEmissionKind::LineTablesOnly,
            0,
            false,
            false,
            "",
            "",
        );

        let mut files = FxHashMap::default();
        if let Some((file_id, _)) = default_mapping {
            files.insert(file_id, compile_unit.get_file());
        }

        Self {
            builder,
            compile_unit,
            files,
            current_function: None,
        }
    }

    pub(super) fn begin_function(
        &mut self,
        function: FunctionValue<'llvm>,
        body: &mir::Body<'_>,
        gcx: GlobalContext<'_>,
    ) {
        let ident = gcx.try_definition_ident(body.owner);
        let span = ident
            .map(|ident| ident.span)
            .unwrap_or_else(|| body_source_span(body));
        let file = self.file_for(gcx, span.file);
        let line = dwarf_coordinate(span.start.line);
        let name = ident
            .map(|ident| gcx.symbol_text(ident.symbol))
            .unwrap_or_else(|| {
                gcx.definition_symbol_or_fallback(body.owner)
                    .as_str()
                    .into()
            });
        let linkage_name = function.get_name().to_string_lossy();
        let function_type = self
            .builder
            .create_subroutine_type(file, None, &[], DIFlags::ZERO);
        let subprogram = self.builder.create_function(
            self.compile_unit.as_debug_info_scope(),
            &name,
            Some(&linkage_name),
            file,
            line,
            function_type,
            false,
            true,
            line,
            DIFlags::ZERO,
            matches!(gcx.config.profile, BuildProfile::Release),
        );
        function.set_subprogram(subprogram);
        self.current_function = Some(FunctionDebugState {
            subprogram,
            primary_file: span.file,
            alternate_file_scopes: FxHashMap::default(),
        });
    }

    pub(super) fn set_location(
        &mut self,
        context: &'llvm Context,
        llvm_builder: &inkwell::builder::Builder<'llvm>,
        gcx: GlobalContext<'_>,
        span: Span,
    ) {
        let file = self.file_for(gcx, span.file);
        let Some(function) = self.current_function.as_mut() else {
            llvm_builder.unset_current_debug_location();
            return;
        };
        let scope = if span.file == function.primary_file {
            function.subprogram.as_debug_info_scope()
        } else {
            function
                .alternate_file_scopes
                .entry(span.file)
                .or_insert_with(|| {
                    self.builder.create_lexical_block(
                        function.subprogram.as_debug_info_scope(),
                        file,
                        dwarf_coordinate(span.start.line),
                        dwarf_coordinate(span.start.offset),
                    )
                })
                .as_debug_info_scope()
        };
        let location = self.builder.create_debug_location(
            context,
            dwarf_coordinate(span.start.line),
            dwarf_coordinate(span.start.offset),
            scope,
            None,
        );
        llvm_builder.set_current_debug_location(location);
    }

    pub(super) fn end_function(&mut self, llvm_builder: &inkwell::builder::Builder<'llvm>) {
        llvm_builder.unset_current_debug_location();
        self.current_function = None;
    }

    pub(super) fn finalize(&self) {
        self.builder.finalize();
    }

    fn file_for(&mut self, gcx: GlobalContext<'_>, file_id: FileID) -> DIFile<'llvm> {
        if let Some(file) = self.files.get(&file_id) {
            return *file;
        }
        let path = gcx
            .dcx()
            .file_path(file_id)
            .unwrap_or_else(|| PathBuf::from("<unknown>"));
        let (filename, directory) = debug_path_parts(&path);
        let file = self.builder.create_file(&filename, &directory);
        self.files.insert(file_id, file);
        file
    }
}

fn body_source_span(body: &mir::Body<'_>) -> Span {
    body.basic_blocks
        .iter()
        .flat_map(|block| block.statements.iter().map(|statement| statement.span))
        .next()
        .or_else(|| {
            body.basic_blocks
                .iter()
                .find_map(|block| block.terminator.as_ref().map(|terminator| terminator.span))
        })
        .unwrap_or(body.locals[body.return_local].span)
}

fn debug_path_parts(path: &Path) -> (String, String) {
    let filename = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("<unknown>")
        .to_owned();
    let directory = path
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
        .to_string_lossy()
        .into_owned();
    (filename, directory)
}

fn dwarf_coordinate(zero_based: usize) -> u32 {
    zero_based.saturating_add(1).min(u32::MAX as usize) as u32
}

#[cfg(test)]
mod tests {
    use super::{DebugContext, debug_path_parts, dwarf_coordinate};
    use crate::{
        mir::test_support::{minimal_body, with_test_gcx},
        span::Span,
    };
    use inkwell::context::Context;
    use std::path::Path;

    #[test]
    fn splits_debug_paths_for_dwarf_files() {
        assert_eq!(
            debug_path_parts(Path::new("/tmp/src/main.tr")),
            ("main.tr".to_owned(), "/tmp/src".to_owned())
        );
        assert_eq!(
            debug_path_parts(Path::new("main.tr")),
            ("main.tr".to_owned(), ".".to_owned())
        );
    }

    #[test]
    fn converts_and_clamps_source_coordinates() {
        assert_eq!(dwarf_coordinate(0), 1);
        assert_eq!(dwarf_coordinate(usize::MAX), u32::MAX);
    }

    #[test]
    fn emits_compile_unit_function_and_line_metadata() {
        with_test_gcx(|gcx| {
            let context = Context::create();
            let module = context.create_module("debug-test");
            let builder = context.create_builder();
            let mut debug = DebugContext::new(&context, &module, gcx);
            let body = minimal_body(gcx);
            let function = module.add_function(
                "_Tdebug_test",
                context.void_type().fn_type(&[], false),
                None,
            );
            let block = context.append_basic_block(function, "entry");
            builder.position_at_end(block);

            debug.begin_function(function, &body, gcx);
            debug.set_location(
                &context,
                &builder,
                gcx,
                Span::empty(body.locals[0].span.file),
            );
            builder.build_return(None).unwrap();
            debug.end_function(&builder);
            debug.finalize();

            module.verify().expect("debug module should verify");
            let ir = module.print_to_string().to_string();
            assert!(ir.contains("!DICompileUnit(language: DW_LANG_Rust"));
            assert!(ir.contains("!DISubprogram(name:"));
            assert!(ir.contains("!DILocation(line: 1, column: 1"));
        });
    }
}
