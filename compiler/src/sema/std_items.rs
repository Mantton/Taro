use crate::{
    ast::{self, AttributeArg, Literal},
    compile::context::GlobalContext,
    error::{CompileResult, ReportedError},
    hir::{DefinitionID, DefinitionKind, StdItem},
    sema::resolve::models::{ResolutionOutput, VariantCtorKind},
    span::Span,
};
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, Copy)]
pub struct StdItemEntry {
    pub def_id: DefinitionID,
    pub def_kind: DefinitionKind,
    pub span: Span,
}

#[derive(Debug, Default, Clone)]
pub struct StdItemRegistry {
    items: FxHashMap<StdItem, StdItemEntry>,
}

impl StdItemRegistry {
    pub fn get(&self, item: StdItem) -> Option<StdItemEntry> {
        self.items.get(&item).copied()
    }

    pub fn entries(&self) -> impl Iterator<Item = (StdItem, StdItemEntry)> + '_ {
        self.items.iter().map(|(item, entry)| (*item, *entry))
    }

    pub fn from_entries(entries: impl IntoIterator<Item = (StdItem, StdItemEntry)>) -> Self {
        let mut items = FxHashMap::default();
        for (item, entry) in entries {
            items.insert(item, entry);
        }
        StdItemRegistry { items }
    }

    fn insert(&mut self, gcx: GlobalContext<'_>, item: StdItem, entry: StdItemEntry) -> bool {
        if let Some(existing) = self.items.get(&item) {
            let name = item.name_str().unwrap_or("<unknown>");
            gcx.dcx().emit_error(
                format!("duplicate @lang item '{}'", name).into(),
                Some(entry.span),
            );
            gcx.dcx()
                .emit_info("previously declared here".into(), Some(existing.span));
            return false;
        }
        self.items.insert(item, entry);
        true
    }
}

pub fn collect_std_items(
    package: &ast::Package,
    gcx: GlobalContext<'_>,
    output: &ResolutionOutput<'_>,
) -> CompileResult<Option<StdItemRegistry>> {
    let is_std = gcx.is_std_package(gcx.package_index());
    let mut registry = StdItemRegistry::default();
    let mut had_error = false;

    visit_module(
        &package.root,
        gcx,
        output,
        is_std,
        &mut registry,
        &mut had_error,
    );

    if is_std {
        if let Some(entry) = registry.get(StdItem::Optional) {
            if let Some(enum_decl) = find_enum_by_def_id(package, output, entry.def_id) {
                derive_optional_variants(enum_decl, gcx, output, &mut registry, &mut had_error);
            } else {
                gcx.dcx().emit_error(
                    "unable to locate Optional enum for @lang item".into(),
                    Some(entry.span),
                );
                had_error = true;
            }
        }

        let mut missing = Vec::new();
        for item in StdItem::ALL_REQUIRED {
            if registry.get(item).is_none() {
                let name = item.name_str().unwrap_or("<unknown>");
                missing.push(name);
            }
        }
        if !missing.is_empty() {
            let message = format!(
                "missing required @lang items in std: {}",
                missing.join(", ")
            );
            gcx.dcx().emit_error(message.into(), None);
            had_error = true;
        }
    }

    if had_error {
        return Err(ReportedError);
    }

    if is_std { Ok(Some(registry)) } else { Ok(None) }
}

fn visit_module(
    module: &ast::Module,
    gcx: GlobalContext<'_>,
    output: &ResolutionOutput<'_>,
    is_std: bool,
    registry: &mut StdItemRegistry,
    had_error: &mut bool,
) {
    for file in &module.files {
        for decl in &file.declarations {
            handle_declaration(decl, gcx, output, is_std, registry, had_error);
        }
    }
    for sub in &module.submodules {
        visit_module(sub, gcx, output, is_std, registry, had_error);
    }
}

fn handle_declaration(
    decl: &ast::Declaration,
    gcx: GlobalContext<'_>,
    output: &ResolutionOutput<'_>,
    is_std: bool,
    registry: &mut StdItemRegistry,
    had_error: &mut bool,
) {
    for attr in &decl.attributes {
        let Some(lang_item) = parse_lang_attribute(attr, gcx, is_std, had_error) else {
            continue;
        };

        if !is_std {
            continue;
        }

        let Some(def_id) = output.node_to_definition.get(&decl.id) else {
            gcx.dcx().emit_error(
                "unable to resolve definition for @lang item".into(),
                Some(attr.span),
            );
            *had_error = true;
            continue;
        };
        let Some(def_kind) = output.definition_to_kind.get(def_id) else {
            gcx.dcx().emit_error(
                "unable to resolve definition kind for @lang item".into(),
                Some(attr.span),
            );
            *had_error = true;
            continue;
        };

        if let Some(expected) = lang_item.expected_def_kind() {
            if expected != *def_kind {
                let name = lang_item.name_str().unwrap_or("<unknown>");
                gcx.dcx().emit_error(
                    format!(
                        "@lang item '{}' must be declared as a {}, found {}",
                        name,
                        expected.description(),
                        def_kind.description()
                    )
                    .into(),
                    Some(attr.span),
                );
                *had_error = true;
                continue;
            }
        }

        let entry = StdItemEntry {
            def_id: *def_id,
            def_kind: *def_kind,
            span: attr.span,
        };
        if !registry.insert(gcx, lang_item, entry) {
            *had_error = true;
        }
    }
}

fn parse_lang_attribute(
    attr: &ast::Attribute,
    gcx: GlobalContext<'_>,
    is_std: bool,
    had_error: &mut bool,
) -> Option<StdItem> {
    let name = gcx.symbol_text(attr.identifier.symbol);
    if name.as_ref() != "lang" {
        return None;
    }

    if !is_std {
        gcx.dcx().emit_error(
            "@lang attributes are only allowed in the standard library".into(),
            Some(attr.span),
        );
        *had_error = true;
        return None;
    }

    let Some(args) = attr.args.as_ref() else {
        gcx.dcx().emit_error(
            "@lang expects exactly one string literal argument".into(),
            Some(attr.span),
        );
        *had_error = true;
        return None;
    };

    if args.items.len() != 1 {
        gcx.dcx().emit_error(
            "@lang expects exactly one string literal argument".into(),
            Some(attr.span),
        );
        *had_error = true;
        return None;
    }

    let item_name = match &args.items[0] {
        AttributeArg::Literal { value, .. } => match value {
            Literal::String { value } => value.clone(),
            _ => {
                gcx.dcx()
                    .emit_error("@lang expects a string literal".into(), Some(attr.span));
                *had_error = true;
                return None;
            }
        },
        _ => {
            gcx.dcx()
                .emit_error("@lang expects a string literal".into(), Some(attr.span));
            *had_error = true;
            return None;
        }
    };

    let Some(item) = StdItem::from_name(item_name.as_str()) else {
        gcx.dcx().emit_error(
            format!("unknown @lang item '{}'", item_name).into(),
            Some(attr.span),
        );
        *had_error = true;
        return None;
    };

    Some(item)
}

fn find_enum_by_def_id<'a>(
    package: &'a ast::Package,
    output: &ResolutionOutput<'_>,
    def_id: DefinitionID,
) -> Option<&'a ast::Enum> {
    fn walk_module<'a>(
        module: &'a ast::Module,
        output: &ResolutionOutput<'_>,
        def_id: DefinitionID,
    ) -> Option<&'a ast::Enum> {
        for file in &module.files {
            for decl in &file.declarations {
                if let ast::DeclarationKind::Enum(enum_def) = &decl.kind {
                    if output.node_to_definition.get(&decl.id) == Some(&def_id) {
                        return Some(enum_def);
                    }
                }
            }
        }
        for sub in &module.submodules {
            if let Some(found) = walk_module(sub, output, def_id) {
                return Some(found);
            }
        }
        None
    }

    walk_module(&package.root, output, def_id)
}

fn derive_optional_variants(
    enum_def: &ast::Enum,
    gcx: GlobalContext<'_>,
    output: &ResolutionOutput<'_>,
    registry: &mut StdItemRegistry,
    had_error: &mut bool,
) {
    let mut some_variant: Option<&ast::Variant> = None;
    let mut none_variant: Option<&ast::Variant> = None;

    for case in &enum_def.cases {
        for variant in &case.variants {
            if gcx.symbol_eq(variant.identifier.symbol, "some") {
                some_variant = Some(variant);
            } else if gcx.symbol_eq(variant.identifier.symbol, "none") {
                none_variant = Some(variant);
            }
        }
    }

    let Some(some_variant) = some_variant else {
        gcx.dcx()
            .emit_error("Optional is missing `some` variant".into(), None);
        *had_error = true;
        return;
    };
    let Some(none_variant) = none_variant else {
        gcx.dcx()
            .emit_error("Optional is missing `none` variant".into(), None);
        *had_error = true;
        return;
    };

    if !matches!(some_variant.kind, ast::VariantKind::Tuple(_)) {
        gcx.dcx().emit_error(
            "Optional.some must be a tuple variant".into(),
            Some(some_variant.span),
        );
        *had_error = true;
    }
    if !matches!(none_variant.kind, ast::VariantKind::Unit) {
        gcx.dcx().emit_error(
            "Optional.none must be a unit variant".into(),
            Some(none_variant.span),
        );
        *had_error = true;
    }

    let Some(some_variant_id) = output.node_to_definition.get(&some_variant.id) else {
        gcx.dcx().emit_error(
            "unable to resolve Optional.some variant definition".into(),
            Some(some_variant.span),
        );
        *had_error = true;
        return;
    };
    let Some(none_variant_id) = output.node_to_definition.get(&none_variant.id) else {
        gcx.dcx().emit_error(
            "unable to resolve Optional.none variant definition".into(),
            Some(none_variant.span),
        );
        *had_error = true;
        return;
    };
    let Some(some_ctor_id) = output.node_to_definition.get(&some_variant.ctor_id) else {
        gcx.dcx().emit_error(
            "unable to resolve Optional.some constructor definition".into(),
            Some(some_variant.span),
        );
        *had_error = true;
        return;
    };
    let Some(none_ctor_id) = output.node_to_definition.get(&none_variant.ctor_id) else {
        gcx.dcx().emit_error(
            "unable to resolve Optional.none constructor definition".into(),
            Some(none_variant.span),
        );
        *had_error = true;
        return;
    };

    if let Some(kind) = output.definition_to_kind.get(some_variant_id) {
        if *kind != DefinitionKind::Variant {
            gcx.dcx().emit_error(
                "Optional.some is not a variant definition".into(),
                Some(some_variant.span),
            );
            *had_error = true;
        }
    }
    if let Some(kind) = output.definition_to_kind.get(none_variant_id) {
        if *kind != DefinitionKind::Variant {
            gcx.dcx().emit_error(
                "Optional.none is not a variant definition".into(),
                Some(none_variant.span),
            );
            *had_error = true;
        }
    }
    if let Some(kind) = output.definition_to_kind.get(some_ctor_id) {
        if *kind != DefinitionKind::VariantConstructor(VariantCtorKind::Function) {
            gcx.dcx().emit_error(
                "Optional.some constructor must be a function constructor".into(),
                Some(some_variant.span),
            );
            *had_error = true;
        }
    }
    if let Some(kind) = output.definition_to_kind.get(none_ctor_id) {
        if *kind != DefinitionKind::VariantConstructor(VariantCtorKind::Constant) {
            gcx.dcx().emit_error(
                "Optional.none constructor must be a constant constructor".into(),
                Some(none_variant.span),
            );
            *had_error = true;
        }
    }

    let some_variant_entry = StdItemEntry {
        def_id: *some_variant_id,
        def_kind: DefinitionKind::Variant,
        span: some_variant.span,
    };
    let some_ctor_entry = StdItemEntry {
        def_id: *some_ctor_id,
        def_kind: DefinitionKind::VariantConstructor(VariantCtorKind::Function),
        span: some_variant.span,
    };
    let none_variant_entry = StdItemEntry {
        def_id: *none_variant_id,
        def_kind: DefinitionKind::Variant,
        span: none_variant.span,
    };
    let none_ctor_entry = StdItemEntry {
        def_id: *none_ctor_id,
        def_kind: DefinitionKind::VariantConstructor(VariantCtorKind::Constant),
        span: none_variant.span,
    };

    if !registry.insert(gcx, StdItem::OptionalSomeVariant, some_variant_entry) {
        *had_error = true;
    }
    if !registry.insert(gcx, StdItem::OptionalSomeCtor, some_ctor_entry) {
        *had_error = true;
    }
    if !registry.insert(gcx, StdItem::OptionalNoneVariant, none_variant_entry) {
        *had_error = true;
    }
    if !registry.insert(gcx, StdItem::OptionalNoneCtor, none_ctor_entry) {
        *had_error = true;
    }
}
