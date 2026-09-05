use crate::{ast, cfg::TargetInfo, compile::context::GlobalContext};

pub(crate) fn target_info(gcx: GlobalContext<'_>) -> TargetInfo {
    let triple = gcx.store.target_layout.triple();
    let mut target = TargetInfo::from_triple(triple.as_str().to_str().unwrap_or(""));
    target.profile = match gcx.config.profile {
        crate::compile::config::BuildProfile::Debug => "debug".to_string(),
        crate::compile::config::BuildProfile::Release => "release".to_string(),
    };
    target.test_mode = gcx.config.harness_mode.is_test();
    target.bench_mode = gcx.config.harness_mode.is_bench();
    target
}

pub fn filter_package(package: &mut ast::Package, target: &TargetInfo, gcx: GlobalContext<'_>) {
    filter_module(&mut package.root, target, gcx);
}

fn filter_module(module: &mut ast::Module, target: &TargetInfo, gcx: GlobalContext<'_>) {
    for file in &mut module.files {
        filter_file(file, target, gcx);
    }

    module.submodules.retain_mut(|submodule| {
        if let Some(decl) = &submodule.module_decl {
            if !should_include_attrs(&decl.attributes, target, gcx) {
                return false;
            }
        }
        filter_module(submodule, target, gcx);
        true
    });
}

fn filter_file(file: &mut ast::File, target: &TargetInfo, gcx: GlobalContext<'_>) {
    filter_declarations(&mut file.declarations, target, gcx);
}

fn filter_declarations(
    decls: &mut Vec<ast::Declaration>,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) {
    decls.retain_mut(|decl| filter_declaration(decl, target, gcx));
}

fn filter_declaration(
    decl: &mut ast::Declaration,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) -> bool {
    if !should_include_attrs(&decl.attributes, target, gcx) {
        return false;
    }

    match &mut decl.kind {
        ast::DeclarationKind::Interface(node) => {
            filter_assoc_declarations(&mut node.declarations, target, gcx);
        }
        ast::DeclarationKind::Namespace(node) => {
            filter_namespace_declarations(&mut node.declarations, target, gcx);
        }
        ast::DeclarationKind::ExternBlock(node) => {
            filter_extern_declarations(&mut node.declarations, target, gcx);
        }
        ast::DeclarationKind::Impl(node) => {
            filter_assoc_declarations(&mut node.declarations, target, gcx);
        }
        _ => {}
    }

    true
}

fn filter_namespace_declarations(
    decls: &mut Vec<ast::NamespaceDeclaration>,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) {
    decls.retain_mut(|decl| filter_namespace_declaration(decl, target, gcx));
}

fn filter_namespace_declaration(
    decl: &mut ast::NamespaceDeclaration,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) -> bool {
    if !should_include_attrs(&decl.attributes, target, gcx) {
        return false;
    }

    match &mut decl.kind {
        ast::NamespaceDeclarationKind::Namespace(node) => {
            filter_namespace_declarations(&mut node.declarations, target, gcx);
        }
        ast::NamespaceDeclarationKind::Interface(node) => {
            filter_assoc_declarations(&mut node.declarations, target, gcx);
        }
        _ => {}
    }

    true
}

fn filter_assoc_declarations(
    decls: &mut Vec<ast::AssociatedDeclaration>,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) {
    decls.retain_mut(|decl| should_include_attrs(&decl.attributes, target, gcx));
}

fn filter_extern_declarations(
    decls: &mut Vec<ast::ExternDeclaration>,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) {
    decls.retain_mut(|decl| should_include_attrs(&decl.attributes, target, gcx));
}

pub fn should_include_attrs(
    attrs: &ast::AttributeList,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) -> bool {
    for attr in attrs {
        if gcx.symbol_eq(attr.identifier.symbol, "cfg") && !eval_cfg_attr(attr, target, gcx) {
            return false;
        }
    }
    true
}

fn eval_cfg_attr(attr: &ast::Attribute, target: &TargetInfo, gcx: GlobalContext<'_>) -> bool {
    if let Some(cfg_expr) = &attr.cfg_expr {
        return eval_cfg_expr(cfg_expr, target, gcx);
    }

    let Some(args) = &attr.args else {
        return true;
    };

    for arg in &args.items {
        match arg {
            ast::AttributeArg::KeyValue { key, value, .. } => {
                let key_text = gcx.symbol_text(key.symbol);
                let key_str = key_text.as_str();
                let value_str = match value {
                    ast::Literal::String { value } => value.as_str(),
                    _ => continue,
                };

                match key_str {
                    "target_os" => {
                        if !target.matches_os(value_str) {
                            return false;
                        }
                    }
                    "target_arch" => {
                        if !target.matches_arch(value_str) {
                            return false;
                        }
                    }
                    "target_profile" => {
                        if !target.matches_profile(value_str) {
                            return false;
                        }
                    }
                    _ => return false,
                }
            }
            ast::AttributeArg::Flag { key, .. } => {
                let key_text = gcx.symbol_text(key.symbol);
                let key_str = key_text.as_str();
                match key_str {
                    "debug" => {
                        if !target.matches_profile("debug") {
                            return false;
                        }
                    }
                    "test" => {
                        if !target.test_mode {
                            return false;
                        }
                    }
                    "bench" => {
                        if !target.bench_mode {
                            return false;
                        }
                    }
                    _ => return false,
                }
            }
            ast::AttributeArg::Literal { .. } => return false,
        }
    }

    true
}

pub(crate) fn eval_cfg_expr(
    expr: &ast::CfgExpr,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) -> bool {
    match expr {
        ast::CfgExpr::Flag { name, .. } => {
            let name = gcx.symbol_text(name.symbol);
            match name.as_str() {
                "debug" => target.matches_profile("debug"),
                "test" => target.test_mode,
                "bench" => target.bench_mode,
                _ => false,
            }
        }
        ast::CfgExpr::Predicate { name, value, .. } => {
            let name_text = gcx.symbol_text(name.symbol);
            let name_str = name_text.as_str();
            let value_text = gcx.symbol_text(*value);
            let value_str = value_text.as_str();

            match name_str {
                "os" => target.matches_os(value_str),
                "arch" => target.matches_arch(value_str),
                "family" => target.matches_family(value_str),
                "profile" => target.matches_profile(value_str),
                _ => false,
            }
        }
        ast::CfgExpr::Not(inner, _) => !eval_cfg_expr(inner, target, gcx),
        ast::CfgExpr::All(items, _) => items.iter().all(|e| eval_cfg_expr(e, target, gcx)),
        ast::CfgExpr::Any(items, _) => items.iter().any(|e| eval_cfg_expr(e, target, gcx)),
    }
}
