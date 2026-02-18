use crate::{ast, cfg::TargetInfo, compile::context::GlobalContext};

pub fn filter_package(package: &mut ast::Package, target: &TargetInfo, gcx: GlobalContext<'_>) {
    filter_module(&mut package.root, target, gcx);
}

fn filter_module(module: &mut ast::Module, target: &TargetInfo, gcx: GlobalContext<'_>) {
    for file in &mut module.files {
        filter_file(file, target, gcx);
    }

    for submodule in &mut module.submodules {
        filter_module(submodule, target, gcx);
    }
}

fn filter_file(file: &mut ast::File, target: &TargetInfo, gcx: GlobalContext<'_>) {
    filter_declarations(&mut file.declarations, target, gcx);
}

fn filter_declarations(
    decls: &mut Vec<ast::Declaration>,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) {
    retain_mut(decls, |decl| filter_declaration(decl, target, gcx));
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
    retain_mut(decls, |decl| {
        filter_namespace_declaration(decl, target, gcx)
    });
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
    retain_mut(decls, |decl| {
        should_include_attrs(&decl.attributes, target, gcx)
    });
}

fn filter_extern_declarations(
    decls: &mut Vec<ast::ExternDeclaration>,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) {
    retain_mut(decls, |decl| {
        should_include_attrs(&decl.attributes, target, gcx)
    });
}

pub fn should_include_attrs(
    attrs: &ast::AttributeList,
    target: &TargetInfo,
    gcx: GlobalContext<'_>,
) -> bool {
    for attr in attrs {
        if gcx.symbol_eq(attr.identifier.symbol.clone(), "cfg") && !eval_cfg_attr(attr, target, gcx) {
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
                let key_text = gcx.symbol_text(key.symbol.clone());
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
                let key_text = gcx.symbol_text(key.symbol.clone());
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
                    _ => return false,
                }
            }
        }
    }

    true
}

fn eval_cfg_expr(expr: &ast::CfgExpr, target: &TargetInfo, gcx: GlobalContext<'_>) -> bool {
    match expr {
        ast::CfgExpr::Predicate { name, value, .. } => {
            let name_text = gcx.symbol_text(name.symbol.clone());
            let name_str = name_text.as_str();
            let value_text = gcx.symbol_text(value.clone());
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

fn retain_mut<T>(items: &mut Vec<T>, mut keep: impl FnMut(&mut T) -> bool) {
    let mut out = Vec::with_capacity(items.len());
    for mut item in items.drain(..) {
        if keep(&mut item) {
            out.push(item);
        }
    }
    *items = out;
}
