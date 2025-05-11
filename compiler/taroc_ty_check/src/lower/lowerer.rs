use taroc_context::GlobalContext;
use taroc_hir::{DefinitionID, DefinitionKind, NodeID, PrimaryType};
use taroc_ty::{GenericArgument, GenericArguments, InterfaceTypeReference, Ty, TyKind};

use crate::utils::{convert_ast_float_ty, convert_ast_int_ty, convert_ast_uint_ty};

use super::{LoweringContext, LoweringRequest};

pub trait TypeLowerer<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;

    fn lowerer(&self) -> &dyn TypeLowerer<'ctx>
    where
        Self: Sized,
    {
        self
    }
}

impl<'ctx> dyn TypeLowerer<'ctx> + '_ {
    pub fn lower_type(&self, hir_ty: &taroc_hir::Type, request: &LoweringRequest) -> Ty<'ctx> {
        let gcx = self.gcx();
        // gcx.diagnostics.warn("Lowering Ty".into(), hir_ty.span);
        let result_ty = match &hir_ty.kind {
            taroc_hir::TypeKind::Tuple(items) => {
                let items: Vec<Ty<'ctx>> = items
                    .iter()
                    .map(|ty| self.lower_type(ty, request))
                    .collect();
                let items = gcx.store.interners.intern_ty_list(&items);
                Self::mk_ty(gcx, TyKind::Tuple(items))
            }
            taroc_hir::TypeKind::Path(path) => {
                self.lower_partially_resolved_path(hir_ty.id, path, request)
            }
            taroc_hir::TypeKind::Opaque(..) => todo!(),
            taroc_hir::TypeKind::Exisitential(..) => todo!(),
            taroc_hir::TypeKind::AnonStruct { .. } => todo!(),
            taroc_hir::TypeKind::Infer => todo!(),
            taroc_hir::TypeKind::Function { .. } => todo!(),
            taroc_hir::TypeKind::Malformed => unreachable!(),
        };

        gcx.cache_type_of_node(hir_ty.id, result_ty);
        result_ty
    }

    fn lower_partially_resolved_path(
        &self,
        id: NodeID,
        path: &taroc_hir::Path,
        request: &LoweringRequest,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();
        let resolution = gcx.resolution(id);

        if resolution.unresolved_segments() == 0 {
            return self.lower_path(id, path, request);
        } else {
            return self.lower_unresolved_path(id, path, &resolution, request);
        }
    }

    fn lower_path(
        &self,
        id: NodeID,
        path: &taroc_hir::Path,
        request: &LoweringRequest,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        let resolution = gcx.resolution(id).resolution();

        match resolution {
            taroc_hir::Resolution::PrimaryType(ty) => {
                // TODO: Prohibit Generic Arguments
                self.lower_primary_type(ty)
            }
            taroc_hir::Resolution::Definition(
                id,
                DefinitionKind::Enum | DefinitionKind::TypeAlias | DefinitionKind::Struct,
            ) => return self.lower_path_segment(id, path.segments.last().unwrap(), request),
            taroc_hir::Resolution::Definition(id, DefinitionKind::TypeParameter) => {
                // TODO: Prohibit Generics
                gcx.type_of(id)
            }
            taroc_hir::Resolution::Definition(_, DefinitionKind::Interface) => {
                // TODO: Check Generics
                // let arguments = self.lower_type_arguments(id, path.segments.last().unwrap());

                // let Ok(arguments) = arguments else {
                //     return gcx.store.common_types.error;
                // };
                // let reference = InterfaceReference { id, arguments };
                // let references = gcx.store.interners.intern_slice(&[reference]);
                // let kind = TyKind::Existential(references);
                // Self::mk_ty(gcx, kind)
                gcx.store.common_types.error
            }
            taroc_hir::Resolution::Definition(id, DefinitionKind::AssociatedType) => {
                Self::mk_ty(gcx, TyKind::AssociatedType(id))
            }
            taroc_hir::Resolution::InterfaceSelfTypeAlias(..) => {
                // TODO: Prohibit Generics
                gcx.store.common_types.self_type_parameter
            }
            taroc_hir::Resolution::SelfTypeAlias(k) => match k {
                taroc_hir::SelfTypeAlias::Def(id) => gcx.type_of(id),
                taroc_hir::SelfTypeAlias::Primary(ty) => self.lower_primary_type(ty),
            },
            taroc_hir::Resolution::SelfConstructor(..)
            | taroc_hir::Resolution::Local(..)
            | taroc_hir::Resolution::FunctionSet(..) => unreachable!(),
            taroc_hir::Resolution::Error => gcx.store.common_types.error,
            taroc_hir::Resolution::Definition(..) => {
                println!("{resolution:?}");
                todo!("")
            }
        }
    }

    fn lower_primary_type(&self, ty: PrimaryType) -> Ty<'ctx> {
        let gcx = self.gcx();
        match ty {
            taroc_hir::PrimaryType::Int(i) => Self::mk_ty(gcx, TyKind::Int(convert_ast_int_ty(i))),
            taroc_hir::PrimaryType::UInt(i) => {
                Self::mk_ty(gcx, TyKind::UInt(convert_ast_uint_ty(i)))
            }
            taroc_hir::PrimaryType::Float(i) => {
                Self::mk_ty(gcx, TyKind::Float(convert_ast_float_ty(i)))
            }
            taroc_hir::PrimaryType::String => gcx.store.common_types.string,
            taroc_hir::PrimaryType::Bool => gcx.store.common_types.bool,
            taroc_hir::PrimaryType::Rune => gcx.store.common_types.rune,
        }
    }
    fn lower_unresolved_path(
        &self,
        id: NodeID,
        path: &taroc_hir::Path,
        resolution: &taroc_hir::PartialResolution,
        request: &LoweringRequest,
    ) -> Ty<'ctx> {
        assert_eq!(resolution.unresolved_segments(), 1);
        let gcx = self.gcx();
        let segment = path.segments.last().unwrap();
        let name = segment.identifier.symbol;
        let span = segment.identifier.span;
        let resolved_path = taroc_hir::Path {
            span,
            segments: path.segments[..path.segments.len() - 1].to_vec(),
        };
        let base_ty = self.lower_path(id, &resolved_path, request);
        let simple_ty = base_ty.to_simple_type();
        // println!("Base {base_ty}");

        let file = segment.identifier.span.file;
        let visible_packages = {
            let index = gcx.session().index().index();
            let resolutions = gcx.store.resolutions.borrow();
            let Some(resolutions) = resolutions.get(&index) else {
                unreachable!()
            };
            resolutions
                .file_to_imports
                .get(&file)
                .cloned()
                .unwrap_or_default()
        };

        let mut candidates = vec![];
        for package in visible_packages {
            gcx.with_type_database(package, |db| {
                let result = db.alias_table.by_type.get(&simple_ty);
                let Some(entry) = result else { return };
                let target = entry.aliases.get(&name);
                let Some(target) = target else { return };
                candidates.push(target.0);
            });
        }

        if candidates.len() > 1 {
            let message = format!("ambiguous associated type named '{name}' in '{base_ty}'");
            gcx.diagnostics.error(message, span);

            for (index, &candidate) in candidates.iter().enumerate() {
                let index = index + 1;
                let message = format!("candidate {index} defined here");
                gcx.diagnostics.info(message, gcx.ident_for(candidate).span);
            }

            return gcx.store.common_types.error;
        }

        let entry = match candidates.pop() {
            None => {
                // no candidates, assoc type not found
                let message = format!("unknown associated type named '{name}' in '{base_ty}'");
                gcx.diagnostics.error(message, span);
                return gcx.store.common_types.error;
            }
            Some(e) => e,
        };

        // println!("Assoc Type {name}");
        // return self.resolve_alias_ty(entry, request);

        let kind = TyKind::AssociatedType(entry);
        return Self::mk_ty(gcx, kind);
    }

    fn lower_path_segment(
        &self,
        id: DefinitionID,
        segment: &taroc_hir::PathSegment,
        request: &LoweringRequest,
    ) -> Ty<'ctx> {
        let gcx = self.gcx();

        let args = self.lower_type_arguments(id, segment, request);
        let Ok(args) = args else {
            return gcx.store.common_types.error;
        };

        let base = if matches!(gcx.def_kind(id), DefinitionKind::TypeAlias) {
            if let Some(base) = gcx.type_of_opt(id) {
                return base;
            } else {
                println!("inheretnt");
                let kind = TyKind::AssociatedType(id);
                Self::mk_ty(gcx, kind)
            }
        } else {
            let base = gcx.type_of(id);
            base
        };

        // instantiate
        // instantiate_ty_with_args(gcx, base, args)
        base
    }

    pub fn lower_type_arguments(
        &self,
        def_id: DefinitionID,
        segment: &taroc_hir::PathSegment,
        request: &LoweringRequest,
    ) -> Result<taroc_ty::GenericArguments<'ctx>, ()> {
        let gcx = self.gcx();
        let arguments = if let Some(arguments) = &segment.arguments {
            arguments
        } else {
            // implicit params for extension self types
            if matches!(request.context, LoweringContext::ExtensionSelfTy) {
                return Ok(convert_params_to_arguments(gcx, def_id));
            }
            &taroc_hir::TypeArguments {
                span: segment.identifier.span,
                arguments: Default::default(),
            }
        };
        let mut ok = check_generics_prohibited(def_id, &arguments, gcx);
        if !ok {
            return Err(());
        }

        ok = check_generic_arg_count(def_id, segment, gcx);
        if !ok {
            return Err(());
        }

        let arguments = self.lower_generic_args(def_id, arguments, request);
        return Ok(arguments);
    }

    fn lower_generic_args(
        &self,
        id: DefinitionID,
        arguments: &taroc_hir::TypeArguments,
        request: &LoweringRequest,
    ) -> GenericArguments<'ctx> {
        let gcx = self.gcx();
        let generics = gcx.generics_of(id);

        let mut output = vec![];

        for (index, parameter) in generics.parameters.iter().enumerate() {
            // ───── Is there an explicit <…> argument in source? ─────
            if let Some(hir_arg) = arguments.arguments.get(index) {
                let lowered = match hir_arg {
                    taroc_hir::TypeArgument::Type(ty) => {
                        GenericArgument::Type(self.lower_type(ty, request))
                    }
                    taroc_hir::TypeArgument::Const(_) => todo!(), // const generics later
                };
                output.push(lowered);
                continue;
            }

            match &parameter.kind {
                // ---- provided default ----
                taroc_ty::GenericParameterDefinitionKind::Type { default: Some(d) } => {
                    let ty = self.lower_type(d, request);
                    output.push(GenericArgument::Type(ty));
                }

                // ---- no default ----
                taroc_ty::GenericParameterDefinitionKind::Type { default: None } => {
                    if matches!(gcx.def_kind(id), DefinitionKind::Function) {
                        // For *functions* we leave the original parameter so
                        // `instantiate(FnDef)` can replace it with a fresh TyVar.
                        // output.push(GenericArgument::Type(self.context.type_of(parameter.id)));
                        todo!()
                    } else {
                        // For structs/enums/etc. this should already have been
                        // rejected by `check_generic_arg_count`, but keep a
                        // fallback just in case.
                        gcx.diagnostics
                            .error("missing generic argument".into(), arguments.span);
                        output.push(GenericArgument::Type(gcx.store.common_types.error));
                    }
                }

                taroc_ty::GenericParameterDefinitionKind::Const { .. } => todo!(),
            }
        }
        return gcx.store.interners.intern_generic_args(&output);
    }

    fn mk_ty(gcx: GlobalContext<'ctx>, k: TyKind<'ctx>) -> Ty<'ctx> {
        gcx.store.interners.intern_ty(k)
    }

    pub fn lower_interface_reference(
        &self,
        self_ty: Ty<'ctx>,
        node: &taroc_hir::TaggedPath,
        request: &LoweringRequest,
    ) -> InterfaceTypeReference<'ctx> {
        let gcx = self.gcx();
        let resolution = gcx.resolution(node.id).resolution();
        let interface_id = match resolution {
            taroc_hir::Resolution::Definition(id, taroc_hir::DefinitionKind::Interface) => id,
            _ => unreachable!("resolver must validate provided paths are interfaces"),
        };

        let arguments = node
            .path
            .segments
            .last()
            .map(|f| f.arguments.as_ref())
            .flatten();

        let generics = gcx.generics_of(interface_id);
        check_generic_arg_count(interface_id, node.path.segments.last().unwrap(), gcx);

        let mut result = vec![];

        for (index, parameter) in generics.parameters.iter().enumerate() {
            if index == 0 && generics.has_self {
                result.push(GenericArgument::Type(self_ty));
                continue;
            }

            if let Some(arguments) = arguments
                && let Some(argument) = arguments
                    .arguments
                    .get(parameter.index - generics.has_self as usize)
            {
                match argument {
                    taroc_hir::TypeArgument::Type(ty) => {
                        let ty = self.lower_type(ty, request);
                        result.push(GenericArgument::Type(ty));
                        continue;
                    }
                    taroc_hir::TypeArgument::Const(_) => todo!(),
                }
            } else {
                // Get Default Argument
                match &parameter.kind {
                    taroc_ty::GenericParameterDefinitionKind::Type { default } => {
                        let ty = if let Some(default) = default {
                            self.lower_type(default, request)
                        } else {
                            gcx.diagnostics
                                .warn("Defaulting To Err".into(), node.path.span);
                            gcx.store.common_types.error
                        };

                        result.push(GenericArgument::Type(ty));
                        continue;
                    }
                    taroc_ty::GenericParameterDefinitionKind::Const { .. } => {
                        todo!()
                    }
                }
            };
        }

        let reference = InterfaceTypeReference {
            id: interface_id,
            arguments: gcx.store.interners.mk_args(result),
        };

        return reference;
    }

    fn resolve_alias_ty(&self, id: DefinitionID, request: &LoweringRequest) -> Ty<'ctx> {
        let gcx = self.gcx();
        let has_seen = {
            let seen = request.alias_visits.borrow();
            seen.contains(&id)
        };

        if has_seen {
            let ident = gcx.ident_for(id);
            let message = format!("circular alias reference through '{}'", ident.symbol);
            gcx.diagnostics.error(message, ident.span);
            return gcx.store.common_types.error;
        }

        {
            let mut seen = request.alias_visits.borrow_mut();
            seen.push(id);
        };

        let entry =
            gcx.with_type_database(id.package(), |db| db.alias_table.aliases.get(&id).cloned());

        let entry = entry.unwrap();

        return self.lower_type(&entry.ast_type, request);
    }
}

fn check_generics_prohibited(
    def_id: DefinitionID,
    arguments: &taroc_hir::TypeArguments,
    context: GlobalContext<'_>,
) -> bool {
    let kind = context.def_kind(def_id);

    // No type arguments => always OK
    if arguments.arguments.is_empty() {
        return true;
    }

    // Only these kinds allow generics
    let allowed = matches!(
        kind,
        DefinitionKind::Struct
            | DefinitionKind::Enum
            | DefinitionKind::Interface
            | DefinitionKind::TypeAlias
            | DefinitionKind::Function
    );

    if !allowed {
        context.diagnostics.error(
            format!("Generics not permitted on {:?}", kind),
            arguments.span,
        );
        return false;
    }

    true
}

pub fn check_generic_arg_count(
    id: DefinitionID,
    segment: &taroc_hir::PathSegment,
    context: GlobalContext<'_>,
) -> bool {
    let generics = context.generics_of(id);

    let defaults_count = generics.default_count();
    let total_count = generics.total_count();

    let min = total_count - defaults_count - generics.has_self as usize;
    let provided = segment
        .arguments
        .as_ref()
        .map(|v| v.arguments.len())
        .unwrap_or(0);

    if matches!(context.def_kind(id), DefinitionKind::Function) {
        // any number ≤ total is OK – inference will fill the rest
        if provided <= total_count {
            return true;
        }
        context.diagnostics.error(
            format!(
                "excess generic arguments: function takes at most {total_count}, provided {provided}"
            ),
            segment.arguments.as_ref().unwrap().span,
        );
        return false;
    }

    if (min..=total_count).contains(&provided) {
        return true;
    }

    if provided > total_count {
        let message = format!(
            "excess generic arguments, '{}' requires {} type argument(s), provided {}",
            segment.identifier.symbol, min, provided
        );
        context
            .diagnostics
            .error(message, segment.arguments.as_ref().map(|v| v.span).unwrap());
    } else {
        context
            .diagnostics
            .error("Missing Generic Arguments".into(), segment.identifier.span);
    }

    return false;
}

fn convert_params_to_arguments<'ctx>(
    gcx: GlobalContext<'ctx>,
    def_id: DefinitionID,
) -> GenericArguments<'ctx> {
    let generics = gcx.generics_of(def_id);
    let parameters = &generics.parameters;

    let mut args = vec![];
    for parameter in parameters {
        match &parameter.kind {
            taroc_ty::GenericParameterDefinitionKind::Type { .. } => {
                let ty = gcx.type_of(parameter.id);
                args.push(GenericArgument::Type(ty));
            }
            taroc_ty::GenericParameterDefinitionKind::Const { .. } => todo!(),
        }
    }

    gcx.store.interners.intern_generic_args(&args)
}
