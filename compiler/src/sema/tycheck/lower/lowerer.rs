use crate::{
    compile::context::GlobalContext,
    hir::{self, DefinitionID, DefinitionKind, Resolution},
    sema::{
        models::{
            AdtDef, AdtKind, GenericArgument, GenericArguments, GenericParameterDefinition,
            GenericParameterDefinitionKind, InterfaceReference, Ty, TyKind,
        },
        resolve::models::{PrimaryType, TypeHead},
        tycheck::utils::instantiate::instantiate_ty_with_args,
    },
    span::Span,
};

pub trait TypeLowerer<'ctx> {
    fn gcx(&self) -> GlobalContext<'ctx>;
    fn current_definition(&self) -> Option<hir::DefinitionID> {
        None
    }
    fn lowerer(&self) -> &dyn TypeLowerer<'ctx>
    where
        Self: Sized,
    {
        self
    }
    fn ty_infer(&self, param: Option<&GenericParameterDefinition>, span: Span) -> Ty<'ctx>;
}

impl<'ctx> dyn TypeLowerer<'ctx> + '_ {
    pub fn lower_type(&self, node: &hir::Type) -> Ty<'ctx> {
        let gcx = self.gcx();
        match &node.kind {
            hir::TypeKind::Nominal(path) => self.lower_nominal_type(node.id, path),
            hir::TypeKind::Pointer(node, mutability) => {
                let internal = self.lower_type(node);
                Ty::new(TyKind::Pointer(internal, *mutability), gcx)
            }
            hir::TypeKind::Reference(node, mutability) => {
                let internal = self.lower_type(node);
                Ty::new(TyKind::Reference(internal, *mutability), gcx)
            }
            hir::TypeKind::Tuple(elements) => {
                let mut lowered = Vec::with_capacity(elements.len());
                for elem in elements {
                    lowered.push(self.lower_type(elem));
                }
                Ty::new(
                    TyKind::Tuple(gcx.store.interners.intern_ty_list(lowered)),
                    gcx,
                )
            }
            hir::TypeKind::Array { .. } => todo!(),
            hir::TypeKind::Function { .. } => todo!(),
            hir::TypeKind::BoxedExistential { .. } => todo!(),
            hir::TypeKind::Infer => todo!(),
        }
    }

    fn lower_nominal_type(&self, node_id: hir::NodeID, path: &hir::ResolvedPath) -> Ty<'ctx> {
        match path {
            hir::ResolvedPath::Resolved(path) => self.lower_resolved_type_path(node_id, path),
            hir::ResolvedPath::Relative(..) => todo!(),
        }
    }

    fn lower_resolved_type_path(&self, _: hir::NodeID, path: &hir::Path) -> Ty<'ctx> {
        let resolution = path.resolution.clone();
        let gcx = self.gcx();
        match resolution {
            Resolution::PrimaryType(k) => match k {
                PrimaryType::Int(k) => Ty::new_int(gcx, k),
                PrimaryType::UInt(k) => Ty::new_uint(gcx, k),
                PrimaryType::Float(k) => Ty::new_float(gcx, k),
                PrimaryType::String => gcx.types.string,
                PrimaryType::Bool => gcx.types.bool,
                PrimaryType::Rune => gcx.types.rune,
            },
            Resolution::Definition(id, DefinitionKind::TypeParameter) => {
                // TODO: Prohibit Generics
                gcx.get_type(id)
            }
            Resolution::Definition(id, kind) => {
                if let Some(from) = self.current_definition() {
                    if !gcx.is_definition_visible(id, from) {
                        let name = gcx.definition_ident(id).symbol;
                        gcx.dcx().emit_error(
                            format!("type '{}' is not visible here", name).into(),
                            Some(path.span),
                        );
                        return gcx.types.error;
                    }
                }
                if gcx.is_std_gc_ptr(id) {
                    return Ty::new(TyKind::GcPtr, gcx);
                }
                let segment = path.segments.last().unwrap();
                let _ = check_generics_prohibited(id, segment, gcx);
                let args = self.lower_type_arguments(id, segment);
                let ty = match kind {
                    crate::sema::resolve::models::DefinitionKind::Struct
                    | crate::sema::resolve::models::DefinitionKind::Enum => {
                        let ident = gcx.definition_ident(id);
                        let def = AdtDef {
                            name: ident.symbol,
                            kind: match kind {
                                crate::sema::resolve::models::DefinitionKind::Enum => AdtKind::Enum,
                                _ => AdtKind::Struct,
                            },
                            id,
                        };
                        Ty::new(TyKind::Adt(def, args), gcx)
                    }
                    _ => todo!("nominal type lowering for {kind:?}"),
                };
                instantiate_ty_with_args(gcx, ty, args)
            }
            Resolution::SelfTypeAlias(id) => match gcx.definition_kind(id) {
                crate::sema::resolve::models::DefinitionKind::Struct
                | crate::sema::resolve::models::DefinitionKind::Enum => gcx.get_type(id),
                crate::sema::resolve::models::DefinitionKind::Extension => {
                    let Some(head) = gcx.get_extension_type_head(id) else {
                        return gcx.types.error;
                    };
                    match head {
                        TypeHead::Nominal(target_id) => gcx.get_type(target_id),
                        TypeHead::GcPtr => Ty::new(TyKind::GcPtr, gcx),
                        TypeHead::Primary(p) => match p {
                            PrimaryType::Int(k) => Ty::new_int(gcx, k),
                            PrimaryType::UInt(k) => Ty::new_uint(gcx, k),
                            PrimaryType::Float(k) => Ty::new_float(gcx, k),
                            PrimaryType::String => gcx.types.string,
                            PrimaryType::Bool => gcx.types.bool,
                            PrimaryType::Rune => gcx.types.rune,
                        },
                        _ => todo!("Self type alias lowering for {head:?}"),
                    }
                }
                other => todo!("Self type alias lowering for {other:?}"),
            },
            Resolution::InterfaceSelfTypeParameter(_interface_id) => {
                // Inside an interface, `Self` refers to the abstract Self type parameter
                gcx.types.self_type_parameter
            }
            Resolution::Foundation(..) => todo!(),
            Resolution::Error => gcx.types.error,
            Resolution::SelfConstructor(..)
            | Resolution::FunctionSet(..)
            | Resolution::LocalVariable(_) => {
                unreachable!("value resolution")
            }
        }
    }

    pub fn lower_type_arguments(
        &self,
        def_id: DefinitionID,
        segment: &hir::PathSegment,
    ) -> GenericArguments<'ctx> {
        self.lower_generic_args(def_id, segment, None)
    }

    fn lower_generic_args(
        &self,
        id: DefinitionID,
        segment: &hir::PathSegment,
        self_ty: Option<Ty<'ctx>>,
    ) -> GenericArguments<'ctx> {
        let gcx = self.gcx();
        let _ = check_generic_arg_count(id, segment, gcx);

        let generics = gcx.generics_of(id);

        let mut output = vec![];

        let arguments = segment
            .arguments
            .clone()
            .map(|v| v.arguments)
            .unwrap_or_default();
        let span = segment
            .arguments
            .as_ref()
            .map(|f| f.span)
            .unwrap_or(segment.span);
        let mut args_iter = arguments.iter().peekable();
        let mut params_iter = generics.parameters.iter().peekable();

        loop {
            match (args_iter.peek(), params_iter.peek()) {
                (_, Some(&param)) if generics.has_self && param.index == 0 => {
                    // Self must always be provided for interface references
                    let ty =
                        self_ty.expect("ICE: Self type must be provided for interface references");
                    output.push(GenericArgument::Type(ty));
                    params_iter.next();
                }
                (Some(&arg), Some(&_)) => {
                    let lowered = match arg {
                        hir::TypeArgument::Type(ty) => GenericArgument::Type(self.lower_type(ty)),
                        hir::TypeArgument::Const(_) => todo!(), // const generics later
                    };
                    output.push(lowered);
                    args_iter.next();
                    params_iter.next();
                }
                (Some(_), None) => {
                    break;
                }
                (None, Some(&param)) => {
                    match &param.kind {
                        // ---- provided default ----
                        GenericParameterDefinitionKind::Type { default: Some(d) } => {
                            let ty = self.lower_type(&d);
                            output.push(GenericArgument::Type(ty));
                        }

                        // ---- no default ----
                        GenericParameterDefinitionKind::Type { default: None } => {
                            let ty = self.ty_infer(Some(param), span);
                            output.push(GenericArgument::Type(ty));
                        }

                        GenericParameterDefinitionKind::Const { .. } => todo!(),
                    }
                    params_iter.next();
                }
                (None, None) => break,
            }
        }

        gcx.store.interners.intern_generic_args(output)
    }

    pub fn lower_interface_reference(
        &self,
        self_ty: Ty<'ctx>,
        node: &hir::PathNode,
    ) -> InterfaceReference<'ctx> {
        let path = match &node.path {
            hir::ResolvedPath::Resolved(path) => path,
            _ => {
                unreachable!("ICE: Interface Paths must be fully resolved")
            }
        };

        let interface_id = match &path.resolution {
            Resolution::Definition(id, DefinitionKind::Interface) => *id,
            _ => unreachable!("ICE: not an interface"),
        };

        let segment = path.segments.last().unwrap();
        let arguments = self.lower_generic_args(interface_id, segment, Some(self_ty));

        InterfaceReference {
            id: interface_id,
            arguments,
        }
    }
}

fn check_generics_prohibited(
    def_id: DefinitionID,
    segment: &hir::PathSegment,
    context: GlobalContext<'_>,
) -> bool {
    let kind = context.definition_kind(def_id);

    let Some(arguments) = &segment.arguments else {
        return true;
    };
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
        context.dcx.emit_error(
            format!("Generics not permitted on {:?}", kind),
            Some(arguments.span),
        );
        return false;
    }

    true
}

pub fn check_generic_arg_count(
    id: DefinitionID,
    segment: &hir::PathSegment,
    context: GlobalContext<'_>,
) -> bool {
    let generics = context.generics_of(id);
    let should_infer = segment.arguments.is_none();

    let defaults_count = generics.default_count();
    let total_count = generics.total_count();

    let min = if !should_infer {
        total_count - defaults_count - generics.has_self as usize
    } else {
        0
    };

    let provided = segment
        .arguments
        .as_ref()
        .map(|v| v.arguments.len())
        .unwrap_or(0);

    if matches!(context.definition_kind(id), DefinitionKind::Function) {
        // any number ≤ total is OK – inference will fill the rest
        if provided <= total_count {
            return true;
        }
        context.dcx().emit_error(
            format!(
                "excess generic arguments: function takes at most {total_count}, provided {provided}"
            ),
            segment.arguments.as_ref().map(|v| v.span),
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
            .dcx()
            .emit_error(message, segment.arguments.as_ref().map(|v| v.span));
    } else {
        context.dcx().emit_error(
            "Missing Generic Arguments".into(),
            Some(segment.identifier.span),
        );
    }

    return false;
}
