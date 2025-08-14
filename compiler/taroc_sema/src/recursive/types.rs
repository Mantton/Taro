use crate::{
    GlobalContext,
    normalize::assoc::normalize_ty,
    recursive::type_graph::{EdgeInfo, TypeGraph},
    ty::{AdtFieldDefinition, EnumDefinition, FieldIndex, StructDefinition, Ty, TyKind},
};
use index_vec::IndexVec;
use std::cell::RefCell;
use taroc_error::CompileResult;
use taroc_hir::DefinitionID;

pub fn run(package: &taroc_hir::Package, context: GlobalContext) -> CompileResult<()> {
    Actor::run(package, context)
}

struct Actor<'ctx> {
    context: GlobalContext<'ctx>,
    graph: RefCell<TypeGraph>,
}

impl<'ctx> Actor<'ctx> {
    fn new(context: GlobalContext<'ctx>) -> Actor<'ctx> {
        Actor {
            context,
            graph: RefCell::new(TypeGraph::new()),
        }
    }

    fn run(_: &taroc_hir::Package, context: GlobalContext<'ctx>) -> CompileResult<()> {
        let actor = Actor::new(context);
        actor.build_type_graph();
        actor.emit_cycles();
        context.diagnostics.report()
    }
}

impl<'ctx> Actor<'ctx> {
    fn build_type_graph(&self) {
        let (structs, enums) = self
            .context
            .with_session_type_database(|db| (db.structs.clone(), db.enums.clone()));
        // Seed
        {
            let mut g = self.graph.borrow_mut();
            for (&id, _) in &structs {
                g.ensure_node(id);
            }
            for (&id, _) in &enums {
                g.ensure_node(id);
            }
        }

        for (id, definition) in structs {
            self.collect_from_struct(id, definition);
        }
        for (id, definition) in enums {
            self.collect_from_enum(id, definition);
        }
    }

    fn collect_from_struct(&self, id: DefinitionID, definition: &'ctx StructDefinition<'ctx>) {
        let fields = &definition.variant.fields;
        self.collect_from_fields(id, fields, None);
    }

    fn collect_from_enum(&self, id: DefinitionID, definition: &'ctx EnumDefinition<'ctx>) {
        for variant in &definition.variants {
            self.collect_from_fields(id, &variant.fields, Some(variant.id));
        }
    }

    fn collect_from_fields(
        &self,
        id: DefinitionID,
        fields: &IndexVec<FieldIndex, AdtFieldDefinition<'ctx>>,
        variant: Option<DefinitionID>,
    ) {
        for field in fields {
            self.collect_from_type(id, field.ty, field.id, variant);
        }
    }

    fn collect_from_type(
        &self,
        id: DefinitionID,
        ty: Ty<'ctx>,
        field: DefinitionID,
        variant: Option<DefinitionID>,
    ) {
        match ty.kind() {
            // no edges
            TyKind::Bool
            | TyKind::Rune
            | TyKind::String
            | TyKind::Int(..)
            | TyKind::UInt(..)
            | TyKind::Float(..) => {}
            // pointer indirection
            TyKind::Pointer(..) | TyKind::Reference(..) | TyKind::Function { .. } => {}
            // polymorphic indirection
            TyKind::Parameter(..) | TyKind::Existential(..) | TyKind::Opaque(..) => {}

            TyKind::Array(ty, _) => self.collect_from_type(id, ty, field, variant),
            TyKind::Tuple(tys) => {
                for &ty in tys {
                    self.collect_from_type(id, ty, field, variant);
                }
            }
            TyKind::Adt(adt_def, ..) => {
                let info = EdgeInfo { field, variant };
                self.graph
                    .borrow_mut()
                    .add_edge_from_field(id, adt_def.id, info);
            }

            TyKind::AssociatedType(..) => {
                let ty = normalize_ty(ty, self.context);
                self.collect_from_type(id, ty, field, variant);
            }

            // unreachable
            TyKind::FnDef(..) | TyKind::Infer(..) | TyKind::Error | TyKind::Placeholder => {
                unreachable!()
            }
        }
    }
}

impl<'ctx> Actor<'ctx> {
    fn emit_cycles(&self) {
        let cycles = self.graph.borrow().recursive_sccs();
        for cycle in cycles {
            self.emit_cycle(cycle);
        }
    }

    fn emit_cycle(&self, cycle: Vec<DefinitionID>) {
        let gcx = self.context;
        let first_ident = gcx.ident_for(cycle[0]);
        let message = format!(
            "'{}' cannot have a field that recursively contains itself. Add some form of indirection",
            first_ident.symbol
        );
        gcx.diagnostics.error(message, first_ident.span);
        // TODO: Propery Error Reporting
    }
}
