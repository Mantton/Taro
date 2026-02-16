use std::fmt;

use crate::compile::context::Gcx;
use crate::thir::VariantIndex;

use super::{
    BasicBlockData, Body, CallUnwindAction, Constant, ConstantKind, LocalDecl, LocalKind, Operand,
    Place, PlaceElem, Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};

pub struct PrettyPrintMir<'body, 'ctx> {
    pub body: &'body Body<'ctx>,
    pub gcx: Gcx<'ctx>,
}

impl<'body, 'ctx> PrettyPrintMir<'body, 'ctx> {
    fn mutability(decl: &LocalDecl) -> &'static str {
        match decl.kind {
            LocalKind::User => "mut ",
            _ => "",
        }
    }

    fn write_block(&self, block: &BasicBlockData<'ctx>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for stmt in &block.statements {
            write!(f, "        ")?;
            self.write_statement(stmt, f)?;
            writeln!(f, ";")?;
        }

        if let Some(term) = &block.terminator {
            write!(f, "        ")?;
            self.write_terminator(term, f)?;
            writeln!(f, ";")?;
        }

        Ok(())
    }

    fn write_statement(&self, stmt: &Statement<'ctx>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &stmt.kind {
            StatementKind::Assign(place, rvalue) => {
                self.write_place(place, f)?;
                write!(f, " = ")?;
                self.write_rvalue(rvalue, f)
            }
            StatementKind::GcSafepoint => write!(f, "gc_safepoint"),
            StatementKind::Nop => write!(f, "nop"),
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => {
                write!(f, "set_discriminant ")?;
                self.write_place(place, f)?;
                if let Some(name) = self.variant_name_for_place(place, *variant_index) {
                    write!(f, " = {}", name)
                } else {
                    write!(f, " = {}", variant_index.index())
                }
            }
        }
    }

    fn write_terminator(&self, term: &Terminator<'ctx>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &term.kind {
            TerminatorKind::Goto { target } => write!(f, "goto -> bb{:?}", target),
            TerminatorKind::UnresolvedGoto => write!(f, "unresolved_goto"),
            TerminatorKind::SwitchInt {
                discr,
                targets,
                otherwise,
            } => {
                write!(f, "switchInt(")?;
                self.write_operand(discr, f)?;
                write!(f, ") -> [")?;
                for (val, target) in targets {
                    write!(f, "{}: bb{:?}, ", val, target)?;
                }
                write!(f, "otherwise: bb{:?}]", otherwise)
            }
            TerminatorKind::Return => write!(f, "return"),
            TerminatorKind::ResumeUnwind => write!(f, "resume_unwind"),
            TerminatorKind::Unreachable => write!(f, "unreachable"),
            TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                unwind,
            } => {
                self.write_place(destination, f)?;
                write!(f, " = ")?;
                self.write_operand(func, f)?;
                write!(f, "(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    self.write_operand(arg, f)?;
                }
                write!(f, ") -> bb{:?}", target)?;
                match unwind {
                    CallUnwindAction::Cleanup(bb) => write!(f, " unwind bb{:?}", bb),
                    CallUnwindAction::Terminate => write!(f, " unwind terminate"),
                }
            }
        }
    }

    fn write_place(&self, place: &Place<'ctx>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out = format!("%{:?}", place.local);
        for elem in &place.projection {
            match elem {
                PlaceElem::Deref => {
                    out = format!("*{out}");
                }
                PlaceElem::Field(idx, _) => {
                    out.push_str(&format!(".{:?}", idx));
                }
                PlaceElem::VariantDowncast { name, .. } => {
                    out = format!("({out} as {name})");
                }
            }
        }
        write!(f, "{out}")
    }

    fn write_operand(&self, op: &Operand<'ctx>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match op {
            Operand::Copy(place) => self.write_place(place, f),
            Operand::Move(place) => {
                write!(f, "move ")?;
                self.write_place(place, f)
            }
            Operand::Constant(c) => self.write_constant(c, f),
        }
    }

    fn write_constant(&self, c: &Constant<'ctx>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &c.value {
            ConstantKind::Bool(b) => write!(f, "{}", b),
            ConstantKind::Rune(c) => write!(f, "{:?}", c),
            ConstantKind::String(s) => write!(f, "{:?}", s),
            ConstantKind::Integer(i) => write!(f, "const {}", i),
            ConstantKind::Float(fl) => write!(f, "const {}", fl),
            ConstantKind::Unit => write!(f, "()"),
            ConstantKind::Function(def_id, _, _) => {
                let ident = self.gcx.definition_ident(*def_id);
                write!(f, "fn {}", ident.symbol)
            }
            ConstantKind::ConstParam(param) => write!(f, "const {}", param.name.as_str()),
        }
    }

    fn write_rvalue(&self, rvalue: &Rvalue<'ctx>, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match rvalue {
            Rvalue::Use(op) => self.write_operand(op, f),
            Rvalue::UnaryOp { op, operand } => {
                write!(f, "{:?}", op)?; // Simple debug print for op enum
                self.write_operand(operand, f)
            }
            Rvalue::BinaryOp { op, lhs, rhs } => {
                self.write_operand(lhs, f)?;
                write!(f, " {:?} ", op)?; // Simple debug print for op enum
                self.write_operand(rhs, f)
            }
            Rvalue::Ref { mutable, place } => {
                let kw = if *mutable { "&mut " } else { "&" };
                write!(f, "{}", kw)?;
                self.write_place(place, f)
            }
            Rvalue::Discriminant { place } => {
                write!(f, "discriminant(")?;
                self.write_place(place, f)?;
                write!(f, ")")
            }
            Rvalue::Alloc { ty } => write!(f, "alloc {}", ty.format(self.gcx)),
            Rvalue::Cast { operand, ty, kind } => {
                self.write_operand(operand, f)?;
                write!(f, " as {} ({:?})", ty.format(self.gcx), kind)
            }
            Rvalue::Aggregate { kind, fields } => {
                match kind {
                    super::AggregateKind::Tuple => write!(f, "tuple")?,
                    super::AggregateKind::Array { len, .. } => write!(f, "array[{len}]")?,
                    super::AggregateKind::Adt {
                        def_id,
                        variant_index,
                        ..
                    } => {
                        let ident = self.gcx.definition_ident(*def_id);
                        write!(f, "{}", ident.symbol)?;
                        if let Some(variant_index) = variant_index {
                            if matches!(
                                self.gcx.definition_kind(*def_id),
                                crate::sema::resolve::models::DefinitionKind::Enum
                            ) {
                                let variant =
                                    self.gcx.enum_variant_by_index(*def_id, *variant_index);
                                write!(f, "::{}", variant.name)?;
                            }
                        }
                    }
                    super::AggregateKind::Closure { def_id, .. } => {
                        write!(f, "closure@{:?}", def_id)?;
                    }
                }
                write!(f, " {{ ")?;
                for (i, field) in fields.iter_enumerated() {
                    if i.index() > 0 {
                        write!(f, ", ")?;
                    }
                    self.write_operand(field, f)?;
                }
                write!(f, " }}")
            }
            Rvalue::Repeat { operand, count, .. } => {
                write!(f, "repeat {} x ", count)?;
                self.write_operand(operand, f)
            }
        }
    }

    fn variant_name_for_place(
        &self,
        place: &Place<'ctx>,
        variant_index: VariantIndex,
    ) -> Option<crate::span::Symbol> {
        let mut ty = self.body.locals[place.local].ty;
        for elem in &place.projection {
            match elem {
                PlaceElem::Deref => {
                    ty = ty
                        .dereference()
                        .unwrap_or_else(|| crate::sema::models::Ty::error(self.gcx));
                }
                PlaceElem::Field(_, field_ty) => {
                    ty = *field_ty;
                }
                PlaceElem::VariantDowncast { .. } => {}
            }
        }
        match ty.kind() {
            crate::sema::models::TyKind::Adt(def, _)
                if matches!(def.kind, crate::sema::models::AdtKind::Enum) =>
            {
                let enum_def = self.gcx.get_enum_definition(def.id);
                enum_def
                    .variants
                    .get(variant_index.index())
                    .map(|variant| variant.name)
            }
            _ => None,
        }
    }
}

impl<'body, 'ctx> fmt::Display for PrettyPrintMir<'body, 'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (local, decl) in self.body.locals.iter_enumerated() {
            write!(
                f,
                "    let %{}{:?}: {};",
                Self::mutability(decl),
                local,
                decl.ty.format(self.gcx)
            )?;
            if let Some(name) = decl.name {
                write!(f, "        // debug: {}", name)?;
            }
            writeln!(f)?;
        }

        writeln!(f)?;

        for (id, block) in self.body.basic_blocks.iter_enumerated() {
            write!(f, "    bb{:?}: {{ ", id)?;

            if let Some(note) = block.note.as_deref() {
                write!(f, "// debug: {note}")?;
            }

            writeln!(f)?; // end the line
            self.write_block(block, f)?;
            writeln!(f, "    }}")?;
            writeln!(f)?;
        }

        Ok(())
    }
}
