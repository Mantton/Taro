use std::fmt;

use super::{
    BasicBlockData, Body, Constant, ConstantKind, LocalDecl, LocalKind, Operand, Place, PlaceElem,
    Rvalue, Statement, StatementKind, Terminator, TerminatorKind,
};

pub struct PrettyPrintMir<'ctx> {
    pub body: &'ctx Body<'ctx>,
}

impl<'ctx> fmt::Display for PrettyPrintMir<'ctx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (local, decl) in self.body.locals.iter_enumerated() {
            writeln!(f, "    let {}{:?}: {:?};", mutability(decl), local, decl.ty)?;
            if let Some(name) = decl.name {
                writeln!(f, "        // debug: {}", name)?;
            }
        }

        writeln!(f, "")?;

        for (id, block) in self.body.basic_blocks.iter_enumerated() {
            write!(f, "    bb{:?}: {{ ", id)?;

            if let Some(note) = block.note.as_deref() {
                write!(f, "// debug: {note}")?;
            }

            writeln!(f)?; // end the line
            write_block(block, f)?;
            writeln!(f, "    }}")?;
            writeln!(f, "")?;
        }

        Ok(())
    }
}

fn mutability(decl: &LocalDecl) -> &'static str {
    match decl.kind {
        LocalKind::User => "mut ",
        _ => "",
    }
}

fn write_block(block: &BasicBlockData, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for stmt in &block.statements {
        write!(f, "        ")?;
        write_statement(stmt, f)?;
        writeln!(f, ";")?;
    }

    if let Some(term) = &block.terminator {
        write!(f, "        ")?;
        write_terminator(term, f)?;
        writeln!(f, ";")?;
    }

    Ok(())
}

fn write_statement(stmt: &Statement, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &stmt.kind {
        StatementKind::Assign(place, rvalue) => {
            write_place(place, f)?;
            write!(f, " = ")?;
            write_rvalue(rvalue, f)
        }
        StatementKind::Nop => write!(f, "nop"),
    }
}

fn write_terminator(term: &Terminator, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &term.kind {
        TerminatorKind::Goto { target } => write!(f, "goto -> bb{:?}", target),
        TerminatorKind::UnresolvedGoto => write!(f, "unresolved_goto"),
        TerminatorKind::SwitchInt {
            discr,
            targets,
            otherwise,
        } => {
            write!(f, "switchInt(")?;
            write_operand(discr, f)?;
            write!(f, ") -> [")?;
            for (val, target) in targets {
                write!(f, "{}: bb{:?}, ", val, target)?;
            }
            write!(f, "otherwise: bb{:?}]", otherwise)
        }
        TerminatorKind::Return => write!(f, "return"),
        TerminatorKind::Unreachable => write!(f, "unreachable"),
        TerminatorKind::Call {
            func,
            args,
            destination,
            target,
        } => {
            write_place(destination, f)?;
            write!(f, " = ")?;
            write_operand(func, f)?;
            write!(f, "(")?;
            for (i, arg) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_operand(arg, f)?;
            }
            write!(f, ") -> bb{:?}", target)
        }
    }
}

fn write_place(place: &Place, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    for elem in place.projection.iter().rev() {
        match elem {
            PlaceElem::Deref => write!(f, "*")?,
            PlaceElem::Field(_, _) => {
                // Handled in the inner loop, but typically projections are written
                // as `local.proj1.proj2` or `(*local).proj1`.
                // For simplicity assuming no complex deref chains for now
                // or just printing struct.field.
            }
        }
    }

    write!(f, "%{:?}", place.local)?;

    for elem in &place.projection {
        match elem {
            PlaceElem::Deref => {} // handled by prefix *
            PlaceElem::Field(idx, _) => write!(f, ".{:?}", idx)?,
        }
    }
    Ok(())
}

fn write_operand(op: &Operand, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match op {
        Operand::Copy(place) => write_place(place, f),
        Operand::Move(place) => {
            write!(f, "move ")?;
            write_place(place, f)
        }
        Operand::Constant(c) => write_constant(c, f),
    }
}

fn write_constant(c: &Constant, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &c.value {
        ConstantKind::Bool(b) => write!(f, "{}", b),
        ConstantKind::Rune(c) => write!(f, "{:?}", c),
        ConstantKind::String(s) => write!(f, "{:?}", s),
        ConstantKind::Integer(i) => write!(f, "const {}", i),
        ConstantKind::Float(fl) => write!(f, "const {}", fl),
        ConstantKind::Unit => write!(f, "()"),
        ConstantKind::Function(def_id, _) => write!(f, "fn({:?})", def_id),
    }
}

fn write_rvalue(rvalue: &Rvalue, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match rvalue {
        Rvalue::Use(op) => write_operand(op, f),
        Rvalue::UnaryOp { op, operand } => {
            write!(f, "{:?}", op)?; // Simple debug print for op enum
            write_operand(operand, f)
        }
        Rvalue::BinaryOp { op, lhs, rhs } => {
            write_operand(lhs, f)?;
            write!(f, " {:?} ", op)?; // Simple debug print for op enum
            write_operand(rhs, f)
        }
        Rvalue::Cast { operand, ty } => {
            write_operand(operand, f)?;
            write!(f, " as {:?}", ty)
        }
        Rvalue::Aggregate { kind, fields } => {
            write!(f, "{:?} {{ ", kind)?;
            for (i, field) in fields.iter_enumerated() {
                if i.index() > 0 {
                    write!(f, ", ")?;
                }
                write_operand(field, f)?;
            }
            write!(f, " }}")
        }
    }
}
