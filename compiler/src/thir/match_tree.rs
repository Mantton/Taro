#![allow(clippy::new_without_default)]

//! Shared pattern match decision tree compiler used by exhaustiveness and MIR lowering.
use crate::{
    compile::context::GlobalContext,
    hir::NodeID,
    sema::{
        models::{AdtDef, AdtKind, EnumVariant, EnumVariantKind, Ty, TyKind},
        tycheck::utils::instantiate::instantiate_enum_definition_with_args,
    },
    span::{Span, Symbol},
    thir::{ArmId, ConstantKind, ExprId, FieldPattern, Pattern, PatternKind, ThirFunction},
};
use std::collections::{HashMap, HashSet};

/// A compiled match tree plus its root variable.
#[derive(Debug)]
pub struct MatchTree<'ctx> {
    pub root_var: Variable<'ctx>,
    pub decision: Decision<'ctx>,
}

/// Diagnostics from match compilation.
#[derive(Clone, Debug)]
pub struct Diagnostics {
    pub missing: bool,
    pub reachable: HashSet<ArmId>,
}

/// The result of compiling a pattern match expression.
#[derive(Debug)]
pub struct MatchReport<'ctx> {
    pub tree: MatchTree<'ctx>,
    pub diagnostics: Diagnostics,
}

/// A captured binding from a pattern.
#[derive(Clone, Debug)]
pub struct Binding<'ctx> {
    /// The name of the binding.
    pub name: Symbol,
    /// The pattern-local ID (used to map to MIR locals).
    pub local: NodeID,
    /// The type of the binding.
    pub ty: Ty<'ctx>,

    /// The span of the binding pattern.
    pub span: Span,
    /// The match-tree variable this binding corresponds to.
    pub variable: Variable<'ctx>,
}

/// A runtime type test on one structural projection. Bound tests also expose
/// the converted value in a fresh variable for this candidate arm.
#[derive(Debug, Clone)]
pub struct TypeTest<'ctx> {
    pub source: Variable<'ctx>,
    pub target: Ty<'ctx>,
    pub converted: Option<Variable<'ctx>>,
    pub prepared: Option<Variable<'ctx>>,
}

#[derive(Debug, Clone)]
pub struct PreparedTypeTest<'ctx> {
    pub source: Variable<'ctx>,
    pub target: Ty<'ctx>,
    pub result: Variable<'ctx>,
}

/// The body of code to evaluate in case of a match.
#[derive(Clone, Debug)]
pub struct Body<'ctx> {
    pub arm: ArmId,
    /// Bindings captured from the pattern, mapped to their tree variables.
    pub bindings: Vec<Binding<'ctx>>,
}

impl<'ctx> Body<'ctx> {
    fn new(arm: ArmId) -> Self {
        Self {
            arm,
            bindings: Vec::new(),
        }
    }

    fn with_bindings(arm: ArmId, bindings: Vec<Binding<'ctx>>) -> Self {
        Self { arm, bindings }
    }
}

/// A type constructor.
#[derive(Debug, Clone, Eq, PartialEq)]
pub enum Constructor {
    Bool(bool),
    Tuple(usize),
    Struct(Symbol),
    Variant { name: Symbol, index: usize },
    Literal(LiteralKey),
    Interval(std::ops::RangeInclusive<i128>),
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum LiteralKey {
    Integer(u64),
    Float(u64),
    Rune(char),
    String(Symbol),
}

/// A variable used in a match expression.
#[derive(Eq, PartialEq, Hash, Clone, Copy, Debug)]
pub struct Variable<'ctx> {
    pub id: usize,
    pub ty: Ty<'ctx>,
}

/// A case in a decision tree to test against a variable.
#[derive(Debug, Clone)]
pub struct Case<'ctx> {
    pub constructor: Constructor,
    pub arguments: Vec<Variable<'ctx>>,
    pub body: Decision<'ctx>,
}

impl<'ctx> Case<'ctx> {
    fn new(constructor: Constructor, arguments: Vec<Variable<'ctx>>, body: Decision<'ctx>) -> Self {
        Self {
            constructor,
            arguments,
            body,
        }
    }
}

/// A decision tree compiled from a list of match cases.
#[derive(Debug, Clone)]
pub enum Decision<'ctx> {
    /// A pattern is matched and the right-hand value is to be returned.
    Success(Body<'ctx>),

    /// A pattern is missing.
    Failure,

    /// A candidate arm tests its dynamic types before its source guard.
    Guard {
        prepare: Vec<PreparedTypeTest<'ctx>>,
        tests: Vec<TypeTest<'ctx>>,
        guard: Option<ExprId>,
        body: Body<'ctx>,
        fallback: Box<Decision<'ctx>>,
    },

    /// Read a referent for structural matching, preserving the original
    /// reference variable for any plain identifier bindings in other arms.
    Dereference {
        source: Variable<'ctx>,
        target: Variable<'ctx>,
        next: Box<Decision<'ctx>>,
    },

    /// Checks if a value is any of the given patterns.
    Switch(Variable<'ctx>, Vec<Case<'ctx>>, Option<Box<Decision<'ctx>>>),
}

impl Decision<'_> {
    pub fn has_guard(&self) -> bool {
        match self {
            Decision::Guard { .. } => true,
            Decision::Dereference { next, .. } => next.has_guard(),
            Decision::Switch(_, cases, fallback) => {
                cases.iter().any(|case| case.body.has_guard())
                    || fallback.as_deref().is_some_and(Decision::has_guard)
            }
            Decision::Success(_) | Decision::Failure => false,
        }
    }
}

/// Compile a match expression into a decision tree + diagnostics.
pub fn compile_match<'ctx>(
    gcx: GlobalContext<'ctx>,
    func: &ThirFunction<'ctx>,
    scrutinee: ExprId,
    arms: &[ArmId],
) -> MatchReport<'ctx> {
    let scrutinee_ty = func.exprs[scrutinee].ty;
    let mut compiler = Compiler::new(gcx);
    let scrutinee_var = compiler.new_variable(scrutinee_ty);

    if matches!(scrutinee_ty.kind(), TyKind::Error | TyKind::Infer(_)) {
        return MatchReport {
            tree: MatchTree {
                root_var: scrutinee_var,
                decision: Decision::Failure,
            },
            diagnostics: Diagnostics {
                missing: false,
                reachable: HashSet::new(),
            },
        };
    }

    let mut rows = Vec::with_capacity(arms.len());
    for arm_id in arms {
        let arm = &func.arms[*arm_id];
        if matches!(arm.pattern.ty.kind(), TyKind::Error | TyKind::Infer(_)) {
            return MatchReport {
                tree: MatchTree {
                    root_var: scrutinee_var,
                    decision: Decision::Failure,
                },
                diagnostics: Diagnostics {
                    missing: false,
                    reachable: HashSet::new(),
                },
            };
        }

        rows.push(Row::new(
            vec![Column::new(scrutinee_var, (*arm.pattern).clone())],
            arm.guard,
            Body::new(*arm_id),
        ));
    }

    let (decision, diagnostics) = compiler.compile(rows);
    MatchReport {
        tree: MatchTree {
            root_var: scrutinee_var,
            decision,
        },
        diagnostics,
    }
}

/// Local bindings must cover every possible value of their scrutinee.
pub fn is_irrefutable<'ctx>(gcx: GlobalContext<'ctx>, pattern: &Pattern<'ctx>) -> bool {
    if matches!(pattern.ty.kind(), TyKind::Error | TyKind::Infer(_)) {
        return true;
    }
    let mut compiler = Compiler::new(gcx);
    let variable = compiler.new_variable(pattern.ty);
    let row = Row::new(
        vec![Column::new(variable, pattern.clone())],
        None,
        Body::new(ArmId::from_usize(0)),
    );
    !compiler.compile(vec![row]).1.missing
}

impl<'ctx> MatchReport<'ctx> {
    /// Returns a list of patterns not covered by the match expression.
    pub fn missing_patterns(&self, gcx: GlobalContext<'ctx>) -> Vec<String> {
        let mut names = HashSet::new();
        let mut steps = Vec::new();

        self.add_missing_patterns(&self.tree.decision, &mut steps, &mut names, gcx);

        let mut missing: Vec<String> = names.into_iter().collect();
        missing.sort();
        missing
    }

    fn add_missing_patterns(
        &self,
        node: &Decision<'ctx>,
        terms: &mut Vec<Term<'ctx>>,
        missing: &mut HashSet<String>,
        gcx: GlobalContext<'ctx>,
    ) {
        match node {
            Decision::Success(_) => {}
            Decision::Failure => {
                let mut mapping = HashMap::new();

                for (index, step) in terms.iter().enumerate() {
                    mapping.insert(step.variable, index);
                }

                let name = terms
                    .first()
                    .map(|term| term.pattern_name(terms, &mapping))
                    .unwrap_or_else(|| "_".to_string());

                missing.insert(name);
            }
            Decision::Dereference {
                source,
                target,
                next,
            } => {
                // A parent's payload names the reference variable. Follow its
                // structural read when spelling nested missing patterns.
                let mut changed = Vec::new();
                for (term_index, term) in terms.iter_mut().enumerate() {
                    for (arg_index, argument) in term.arguments.iter_mut().enumerate() {
                        if argument == source {
                            *argument = *target;
                            changed.push((term_index, arg_index));
                        }
                    }
                }
                self.add_missing_patterns(next, terms, missing, gcx);
                for (term, arg) in changed {
                    terms[term].arguments[arg] = *source;
                }
            }
            Decision::Guard { fallback, .. } => {
                self.add_missing_patterns(fallback, terms, missing, gcx);
            }
            Decision::Switch(var, cases, fallback) => {
                for case in cases {
                    match &case.constructor {
                        Constructor::Bool(true) => {
                            terms.push(Term::new(*var, "true".to_string(), Vec::new()));
                        }
                        Constructor::Bool(false) => {
                            terms.push(Term::new(*var, "false".to_string(), Vec::new()));
                        }
                        Constructor::Interval(range) => {
                            let name = if matches!(var.ty.kind(), TyKind::Rune) {
                                format!("{:?}", char::from_u32(*range.start() as u32).unwrap())
                            } else {
                                range.start().to_string()
                            };
                            terms.push(Term::new(*var, name, Vec::new()));
                        }
                        Constructor::Literal(_) => {
                            terms.push(Term::new(*var, "_".to_string(), Vec::new()));
                        }
                        Constructor::Tuple(arity) => {
                            let name = if *arity == 0 {
                                "()".to_string()
                            } else {
                                String::new()
                            };
                            terms.push(Term::new(*var, name, case.arguments.clone()));
                        }
                        Constructor::Struct(name) => {
                            let TyKind::Adt(def, _) = var.ty.kind() else {
                                unreachable!()
                            };
                            let fields = gcx
                                .get_struct_definition(def.id)
                                .fields
                                .iter()
                                .map(|field| gcx.symbol_text(field.name).to_string())
                                .collect();
                            terms.push(Term::named(
                                *var,
                                gcx.symbol_text(*name).to_string(),
                                case.arguments.clone(),
                                fields,
                            ));
                        }
                        Constructor::Variant { name, index } => {
                            let mut term = Term::new(
                                *var,
                                gcx.symbol_text(*name).to_string(),
                                case.arguments.clone(),
                            );
                            if let TyKind::Adt(def, _) = var.ty.kind()
                                && let EnumVariantKind::Struct(fields) =
                                    gcx.get_enum_definition(def.id).variants[*index].kind
                            {
                                term.field_names = Some(
                                    fields
                                        .iter()
                                        .map(|field| {
                                            field
                                                .label
                                                .map(|name| gcx.symbol_text(name).to_string())
                                                .unwrap_or_else(|| "_".into())
                                        })
                                        .collect(),
                                );
                            }
                            terms.push(term);
                        }
                    }

                    self.add_missing_patterns(&case.body, terms, missing, gcx);
                    terms.pop();
                }

                if let Some(node) = fallback {
                    self.add_missing_patterns(node, terms, missing, gcx);
                }
            }
        }
    }
}

/// A column in a pattern matching table.
#[derive(Clone, Debug)]
struct Column<'ctx> {
    variable: Variable<'ctx>,
    pattern: Pattern<'ctx>,
}

impl<'ctx> Column<'ctx> {
    fn new(variable: Variable<'ctx>, pattern: Pattern<'ctx>) -> Self {
        Self { variable, pattern }
    }
}

/// A single case (or row) in a match expression/table.
#[derive(Clone, Debug)]
struct Row<'ctx> {
    columns: Vec<Column<'ctx>>,
    guard: Option<ExprId>,
    body: Body<'ctx>,
    tests: Vec<TypeTest<'ctx>>,
    /// Bindings accumulated as patterns are processed.
    bindings: Vec<Binding<'ctx>>,
}

impl<'ctx> Row<'ctx> {
    fn new(columns: Vec<Column<'ctx>>, guard: Option<ExprId>, body: Body<'ctx>) -> Self {
        Self { columns, guard, body, bindings: Vec::new(), tests: Vec::new() }
    }

    fn remove_column(&mut self, variable: &Variable<'ctx>) -> Option<Column<'ctx>> {
        self.columns
            .iter()
            .position(|c| &c.variable == variable)
            .map(|idx| self.columns.remove(idx))
    }
}

/// The `match` compiler.
struct Compiler<'ctx> {
    variable_id: usize,
    gcx: GlobalContext<'ctx>,
    diagnostics: Diagnostics,
    has_borrowed_type_tests: bool,
}

impl<'ctx> Compiler<'ctx> {
    fn new(gcx: GlobalContext<'ctx>) -> Self {
        Self {
            variable_id: 0,
            has_borrowed_type_tests: false,
            gcx,
            diagnostics: Diagnostics {
                missing: false,
                reachable: HashSet::new(),
            },
        }
    }

    fn compile(&mut self, rows: Vec<Row<'ctx>>) -> (Decision<'ctx>, Diagnostics) {
        self.has_borrowed_type_tests = rows.iter().any(|r| r.guard.is_some())
            && rows.iter().any(|r| r.columns.iter().any(|c| needs_borrowed_type_test(&c.pattern)));
        let decision = self.compile_rows(rows);
        let diagnostics = Diagnostics {
            missing: self.diagnostics.missing,
            reachable: std::mem::take(&mut self.diagnostics.reachable),
        };
        (decision, diagnostics)
    }

    fn compile_rows(&mut self, mut rows: Vec<Row<'ctx>>) -> Decision<'ctx> {
        if rows.is_empty() {
            self.diagnostics.missing = true;
            return Decision::Failure;
        }

        for row in &mut rows {
            self.move_variable_patterns(row);
        }

        // Only expose projections that can be invalidated by this guard.
        // Splitting the enum first ensures we read fields of its active variant.
        let inspect = if self.has_borrowed_type_tests && rows[0].columns.is_empty()
            && rows[0].guard.is_some()
        {
            rows.iter().skip(1).flat_map(|r| &r.columns)
                .find(|col| needs_borrowed_type_test(&col.pattern))
                .map(|col| col.variable)
        } else {
            None
        };
        if inspect.is_none() && rows[0].columns.is_empty() {
            let mut row = rows.remove(0);
            self.diagnostics.reachable.insert(row.body.arm);

            // Create a body with the accumulated bindings
            let body = Body::with_bindings(row.body.arm, row.bindings);

            return if row.guard.is_some() || !row.tests.is_empty() {
                // Type tests cannot close an open hierarchy, but an unguarded
                // candidate does cover a later candidate requiring the same tests.
                if row.guard.is_none() {
                    rows.retain(|later| !row.tests.iter().all(|test| {
                        later.tests.iter().any(|other| {
                            test.source == other.source && test.target == other.target
                        })
                    }));
                }
                let prepare = if self.has_borrowed_type_tests && row.guard.is_some() {
                    self.prepare_borrowed_type_tests(&mut row.tests, &mut rows)
                } else {
                    Vec::new()
                };
                Decision::Guard {
                    prepare,
                    tests: row.tests,
                    guard: row.guard,
                    body,
                    fallback: Box::new(self.compile_rows(rows)),
                }
            } else {
                Decision::Success(body)
            };
        }

        let branch_var = inspect.unwrap_or_else(|| self.branch_variable(&rows));

        // Split alternatives only in the column being inspected. Alternatives
        // inside distinct constructor payloads need never be multiplied here.
        if rows.iter().any(|row| row.columns.iter().any(|col|
            col.variable == branch_var && matches!(col.pattern.kind, PatternKind::Or(_))
        )) {
            let mut expanded = Vec::new();
            for row in rows {
                let alternative = row.columns.iter().enumerate().find_map(|(index, col)| {
                    if col.variable == branch_var && let PatternKind::Or(parts) = &col.pattern.kind {
                        Some((index, parts))
                    } else {
                        None
                    }
                });
                if let Some((index, parts)) = alternative {
                    for part in parts {
                        let mut alternative = row.clone();
                        alternative.columns[index].pattern = part.clone();
                        expanded.push(alternative);
                    }
                } else {
                    expanded.push(row);
                }
            }
            return self.compile_rows(expanded);
        }

        if let TyKind::Reference(inner) = branch_var.ty.kind() {
            let target = self.new_variable(inner);
            for row in &mut rows {
                for column in &mut row.columns {
                    if column.variable == branch_var {
                        column.variable = target;
                    }
                }
            }
            let next = Box::new(self.compile_rows(rows));
            return Decision::Dereference {
                source: branch_var,
                target,
                next,
            };
        }

        let match_ty = branch_var.ty;

        match match_ty.kind() {
            TyKind::Bool => {
                let cases = vec![
                    (Constructor::Bool(false), Vec::new(), Vec::new()),
                    (Constructor::Bool(true), Vec::new(), Vec::new()),
                ];

                Decision::Switch(
                    branch_var,
                    self.compile_constructor_cases(rows, branch_var, cases),
                    None,
                )
            }
            TyKind::Tuple(items) => {
                let vars = self.new_variables(&items);
                let cases = vec![(Constructor::Tuple(items.len()), vars, Vec::new())];

                Decision::Switch(
                    branch_var,
                    self.compile_constructor_cases(rows, branch_var, cases),
                    None,
                )
            }
            TyKind::Adt(def, args) if def.kind == AdtKind::Struct => {
                let definition = crate::sema::tycheck::utils::instantiate::instantiate_struct_definition_with_args(self.gcx, self.gcx.get_struct_definition(def.id), args);
                let types: Vec<_> = definition.fields.iter().map(|field| field.ty).collect();
                let vars = self.new_variables(&types);
                let name = self.gcx.definition_ident(def.id).symbol;
                let cases = vec![(Constructor::Struct(name), vars, Vec::new())];
                Decision::Switch(
                    branch_var,
                    self.compile_constructor_cases(rows, branch_var, cases),
                    None,
                )
            }
            TyKind::Adt(def, args) if def.kind == AdtKind::Enum => {
                let enum_def = self.gcx.get_enum_definition(def.id);
                let enum_def = instantiate_enum_definition_with_args(self.gcx, &enum_def, args);
                let cases = enum_def
                    .variants
                    .iter()
                    .enumerate()
                    .map(|(idx, variant)| {
                        let vars = self.new_variables(&variant_field_types(*variant));
                        let cons = Constructor::Variant {
                            name: variant.name,
                            index: idx,
                        };
                        (cons, vars, Vec::new())
                    })
                    .collect();

                Decision::Switch(
                    branch_var,
                    self.compile_constructor_cases(rows, branch_var, cases),
                    None,
                )
            }
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Rune if rows.iter().any(|row| {
                row.columns.iter().any(|col| {
                    col.variable == branch_var && matches!(col.pattern.kind, PatternKind::Range(_))
                })
            }) => self.compile_range_cases(rows, branch_var),
            TyKind::Int(_) | TyKind::UInt(_) | TyKind::Float(_) | TyKind::Rune | TyKind::String => {
                let (cases, fallback) = self.compile_literal_cases(rows, branch_var);
                Decision::Switch(branch_var, cases, Some(fallback))
            }
            TyKind::Error | TyKind::Infer(_) => Decision::Failure,
            _ => {
                let (cases, fallback) = self.compile_literal_cases(rows, branch_var);
                Decision::Switch(branch_var, cases, Some(fallback))
            }
        }
    }

    /// Split the scalar domain only at pattern boundaries. Every value in one
    /// interval matches the same rows, in source order, even when guards overlap.
    fn compile_range_cases(&mut self, rows: Vec<Row<'ctx>>, var: Variable<'ctx>) -> Decision<'ctx> {
        use crate::sema::tycheck::utils::const_eval::integer_layout;
        let rune = matches!(var.ty.kind(), TyKind::Rune);
        let domain = if rune {
            0..=char::MAX as i128
        } else {
            integer_layout(self.gcx, var.ty).expect("integer range scrutinee").bounds()
        };
        let mut cuts = vec![*domain.start(), domain.end() + 1];
        if rune {
            cuts.extend([0xd800, 0xe000]);
        }
        let mut patterns = Vec::with_capacity(rows.len());
        for mut row in rows {
            let interval = row.remove_column(&var).map(|col| {
                let interval = match col.pattern.kind {
                    PatternKind::Range(interval) => interval,
                    PatternKind::Constant { value } => {
                        let scalar = match value.value {
                            ConstantKind::Rune(r) => r as i128,
                            ConstantKind::Integer(i) if *domain.start() < 0 => i as i64 as i128,
                            ConstantKind::Integer(i) => i as i128,
                            _ => unreachable!("checked scalar pattern"),
                        };
                        scalar..=scalar
                    }
                    _ => unreachable!("checked scalar column"),
                };
                cuts.extend([*interval.start(), interval.end() + 1]);
                interval
            });
            patterns.push((interval, row));
        }

        cuts.sort_unstable();
        cuts.dedup();
        let mut cases = Vec::new();
        for pair in cuts.windows(2) {
            let lo = pair[0];
            if rune && (0xd800..0xe000).contains(&lo) {
                continue;
            }
            let rows = patterns.iter()
                .filter(|(interval, _)| interval.as_ref().is_none_or(|r| r.contains(&lo)))
                .map(|(_, row)| row.clone())
                .collect();
            let constructor = Constructor::Interval(lo..=pair[1] - 1);
            cases.push(Case::new(constructor, Vec::new(), self.compile_rows(rows)));
        }
        Decision::Switch(var, cases, None)
    }

    /// Compiles the cases and fallback cases for literal patterns.
    fn compile_literal_cases(
        &mut self,
        rows: Vec<Row<'ctx>>,
        branch_var: Variable<'ctx>,
    ) -> (Vec<Case<'ctx>>, Box<Decision<'ctx>>) {
        let mut raw_cases: Vec<(Constructor, Vec<Variable<'ctx>>, Vec<Row<'ctx>>)> = Vec::new();
        let mut fallback_rows = Vec::new();
        let mut tested: HashMap<LiteralKey, usize> = HashMap::new();

        for mut row in rows {
            if let Some(col) = row.remove_column(&branch_var) {
                let key = literal_key(&col.pattern);
                let cons = Constructor::Literal(key.clone());

                if let Some(index) = tested.get(&key) {
                    raw_cases[*index].2.push(row);
                    continue;
                }

                tested.insert(key, raw_cases.len());

                let mut rows = fallback_rows.clone();
                rows.push(row);
                raw_cases.push((cons, Vec::new(), rows));
            } else {
                for (_, _, rows) in &mut raw_cases {
                    rows.push(row.clone());
                }
                fallback_rows.push(row);
            }
        }

        let cases = raw_cases
            .into_iter()
            .map(|(cons, vars, rows)| Case::new(cons, vars, self.compile_rows(rows)))
            .collect();

        (cases, Box::new(self.compile_rows(fallback_rows)))
    }

    /// Compiles the cases and sub cases for the constructor located at the
    /// column of the branching variable.
    fn compile_constructor_cases(
        &mut self,
        rows: Vec<Row<'ctx>>,
        branch_var: Variable<'ctx>,
        mut cases: Vec<(Constructor, Vec<Variable<'ctx>>, Vec<Row<'ctx>>)>,
    ) -> Vec<Case<'ctx>> {
        for mut row in rows {
            if let Some(col) = row.remove_column(&branch_var) {
                match &col.pattern.kind {
                    PatternKind::Variant {
                        definition,
                        variant,
                        subpatterns,
                    } => {
                        let idx = self.variant_index(*definition, *variant);
                        let vars = cases[idx].1.clone();
                        self.apply_field_patterns(&mut row.columns, &vars, subpatterns, col.pattern.span);
                        cases[idx].2.push(row);
                    }
                    PatternKind::Leaf { subpatterns } => {
                        let idx = 0;
                        let vars = cases[idx].1.clone();
                        self.apply_field_patterns(&mut row.columns, &vars, subpatterns, col.pattern.span);
                        cases[idx].2.push(row);
                    }
                    PatternKind::Constant { value } => {
                        let idx = match value.value {
                            ConstantKind::Bool(false) => 0,
                            ConstantKind::Bool(true) => 1,
                            ConstantKind::Unit => 0,
                            ConstantKind::ConstParam(_) => {
                                unreachable!("const parameters are not supported in patterns")
                            }
                            _ => unreachable!("non-constructor constant in constructor match"),
                        };
                        cases[idx].2.push(row);
                    }
                    PatternKind::Range(_) => unreachable!("range in a nonscalar column"),
                    PatternKind::Or(_) => {
                        unreachable!("or-patterns should be expanded before compilation")
                    }
                    PatternKind::At { .. } | PatternKind::TypeTest { .. } | PatternKind::Binding { .. } | PatternKind::Wild => {
                        unreachable!("binding pattern should have been moved")
                    }
                }
            } else {
                for (_, _, rows) in &mut cases {
                    rows.push(row.clone());
                }
            }
        }

        cases
            .into_iter()
            .map(|(cons, vars, rows)| Case::new(cons, vars, self.compile_rows(rows)))
            .collect()
    }

    /// Moves variable-only patterns/tests into the right-hand side/body of a
    /// case. Bindings are collected into row.bindings for later use.
    fn move_variable_patterns(&mut self, row: &mut Row<'ctx>) {
        let mut new_columns = Vec::new();
        for mut col in row.columns.drain(..) {
            while let PatternKind::At { binding, pattern } = col.pattern.kind {
                let PatternKind::Binding { name, local, ty } = binding.kind else {
                    unreachable!("the left side of @ is an identifier")
                };
                row.bindings.push(Binding { name, local, ty, span: binding.span, variable: col.variable });
                col.pattern = *pattern;
            }
            match &col.pattern.kind {
                PatternKind::TypeTest { target, binding } => {
                    let converted = binding.as_ref().map(|binding| {
                        let PatternKind::Binding { name, local, ty } = binding.kind else {
                            unreachable!("a typed pattern binds a single name")
                        };
                        let variable = self.new_variable(ty);
                        row.bindings.push(Binding { name, local, ty, span: binding.span, variable });
                        variable
                    });
                    row.tests.push(TypeTest { source: col.variable, target: *target, converted, prepared: None });
                }
                PatternKind::Binding { name, local, ty } => {
                    row.bindings.push(Binding {
                        name: *name,
                        local: *local,
                        ty: *ty,
                        span: col.pattern.span,
                        variable: col.variable,
                    });
                }
                PatternKind::Wild => {
                    // Wildcards don't create bindings, just skip them
                }
                _ => {
                    new_columns.push(col);
                }
            }
        }
        row.columns = new_columns;
    }

    /// A checked cast reads through a borrowed existential, even when the
    /// reference type is only known after monomorphization. A guard can
    /// replace that referent. Save each later inspection before running it;
    /// ordinary bindings of the reference still denote the original storage.
    fn prepare_borrowed_type_tests(
        &mut self,
        current: &mut [TypeTest<'ctx>],
        later: &mut [Row<'ctx>],
    ) -> Vec<PreparedTypeTest<'ctx>> {
        let mut requests = indexmap::IndexMap::new();
        for test in later.iter().flat_map(|row| &row.tests) {
            if test.prepared.is_none() && may_read_erased_reference(test.source.ty) {
                requests.entry((test.source, test.target)).or_insert(false);
            }
        }
        if requests.is_empty() {
            return Vec::new();
        }
        for test in current.iter().chain(later.iter().flat_map(|row| &row.tests)) {
            if test.converted.is_some()
                && let Some(needs_value) = requests.get_mut(&(test.source, test.target))
            {
                *needs_value = true;
            }
        }
        let mut prepared = Vec::with_capacity(requests.len());
        let mut results = HashMap::new();
        for ((source, target), needs_value) in requests {
            let ty = if needs_value { target.optional(self.gcx).0 } else { self.gcx.types.bool };
            let result = self.new_variable(ty);
            prepared.push(PreparedTypeTest { source, target, result });
            results.insert((source, target), result);
        }
        for test in current.iter_mut().chain(later.iter_mut().flat_map(|row| &mut row.tests)) {
            if let Some(result) = results.get(&(test.source, test.target)) {
                test.prepared = Some(*result);
            }
        }
        prepared
    }

    fn branch_variable(&self, rows: &[Row<'ctx>]) -> Variable<'ctx> {
        let mut counts: HashMap<Variable<'ctx>, usize> = HashMap::new();

        for row in rows {
            for col in &row.columns {
                *counts.entry(col.variable).or_insert(0_usize) += 1
            }
        }

        rows[0]
            .columns
            .iter()
            .map(|col| col.variable)
            .max_by_key(|var| counts[var])
            .unwrap()
    }

    /// Returns a new variable to use in the decision tree.
    fn new_variable(&mut self, ty: Ty<'ctx>) -> Variable<'ctx> {
        let var = Variable {
            id: self.variable_id,
            ty,
        };
        self.variable_id += 1;
        var
    }

    fn new_variables(&mut self, tys: &[Ty<'ctx>]) -> Vec<Variable<'ctx>> {
        tys.iter().map(|t| self.new_variable(*t)).collect()
    }

    fn variant_index(&self, definition: AdtDef, variant: EnumVariant<'ctx>) -> usize {
        let enum_def = self.gcx.get_enum_definition(definition.id);
        enum_def
            .variants
            .iter()
            .position(|v| v.def_id == variant.def_id)
            .expect("variant in enum definition")
    }

    fn apply_field_patterns(
        &self,
        cols: &mut Vec<Column<'ctx>>,
        vars: &[Variable<'ctx>],
        subpatterns: &[FieldPattern<'ctx>],
        span: Span,
    ) {
        let mut ordered: Vec<Option<Pattern<'ctx>>> = vec![None; vars.len()];
        for field in subpatterns {
            let idx = field.index.index();
            if idx < ordered.len() {
                ordered[idx] = Some(field.pattern.clone());
            }
        }

        for (var, pat) in vars.iter().zip(ordered) {
            let pat = pat.unwrap_or_else(|| Pattern {
                ty: var.ty,
                span,
                kind: PatternKind::Wild,
            });
            cols.push(Column::new(*var, pat));
        }
    }
}

/// Information about a single constructor/value used for missing pattern names.
#[derive(Debug)]
struct Term<'ctx> {
    variable: Variable<'ctx>,
    name: String,
    arguments: Vec<Variable<'ctx>>,
    field_names: Option<Vec<String>>,
}

impl<'ctx> Term<'ctx> {
    fn new(variable: Variable<'ctx>, name: String, arguments: Vec<Variable<'ctx>>) -> Self {
        Self {
            variable,
            name,
            arguments,
            field_names: None,
        }
    }

    fn named(
        variable: Variable<'ctx>,
        name: String,
        arguments: Vec<Variable<'ctx>>,
        field_names: Vec<String>,
    ) -> Self {
        Self {
            variable,
            name,
            arguments,
            field_names: Some(field_names),
        }
    }

    fn pattern_name(
        &self,
        terms: &[Term<'ctx>],
        mapping: &HashMap<Variable<'ctx>, usize>,
    ) -> String {
        if let Some(names) = &self.field_names {
            let fields = names
                .iter()
                .zip(&self.arguments)
                .map(|(name, argument)| {
                    let value = mapping
                        .get(argument)
                        .map(|&index| terms[index].pattern_name(terms, mapping))
                        .unwrap_or_else(|| "_".into());
                    format!("{name}: {value}")
                })
                .collect::<Vec<_>>()
                .join(", ");
            if fields.is_empty() {
                format!("{} {{}}", self.name)
            } else {
                format!("{} {{ {} }}", self.name, fields)
            }
        } else if self.arguments.is_empty() {
            self.name.to_string()
        } else {
            let args = self
                .arguments
                .iter()
                .map(|arg| {
                    mapping
                        .get(arg)
                        .map(|&idx| terms[idx].pattern_name(terms, mapping))
                        .unwrap_or_else(|| "_".to_string())
                })
                .collect::<Vec<_>>()
                .join(", ");

            format!("{}({})", self.name, args)
        }
    }
}

fn variant_field_types<'ctx>(variant: EnumVariant<'ctx>) -> Vec<Ty<'ctx>> {
    match variant.kind {
        EnumVariantKind::Unit => Vec::new(),
        EnumVariantKind::Tuple(fields) | EnumVariantKind::Struct(fields) => {
            fields.iter().map(|field| field.ty).collect()
        }
    }
}

fn literal_key(pattern: &Pattern<'_>) -> LiteralKey {
    match &pattern.kind {
        PatternKind::Constant { value } => match &value.value {
            ConstantKind::Integer(i) => LiteralKey::Integer(*i),
            ConstantKind::Float(f) => LiteralKey::Float(f.to_bits()),
            ConstantKind::Rune(r) => LiteralKey::Rune(*r),
            ConstantKind::String(s) => LiteralKey::String(*s),
            ConstantKind::Bytes(_)
            | ConstantKind::ConstArray(_)
            | ConstantKind::Bool(_)
            | ConstantKind::Unit => {
                unreachable!("boolean or unit literal used as infinite constructor")
            }
            ConstantKind::ConstParam(_) | ConstantKind::InterfaceConstant(..) => {
                unreachable!("symbolic constants are not supported in patterns")
            }
        },
        PatternKind::Or(_) => unreachable!("or-patterns should be expanded before compilation"),
        _ => {
            unreachable!("expected literal pattern")
        }
    }
}

fn may_read_erased_reference(ty: Ty<'_>) -> bool {
    match ty.kind() {
        TyKind::Reference(inner) => matches!(inner.kind(),
            TyKind::BoxedExistential { .. } | TyKind::Parameter(_) | TyKind::Alias { .. }),
        TyKind::Parameter(_) | TyKind::Alias { .. } => true,
        _ => false,
    }
}

fn needs_borrowed_type_test(pattern: &Pattern<'_>) -> bool {
    match &pattern.kind {
        PatternKind::TypeTest { .. } => may_read_erased_reference(pattern.ty),
        PatternKind::At { pattern, .. } => needs_borrowed_type_test(pattern),
        PatternKind::Or(parts) => parts.iter().any(needs_borrowed_type_test),
        PatternKind::Leaf { subpatterns } | PatternKind::Variant { subpatterns, .. } => {
            subpatterns.iter().any(|field| needs_borrowed_type_test(&field.pattern))
        }
        _ => false,
    }
}
