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
    pub deref_vars: Vec<DerefVar>,
}

/// Diagnostics from match compilation.
#[derive(Clone, Debug)]
pub struct Diagnostics {
    pub missing: bool,
    pub reachable: Vec<ArmId>,
}

/// The result of compiling a pattern match expression.
#[derive(Debug)]
pub struct MatchReport<'ctx> {
    pub tree: MatchTree<'ctx>,
    pub diagnostics: Diagnostics,
}

#[derive(Clone, Debug)]
pub struct DerefVar {
    pub deref: usize,
    pub base: usize,
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
    /// The binding mode (ByValue or ByRef).
    pub mode: crate::hir::BindingMode,
    /// Whether the binding is mutable.
    pub mutable: bool,
    /// The span of the binding pattern.
    pub span: Span,
    /// The match-tree variable this binding corresponds to.
    pub variable: Variable<'ctx>,
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
    Variant { name: Symbol, index: usize },
    Literal(LiteralKey),
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

    /// Checks if a guard evaluates to true, running the body if it does.
    Guard(ExprId, Body<'ctx>, Box<Decision<'ctx>>),

    /// Checks if a value is any of the given patterns.
    Switch(Variable<'ctx>, Vec<Case<'ctx>>, Option<Box<Decision<'ctx>>>),
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
                deref_vars: Vec::new(),
            },
            diagnostics: Diagnostics {
                missing: false,
                reachable: Vec::new(),
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
                    deref_vars: Vec::new(),
                },
                diagnostics: Diagnostics {
                    missing: false,
                    reachable: Vec::new(),
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
            deref_vars: compiler.deref_vars,
        },
        diagnostics,
    }
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
            Decision::Guard(_, _, fallback) => {
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
                        Constructor::Variant { name, .. } => {
                            terms.push(Term::new(
                                *var,
                                gcx.symbol_text(*name).to_string(),
                                case.arguments.clone(),
                            ));
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
    /// Bindings accumulated as patterns are processed.
    bindings: Vec<Binding<'ctx>>,
}

impl<'ctx> Row<'ctx> {
    fn new(columns: Vec<Column<'ctx>>, guard: Option<ExprId>, body: Body<'ctx>) -> Self {
        Self {
            columns,
            guard,
            body,
            bindings: Vec::new(),
        }
    }

    /// Creates a new row preserving the given bindings.
    fn with_bindings(
        columns: Vec<Column<'ctx>>,
        guard: Option<ExprId>,
        body: Body<'ctx>,
        bindings: Vec<Binding<'ctx>>,
    ) -> Self {
        Self {
            columns,
            guard,
            body,
            bindings,
        }
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
    deref_vars: Vec<DerefVar>,
    deref_var_map: HashMap<usize, Variable<'ctx>>,
}

impl<'ctx> Compiler<'ctx> {
    fn new(gcx: GlobalContext<'ctx>) -> Self {
        Self {
            variable_id: 0,
            gcx,
            diagnostics: Diagnostics {
                missing: false,
                reachable: Vec::new(),
            },
            deref_vars: Vec::new(),
            deref_var_map: HashMap::new(),
        }
    }

    fn compile(&mut self, rows: Vec<Row<'ctx>>) -> (Decision<'ctx>, Diagnostics) {
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

        self.peel_deref_patterns(&mut rows);
        expand_or_patterns(&mut rows);

        for row in &mut rows {
            self.move_variable_patterns(row);
        }

        if rows.first().map_or(false, |c| c.columns.is_empty()) {
            let row = rows.remove(0);
            self.diagnostics.reachable.push(row.body.arm);

            // Create a body with the accumulated bindings
            let body = Body::with_bindings(row.body.arm, row.bindings);

            return if let Some(guard) = row.guard {
                Decision::Guard(guard, body, Box::new(self.compile_rows(rows)))
            } else {
                Decision::Success(body)
            };
        }

        let branch_var = self.branch_variable(&rows);

        // Peel off reference to get the actual type for matching
        // This handles match ergonomics where scrutinee is &T but patterns match T
        let match_ty = match branch_var.ty.kind() {
            TyKind::Reference(inner, _) => inner,
            _ => branch_var.ty,
        };

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
                let vars = self.new_variables(items);
                let cases = vec![(Constructor::Tuple(items.len()), vars, Vec::new())];

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
                        let mut cols = row.columns;
                        let vars = cases[idx].1.clone();
                        self.apply_field_patterns(&mut cols, &vars, subpatterns, col.pattern.span);
                        cases[idx].2.push(Row::with_bindings(
                            cols,
                            row.guard,
                            row.body,
                            row.bindings,
                        ));
                    }
                    PatternKind::Leaf { subpatterns } => {
                        let idx = 0;
                        let mut cols = row.columns;
                        let vars = cases[idx].1.clone();
                        self.apply_field_patterns(&mut cols, &vars, subpatterns, col.pattern.span);
                        cases[idx].2.push(Row::with_bindings(
                            cols,
                            row.guard,
                            row.body,
                            row.bindings,
                        ));
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
                        let cols = row.columns;
                        cases[idx].2.push(Row::with_bindings(
                            cols,
                            row.guard,
                            row.body,
                            row.bindings,
                        ));
                    }
                    PatternKind::Or(_) => {
                        unreachable!("or-patterns should be expanded before compilation")
                    }
                    PatternKind::Binding { .. } | PatternKind::Wild => {
                        unreachable!("binding pattern should have been moved")
                    }
                    PatternKind::Deref { .. } => {
                        unreachable!("deref patterns should be lowered in MIR")
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
    fn move_variable_patterns(&self, row: &mut Row<'ctx>) {
        let mut new_columns = Vec::new();
        for col in row.columns.drain(..) {
            match &col.pattern.kind {
                PatternKind::Binding {
                    name,
                    local,
                    ty,
                    mode,
                } => {
                    row.bindings.push(Binding {
                        name: *name,
                        local: *local,
                        ty: *ty,
                        mode: *mode,
                        mutable: true,
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

    /// Given a row, returns the variable in that row that's referred to the
    /// most across all rows.
    fn peel_deref_patterns(&mut self, rows: &mut [Row<'ctx>]) {
        for row in rows {
            let mut new_columns = Vec::with_capacity(row.columns.len());
            for col in row.columns.drain(..) {
                let mut pattern = col.pattern;
                let mut variable = col.variable;

                loop {
                    match pattern.kind {
                        PatternKind::Deref { pattern: inner } => {
                            let inner = *inner;
                            variable = self.deref_variable(variable, inner.ty);
                            pattern = inner;
                        }
                        _ => {
                            new_columns.push(Column::new(variable, pattern));
                            break;
                        }
                    }
                }
            }
            row.columns = new_columns;
        }
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

    fn deref_variable(&mut self, base: Variable<'ctx>, inner_ty: Ty<'ctx>) -> Variable<'ctx> {
        if let Some(var) = self.deref_var_map.get(&base.id) {
            return *var;
        }
        let var = self.new_variable(inner_ty);
        self.deref_var_map.insert(base.id, var);
        self.deref_vars.push(DerefVar {
            deref: var.id,
            base: base.id,
        });
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
}

impl<'ctx> Term<'ctx> {
    fn new(variable: Variable<'ctx>, name: String, arguments: Vec<Variable<'ctx>>) -> Self {
        Self {
            variable,
            name,
            arguments,
        }
    }

    fn pattern_name(
        &self,
        terms: &[Term<'ctx>],
        mapping: &HashMap<Variable<'ctx>, usize>,
    ) -> String {
        if self.arguments.is_empty() {
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
        EnumVariantKind::Tuple(fields) => fields.iter().map(|field| field.ty).collect(),
    }
}

fn literal_key(pattern: &Pattern<'_>) -> LiteralKey {
    match &pattern.kind {
        PatternKind::Constant { value } => match &value.value {
            ConstantKind::Integer(i) => LiteralKey::Integer(*i),
            ConstantKind::Float(f) => LiteralKey::Float(f.to_bits()),
            ConstantKind::Rune(r) => LiteralKey::Rune(*r),
            ConstantKind::String(s) => LiteralKey::String(*s),
            ConstantKind::Bool(_) | ConstantKind::Unit => {
                unreachable!("boolean or unit literal used as infinite constructor")
            }
            ConstantKind::ConstParam(_) => {
                unreachable!("const parameters are not supported in patterns")
            }
        },
        PatternKind::Or(_) => unreachable!("or-patterns should be expanded before compilation"),
        _ => {
            unreachable!("expected literal pattern")
        }
    }
}

/// Expands rows containing OR patterns into individual rows, such that each
/// branch in the OR produces its own row.
fn expand_or_patterns<'ctx>(rows: &mut Vec<Row<'ctx>>) {
    if !rows
        .iter()
        .any(|r| r.columns.iter().any(|c| pattern_has_or(&c.pattern)))
    {
        return;
    }

    let mut new_rows = Vec::with_capacity(rows.len());
    let mut found = true;

    while found {
        found = false;

        for row in rows.drain(0..) {
            let res = row.columns.iter().enumerate().find_map(|(idx, col)| {
                if pattern_has_or(&col.pattern) {
                    Some((idx, &col.pattern))
                } else {
                    None
                }
            });

            if let Some((idx, pat)) = res {
                found = true;
                let expanded = expand_pattern_or(pat);

                for pattern in expanded {
                    let mut new_row = row.clone();
                    new_row.columns[idx].pattern = pattern;
                    new_rows.push(new_row);
                }
            } else {
                new_rows.push(row);
            }
        }

        std::mem::swap(rows, &mut new_rows);
    }
}

fn pattern_has_or(pattern: &Pattern<'_>) -> bool {
    match &pattern.kind {
        PatternKind::Or(_) => true,
        PatternKind::Leaf { subpatterns } | PatternKind::Variant { subpatterns, .. } => subpatterns
            .iter()
            .any(|field| pattern_has_or(&field.pattern)),
        _ => false,
    }
}

fn expand_pattern_or<'ctx>(pattern: &Pattern<'ctx>) -> Vec<Pattern<'ctx>> {
    match &pattern.kind {
        PatternKind::Or(patterns) => patterns
            .iter()
            .flat_map(|pat| expand_pattern_or(pat))
            .collect(),
        PatternKind::Leaf { subpatterns } => expand_field_patterns(subpatterns)
            .into_iter()
            .map(|fields| Pattern {
                ty: pattern.ty,
                span: pattern.span,
                kind: PatternKind::Leaf {
                    subpatterns: fields,
                },
            })
            .collect(),
        PatternKind::Variant {
            definition,
            variant,
            subpatterns,
        } => expand_field_patterns(subpatterns)
            .into_iter()
            .map(|fields| Pattern {
                ty: pattern.ty,
                span: pattern.span,
                kind: PatternKind::Variant {
                    definition: *definition,
                    variant: *variant,
                    subpatterns: fields,
                },
            })
            .collect(),
        _ => vec![pattern.clone()],
    }
}

fn expand_field_patterns<'ctx>(subpatterns: &[FieldPattern<'ctx>]) -> Vec<Vec<FieldPattern<'ctx>>> {
    let mut acc: Vec<Vec<FieldPattern<'ctx>>> = vec![Vec::new()];

    for field in subpatterns {
        let expanded = expand_pattern_or(&field.pattern);
        let mut next = Vec::new();

        for base in &acc {
            for pat in &expanded {
                let mut new_base = base.clone();
                new_base.push(FieldPattern {
                    index: field.index,
                    pattern: pat.clone(),
                });
                next.push(new_base);
            }
        }

        acc = next;
    }

    acc
}
