//! PatternMatrix data types and the AST-facing matcher adapter compiler.
//!
//! Compiles a list of clause patterns into the current AST-free `Matcher` shape
//! so source patterns, bindings, guard calls, and diagnostics have one
//! normalized input. Runtime decision ownership then moves through
//! `dispatch_matrix::pattern` into `DispatchMatrix`/`DispatchGraph`; `Matcher`
//! remains the backend ABI that inline lowering and receive records consume.
//!
//! Algorithm: Maranget-lite. First column with a constructor pattern drives
//! specialization. Wildcards/Vars participate in every specialization
//! (their bindings are recorded). Patterns we don't constructor-specialize
//! (Map, Bitstring, Pinned) lower as sequential Matcher tests.

use crate::ast::{Expr, Pattern, Spanned};
use crate::diag::Span;
use crate::exec::matcher::{GuardExpr, InputId, Matcher, MatcherInput, PinnedId, PinnedInput};
use crate::fz_ir::Var;
use crate::types::Ty;

pub(crate) mod analysis;
pub(crate) mod builder;
pub(crate) mod collect;
pub(crate) mod guard;
pub(crate) mod pattern_ops;

#[cfg(test)]
mod pattern_matrix_test;

#[cfg(test)]
use std::cell::Cell;

#[cfg(test)]
pub use analysis::is_inexhaustive;
pub use analysis::{find_unreachable_rows, is_inexhaustive_with_domains};
pub(crate) use collect::{collect_guard_capture_names, collect_matcher_pattern_bindings};
pub use guard::compile_guard_expr_subset;

use builder::MatcherBuilder;
use collect::collect_pinned_names;

/// Opaque handle into the caller's body table. The PatternMatrix never lowers
/// bodies; it routes Leaves to the caller's body-lowering callback by id.
///
/// PatternMatrix rows must be supplied in source order with strictly increasing
/// `BodyId`s. Specialization preserves row priority by sorting merged rows on
/// this id after it combines constructor-specific and default rows.
pub type BodyId = u32;

#[derive(Debug, Clone)]
pub struct Row {
    /// Column patterns. `patterns.len()` must equal `PatternMatrix::subjects.len()`
    /// at every step of compilation. Specialization may grow or shrink this
    /// vector (e.g. tuple-arity-3 specialization replaces one column with three).
    pub patterns: Vec<Spanned<Pattern>>,
    /// `@spec` annotation tests evaluated at leaf-resolution time, before
    /// the guard. Each (var, descr) emits `TypeTest(var, descr)`; on fail,
    /// the PatternMatrix falls through to the next row.
    pub preconditions: Vec<(Var, Ty)>,
    /// Bindings already proven while specialization removed or expanded
    /// columns. Remaining column bindings are collected when the leaf forms.
    pub bindings: Vec<(String, SubjectRef)>,
    pub guard: Option<Spanned<Expr>>,
    pub body_id: BodyId,
}

#[derive(Debug, Clone)]
pub struct PatternMatrix {
    pub subjects: Vec<Var>,
    pub rows: Vec<Row>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SubjectRef {
    Var(Var),
    TupleField { tuple: Box<SubjectRef>, index: u32 },
    ListHead(Box<SubjectRef>),
    ListTail(Box<SubjectRef>),
}

#[derive(Debug, Clone)]
pub(crate) struct CompilePatternMatrix {
    pub(crate) subjects: Vec<SubjectRef>,
    pub(crate) rows: Vec<Row>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubjectDomain {
    Any,
    List,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PatternMatrixCompileError {
    UnsupportedGuardExpr,
    UnsupportedMapKey,
    UnknownSubject(Var),
    UnknownPinned(String),
    UnknownGuardVar(String),
    GuardCallCycle(String, usize),
    NonMonotonicBodyId { previous: BodyId, current: BodyId },
}

/// Compile a PatternMatrix into the AST-free `Matcher` adapter representation.
pub fn compile_pattern_matrix(pattern_matrix: PatternMatrix) -> Result<Matcher, PatternMatrixCompileError> {
    let mut resolver = |_name: &str,
                        _arity: usize,
                        _args: Vec<GuardExpr>|
     -> Result<Option<GuardExpr>, PatternMatrixCompileError> { Ok(None) };
    compile_pattern_matrix_with_guard_resolver(pattern_matrix, &mut resolver)
}

pub fn compile_pattern_matrix_with_guard_resolver<F>(
    pattern_matrix: PatternMatrix,
    guard_call_resolver: &mut F,
) -> Result<Matcher, PatternMatrixCompileError>
where
    F: FnMut(&str, usize, Vec<GuardExpr>) -> Result<Option<GuardExpr>, PatternMatrixCompileError>,
{
    use std::collections::HashMap;

    validate_source_order(&pattern_matrix)?;
    #[cfg(test)]
    COMPILE_COUNT.with(|count| count.set(count.get() + 1));

    let input_vars = pattern_matrix.subjects.clone();
    let pinned_names = collect_pinned_names(&pattern_matrix);
    let inputs: Vec<MatcherInput> = input_vars
        .iter()
        .copied()
        .map(|v| MatcherInput {
            var: Some(v),
            span: Span::DUMMY,
        })
        .collect();
    let input_by_var: HashMap<Var, InputId> = input_vars
        .into_iter()
        .enumerate()
        .map(|(i, v)| (v, InputId(i as u32)))
        .collect();
    let pinned: Vec<PinnedInput> = pinned_names
        .iter()
        .map(|name| PinnedInput {
            name: name.clone(),
            var: None,
            span: Span::DUMMY,
        })
        .collect();
    let pinned_by_name: HashMap<String, PinnedId> = pinned_names
        .into_iter()
        .enumerate()
        .map(|(i, name)| (name, PinnedId(i as u32)))
        .collect();

    let mut builder = MatcherBuilder {
        input_by_var,
        pinned_by_name,
        nodes: Vec::new(),
        prepared_keys: Vec::new(),
        guard_call_resolver,
    };
    let root = builder.compile_inner(CompilePatternMatrix {
        subjects: pattern_matrix.subjects.into_iter().map(SubjectRef::Var).collect(),
        rows: pattern_matrix.rows,
    })?;
    Ok(Matcher {
        inputs,
        pinned,
        prepared_keys: builder.prepared_keys,
        nodes: builder.nodes,
        root,
    })
}

fn validate_source_order(pattern_matrix: &PatternMatrix) -> Result<(), PatternMatrixCompileError> {
    for pair in pattern_matrix.rows.windows(2) {
        let previous = pair[0].body_id;
        let current = pair[1].body_id;
        if previous >= current {
            return Err(PatternMatrixCompileError::NonMonotonicBodyId { previous, current });
        }
    }
    Ok(())
}

#[cfg(test)]
thread_local! {
    pub(crate) static COMPILE_COUNT: Cell<usize> = const { Cell::new(0) };
}

#[cfg(test)]
pub fn reset_compile_count() {
    COMPILE_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub fn compile_count() -> usize {
    COMPILE_COUNT.with(Cell::get)
}
