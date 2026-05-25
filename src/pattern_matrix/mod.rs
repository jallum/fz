//! PatternMatrix data types and Matcher compiler.
//!
//! Compiles a list of clause patterns into a shared Matcher graph, so that
//! cross-clause constructor tests (same arity, same atom) are emitted ONCE
//! and dispatched into per-clause continuations. Replaces the per-clause
//! `lower_pattern_bind` cascade currently duplicated across
//! `lower_multi_clause`, `lower_case`, and `lower_with`.
//!
//! Algorithm: Maranget-lite. First column with a constructor pattern drives
//! specialization. Wildcards/Vars participate in every specialization
//! (their bindings are recorded). Patterns we don't constructor-specialize
//! (Map, Bitstring, Pinned) lower as sequential Matcher tests.

use crate::ast::{Expr, Pattern, Spanned};
use crate::fz_ir::Var;

pub(crate) mod analysis;
pub(crate) mod builder;
pub(crate) mod collect;
pub(crate) mod guard;
pub(crate) mod pattern_ops;

#[cfg(test)]
mod tests;

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
    pub preconditions: Vec<(Var, crate::types::Ty)>,
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

/// Compile a PatternMatrix into the AST-free `Matcher`
/// representation.
pub fn compile_pattern_matrix(
    pattern_matrix: PatternMatrix,
) -> Result<crate::matcher::Matcher, PatternMatrixCompileError> {
    let mut resolver =
        |_name: &str,
         _arity: usize,
         _args: Vec<crate::matcher::GuardExpr>|
         -> Result<Option<crate::matcher::GuardExpr>, PatternMatrixCompileError> {
            Ok(None)
        };
    compile_pattern_matrix_with_guard_resolver(pattern_matrix, &mut resolver)
}

pub fn compile_pattern_matrix_with_guard_resolver<F>(
    pattern_matrix: PatternMatrix,
    guard_call_resolver: &mut F,
) -> Result<crate::matcher::Matcher, PatternMatrixCompileError>
where
    F: FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<Option<crate::matcher::GuardExpr>, PatternMatrixCompileError>,
{
    use std::collections::HashMap;

    validate_source_order(&pattern_matrix)?;
    #[cfg(test)]
    COMPILE_COUNT.with(|count| count.set(count.get() + 1));

    let input_vars = pattern_matrix.subjects.clone();
    let pinned_names = collect_pinned_names(&pattern_matrix);
    let inputs: Vec<crate::matcher::MatcherInput> = input_vars
        .iter()
        .copied()
        .map(|v| crate::matcher::MatcherInput {
            var: Some(v),
            span: crate::diag::Span::DUMMY,
        })
        .collect();
    let input_by_var: HashMap<Var, crate::matcher::InputId> = input_vars
        .into_iter()
        .enumerate()
        .map(|(i, v)| (v, crate::matcher::InputId(i as u32)))
        .collect();
    let pinned: Vec<crate::matcher::PinnedInput> = pinned_names
        .iter()
        .map(|name| crate::matcher::PinnedInput {
            name: name.clone(),
            var: None,
            span: crate::diag::Span::DUMMY,
        })
        .collect();
    let pinned_by_name: HashMap<String, crate::matcher::PinnedId> = pinned_names
        .into_iter()
        .enumerate()
        .map(|(i, name)| (name, crate::matcher::PinnedId(i as u32)))
        .collect();

    let mut builder = MatcherBuilder {
        input_by_var,
        pinned_by_name,
        nodes: Vec::new(),
        prepared_keys: Vec::new(),
        guard_call_resolver,
    };
    let root = builder.compile_inner(CompilePatternMatrix {
        subjects: pattern_matrix
            .subjects
            .into_iter()
            .map(SubjectRef::Var)
            .collect(),
        rows: pattern_matrix.rows,
    })?;
    Ok(crate::matcher::Matcher {
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
    pub(crate) static COMPILE_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub fn reset_compile_count() {
    COMPILE_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub fn compile_count() -> usize {
    COMPILE_COUNT.with(std::cell::Cell::get)
}
