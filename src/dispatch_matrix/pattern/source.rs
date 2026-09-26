use std::collections::BTreeSet;

use crate::ast::{Expr, Pattern, Spanned};
use crate::dispatch_matrix::{DispatchNode, GraphNodeId};
use crate::source::Span;

use super::{PatternDispatchPlan, PatternPinnedInput, PatternSubjectRef, PinnedKind};

/// Opaque handle into the caller's body table. Source-pattern dispatch never
/// lowers bodies; it routes graph outcomes to caller-owned body lowering by id.
pub(crate) type PatternBodyId = u32;

#[derive(Debug, Clone)]
pub(crate) struct PatternRow<TypeHandle> {
    /// Column patterns. `patterns.len()` must equal `SourcePatternRows::input_count`.
    pub(crate) patterns: Vec<Spanned<Pattern>>,
    /// `@spec` annotation tests evaluated at leaf-resolution time, before the guard.
    pub(crate) preconditions: Vec<(PatternSubjectRef, TypeHandle)>,
    pub(crate) guard: Option<Spanned<Expr>>,
    pub(crate) body_id: PatternBodyId,
}

#[derive(Debug, Clone)]
pub(crate) struct SourcePatternRows<TypeHandle> {
    pub(crate) input_count: usize,
    pub(crate) rows: Vec<PatternRow<TypeHandle>>,
    /// The bindings that existed before these patterns began. A pin resolves
    /// against this snapshot and nothing else.
    pub(crate) prematch: Prematch,
}

impl<TypeHandle> SourcePatternRows<TypeHandle> {
    /// Rows matched inside a live scope: `case`, `with`, `receive`, `cond`, and
    /// the rows built to ask a question about patterns. The bindings that came
    /// before are held by that scope rather than by any input, so each pin is
    /// carried to the lowerer, which resolves it by name.
    pub(crate) fn lexical(input_count: usize, rows: Vec<PatternRow<TypeHandle>>) -> Self {
        Self {
            input_count,
            rows,
            prematch: Prematch::Lexical,
        }
    }

    /// Rows matched on entry to a function, where the bindings that came before
    /// arrive as `inputs`: a lambda's captures, each named and paired with the
    /// input that delivers it. A `def` closes over nothing and passes an empty
    /// list. Those inputs are the whole of the outside here, so a name they do
    /// not carry was never bound, and the pin reaching for it is refused.
    pub(crate) fn entry(input_count: usize, rows: Vec<PatternRow<TypeHandle>>, inputs: Vec<(String, u32)>) -> Self {
        Self {
            input_count,
            rows,
            prematch: Prematch::Inputs(inputs),
        }
    }
}

/// The bindings that existed before a pattern began, in the form the rows' site
/// can offer them.
#[derive(Debug, Clone)]
pub(crate) enum Prematch {
    /// An enclosing scope holds them and resolves each pin by name.
    Lexical,
    /// These inputs deliver them, and they are all there is.
    Inputs(Vec<(String, u32)>),
}

impl Prematch {
    pub(crate) fn input_for(&self, name: &str) -> Option<u32> {
        match self {
            Prematch::Lexical => None,
            Prematch::Inputs(inputs) => inputs
                .iter()
                .find_map(|(bound, input)| (bound == name).then_some(*input)),
        }
    }

    /// The pins this snapshot cannot account for. `Lexical` accounts for all of
    /// them by deferring to the enclosing scope, so only an entry's inputs can
    /// come up short.
    pub(crate) fn undefined_pins(&self, pinned: &[PatternPinnedInput]) -> Vec<PatternPinnedInput> {
        match self {
            Prematch::Lexical => Vec::new(),
            Prematch::Inputs(_) => pinned.iter().filter(|pin| pin.input.is_none()).cloned().collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SourcePatternError {
    UnresolvedStruct(crate::ast::ModuleTarget),
    UnsupportedGuardExpr,
    UnsupportedMapKey,
    UnknownSubject(PatternSubjectRef),
    UnknownPinned(String),
    UnknownGuardVar(String),
    /// Names these patterns reached for that were never bound. Every one is
    /// reported, the way Elixir reports every undefined variable in a head.
    UndefinedPins(Vec<PatternPinnedInput>),
    GuardCallCycle(String, usize),
    DispatchMatrix(String),
    RowPatternArity {
        expected: usize,
        actual: usize,
        body_id: PatternBodyId,
    },
    NonMonotonicBodyId {
        previous: PatternBodyId,
        current: PatternBodyId,
    },
}

/// The names these rows reach for but do not bind: a `^name` pattern, or a
/// guard variable no pattern in the same row binds. Each is resolved against
/// the rows' prematch here, where the whole row set is in view.
pub(crate) fn collect_pinned_names<TypeHandle>(patterns: &SourcePatternRows<TypeHandle>) -> Vec<PatternPinnedInput> {
    let mut out = Vec::new();
    for row in &patterns.rows {
        let mut bound = BTreeSet::new();
        for pattern in &row.patterns {
            collect_pinned_names_in_pattern(pattern, &mut out);
            collect_bound_names_in_pattern(&pattern.node, &mut bound);
        }
        if let Some(guard) = &row.guard {
            collect_guard_capture_names(guard, &bound, &mut out);
        }
    }
    for pin in &mut out {
        pin.input = patterns.prematch.input_for(&pin.name);
    }
    out
}

fn record_pinned_name(name: &str, span: Span, kind: PinnedKind, out: &mut Vec<PatternPinnedInput>) {
    if !out.iter().any(|pin| pin.name == name) {
        out.push(PatternPinnedInput {
            name: name.to_string(),
            input: None,
            span,
            kind,
        });
    }
}

pub(crate) fn collect_bound_names_in_pattern(pattern: &Pattern, out: &mut BTreeSet<String>) {
    match pattern {
        Pattern::Var(name) | Pattern::As(name, _) => {
            out.insert(name.clone());
            if let Pattern::As(_, inner) = pattern {
                collect_bound_names_in_pattern(&inner.node, out);
            }
        }
        Pattern::Tuple(elems) | Pattern::List(elems, _) => {
            for elem in elems {
                collect_bound_names_in_pattern(&elem.node, out);
            }
            if let Pattern::List(_, Some(tail)) = pattern {
                collect_bound_names_in_pattern(&tail.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (key, val) in entries {
                collect_bound_names_in_pattern(&key.node, out);
                collect_bound_names_in_pattern(&val.node, out);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, val) in fields {
                collect_bound_names_in_pattern(&val.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_bound_names_in_pattern(&field.value.node, out);
            }
        }
        Pattern::Wildcard
        | Pattern::Pinned(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
    }
}

pub(crate) fn collect_guard_capture_names(
    expr: &Spanned<Expr>,
    bound: &BTreeSet<String>,
    out: &mut Vec<PatternPinnedInput>,
) {
    match &expr.node {
        Expr::Var(name) if !bound.contains(name) => record_pinned_name(name, expr.span, PinnedKind::Variable, out),
        Expr::BinOp(_, a, b) => {
            collect_guard_capture_names(a, bound, out);
            collect_guard_capture_names(b, bound, out);
        }
        Expr::UnOp(_, a) | Expr::Ascribe(a, _) => collect_guard_capture_names(a, bound, out),
        Expr::Call(target, args) => {
            // A target the callee authority recognises names a callable, not a
            // captured value; anything else is an expression to walk.
            if crate::ast::Callee::for_call(&target.node, args.len()).is_none() {
                collect_guard_capture_names(target, bound, out);
            }
            for arg in args {
                collect_guard_capture_names(arg, bound, out);
            }
        }
        _ => {}
    }
}

fn collect_pinned_names_in_pattern(pattern: &Spanned<Pattern>, out: &mut Vec<PatternPinnedInput>) {
    match &pattern.node {
        Pattern::Pinned(name) => record_pinned_name(name, pattern.span, PinnedKind::Pin, out),
        Pattern::Tuple(elems) | Pattern::List(elems, _) => {
            for elem in elems {
                collect_pinned_names_in_pattern(elem, out);
            }
            if let Pattern::List(_, Some(tail)) = &pattern.node {
                collect_pinned_names_in_pattern(tail, out);
            }
        }
        Pattern::Map(entries) => {
            for (key, val) in entries {
                collect_pinned_names_in_pattern(key, out);
                collect_pinned_names_in_pattern(val, out);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, val) in fields {
                collect_pinned_names_in_pattern(val, out);
            }
        }
        Pattern::As(_, inner) => collect_pinned_names_in_pattern(inner, out),
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pinned_names_in_pattern(&field.value, out);
            }
        }
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
    }
}

pub(crate) fn direct_bitfield_bindings(pattern: &Pattern) -> Vec<String> {
    match pattern {
        Pattern::Var(name) => vec![name.clone()],
        Pattern::As(name, inner) => {
            let mut out = vec![name.clone()];
            out.extend(direct_bitfield_bindings(&inner.node));
            out
        }
        _ => Vec::new(),
    }
}

/// A clause whose row the compiled plan proves no path reaches, paired with
/// the earliest earlier row whose coverage already matches everything that
/// row could see.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct RedundantRow {
    pub(crate) body_id: PatternBodyId,
    pub(crate) always_matches: PatternBodyId,
}

/// Body ids `plan` proves no path reaches, each paired with the earlier row
/// that already matches everything it could see. `plan` is the caller's own
/// compiled dispatch plan for `patterns` — real guards, real annotation
/// preconditions, nothing normalized away — so a guarded row is never
/// mistaken for redundant, and an annotation that actually partitions the
/// input is never mistaken for overlap.
pub(crate) fn find_redundant_rows_with_resolver<TypeHandle: Clone + PartialEq + Eq>(
    patterns: &SourcePatternRows<TypeHandle>,
    plan: &PatternDispatchPlan<TypeHandle>,
    resolver: &mut impl super::PatternResolver<TypeHandle>,
) -> Vec<RedundantRow> {
    let row_bodies: BTreeSet<PatternBodyId> = patterns.rows.iter().map(|r| r.body_id).collect();
    let mut reached = BTreeSet::new();
    collect_reachable_bodies_from_graph(plan, plan.graph.root, &mut reached);
    row_bodies
        .difference(&reached)
        .map(|&body_id| RedundantRow {
            body_id,
            always_matches: earliest_row_that_already_matches(patterns, body_id, resolver),
        })
        .collect()
}

/// The earliest row before `body_id`'s row whose coverage, added to whatever
/// precedes it, already matches everything that row could reach. Coverage
/// only grows as earlier rows are added — each one can only intercept
/// values, never release them back — so the first prefix that already
/// renders `body_id` unreachable names the clause that completes its
/// coverage.
fn earliest_row_that_already_matches<TypeHandle: Clone + PartialEq + Eq>(
    patterns: &SourcePatternRows<TypeHandle>,
    body_id: PatternBodyId,
    resolver: &mut impl super::PatternResolver<TypeHandle>,
) -> PatternBodyId {
    let index = patterns
        .rows
        .iter()
        .position(|row| row.body_id == body_id)
        .expect("a reported body id names a row in these patterns");
    for prefix_end in 0..index {
        let mut candidate_rows = patterns.rows[..=prefix_end].to_vec();
        candidate_rows.push(patterns.rows[index].clone());
        let candidate = SourcePatternRows {
            input_count: patterns.input_count,
            rows: candidate_rows,
            prematch: patterns.prematch.clone(),
        };
        let plan = super::pattern_dispatch_from_source_with_resolver(candidate, resolver)
            .expect("a prefix of already-compiled rows must still compile");
        let mut reached = BTreeSet::new();
        collect_reachable_bodies_from_graph(&plan, plan.graph.root, &mut reached);
        if !reached.contains(&body_id) {
            return patterns.rows[prefix_end].body_id;
        }
    }
    unreachable!("row {body_id} was proved unreachable against the full row set, so some earlier prefix must too")
}

fn collect_reachable_bodies_from_graph<TypeHandle>(
    plan: &PatternDispatchPlan<TypeHandle>,
    node: GraphNodeId,
    out: &mut BTreeSet<PatternBodyId>,
) {
    let Some(node) = plan.graph.node(node) else {
        return;
    };
    match node {
        DispatchNode::Fail => {}
        DispatchNode::Outcome { outcome, .. } => {
            if let Some(outcome) = plan.outcome(*outcome) {
                out.insert(outcome.body_id);
            }
        }
        DispatchNode::Test { on_match, on_miss, .. } => {
            collect_reachable_bodies_from_graph(plan, on_match.target, out);
            collect_reachable_bodies_from_graph(plan, on_miss.target, out);
        }
    }
}

#[cfg(test)]
#[path = "source_test.rs"]
mod source_test;
