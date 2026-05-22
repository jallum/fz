#![allow(dead_code)]
//! Pattern matrix data types and Matcher compiler.
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
use crate::matcher::{SwitchKey, SwitchKind};

/// Opaque handle into the caller's body table. The matrix never lowers
/// bodies; it routes Leaves to the caller's body-lowering callback by id.
///
/// Matrix rows must be supplied in source order with strictly increasing
/// `BodyId`s. Specialization preserves row priority by sorting merged rows on
/// this id after it combines constructor-specific and default rows.
pub type BodyId = u32;

#[derive(Debug, Clone)]
pub struct Row {
    /// Column patterns. `patterns.len()` must equal `Matrix::subjects.len()`
    /// at every step of compilation. Specialization may grow or shrink this
    /// vector (e.g. tuple-arity-3 specialization replaces one column with three).
    pub patterns: Vec<Spanned<Pattern>>,
    /// `@spec` annotation tests evaluated at leaf-resolution time, before
    /// the guard. Each (var, descr) emits `TypeTest(var, descr)`; on fail,
    /// the matrix falls through to the next row.
    pub preconditions: Vec<(Var, crate::types::Ty)>,
    /// Bindings already proven while specialization removed or expanded
    /// columns. Remaining column bindings are collected when the leaf forms.
    pub bindings: Vec<(String, SubjectRef)>,
    pub guard: Option<Spanned<Expr>>,
    pub body_id: BodyId,
}

#[derive(Debug, Clone)]
pub struct Matrix {
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
struct CompileMatrix {
    subjects: Vec<SubjectRef>,
    rows: Vec<Row>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubjectDomain {
    Any,
    List,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatcherCompileError {
    UnsupportedGuardExpr,
    UnsupportedMapKey,
    UnsupportedPerRow,
    UnknownSubject(Var),
    UnknownPinned(String),
    UnknownGuardVar(String),
    GuardCallCycle(String, usize),
    NonMonotonicBodyId { previous: BodyId, current: BodyId },
}

/// Compile the supported pattern matrix subset into the AST-free `Matcher`
/// representation.
pub fn compile_matcher_subset(m: Matrix) -> Result<crate::matcher::Matcher, MatcherCompileError> {
    let mut resolver =
        |_name: &str,
         _arity: usize,
         _args: Vec<crate::matcher::GuardExpr>|
         -> Result<Option<crate::matcher::GuardExpr>, MatcherCompileError> { Ok(None) };
    compile_matcher_subset_with_guard_resolver(m, &mut resolver)
}

pub fn compile_matcher_subset_with_guard_resolver<F>(
    m: Matrix,
    guard_call_resolver: &mut F,
) -> Result<crate::matcher::Matcher, MatcherCompileError>
where
    F: FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<Option<crate::matcher::GuardExpr>, MatcherCompileError>,
{
    use std::collections::HashMap;

    validate_source_order(&m)?;

    let input_vars = m.subjects.clone();
    let pinned_names = collect_pinned_names(&m);
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
    let root = builder.compile_inner(CompileMatrix {
        subjects: m.subjects.into_iter().map(SubjectRef::Var).collect(),
        rows: m.rows,
    })?;
    Ok(crate::matcher::Matcher {
        inputs,
        pinned,
        prepared_keys: builder.prepared_keys,
        nodes: builder.nodes,
        root,
    })
}

fn validate_source_order(m: &Matrix) -> Result<(), MatcherCompileError> {
    for pair in m.rows.windows(2) {
        let previous = pair[0].body_id;
        let current = pair[1].body_id;
        if previous >= current {
            return Err(MatcherCompileError::NonMonotonicBodyId { previous, current });
        }
    }
    Ok(())
}

struct MatcherBuilder<'a, F>
where
    F: FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<Option<crate::matcher::GuardExpr>, MatcherCompileError>,
{
    input_by_var: std::collections::HashMap<Var, crate::matcher::InputId>,
    pinned_by_name: std::collections::HashMap<String, crate::matcher::PinnedId>,
    nodes: Vec<crate::matcher::MatcherNode>,
    prepared_keys: Vec<crate::matcher::MatcherConst>,
    guard_call_resolver: &'a mut F,
}

impl<F> MatcherBuilder<'_, F>
where
    F: FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<Option<crate::matcher::GuardExpr>, MatcherCompileError>,
{
    fn push(&mut self, node: crate::matcher::MatcherNode) -> crate::matcher::NodeId {
        push_matcher_node(&mut self.nodes, node)
    }

    fn compile_inner(
        &mut self,
        m: CompileMatrix,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        if m.rows.is_empty() {
            return Ok(self.push(crate::matcher::MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            }));
        }
        if m.subjects.is_empty() {
            return self.leaf_or_rejecting_chain(m.rows, vec![]);
        }

        if m.rows
            .first()
            .map(|r| r.patterns.iter().all(|p| is_wildlike(&p.node)))
            .unwrap_or(false)
            && m.rows
                .first()
                .is_some_and(|r| r.guard.is_none() && r.preconditions.is_empty())
        {
            return self.leaf_or_rejecting_chain(m.rows, m.subjects);
        }

        let col = match pick_specialization_column(&m) {
            Some(c) => c,
            None => return self.leaf_or_rejecting_chain(m.rows, m.subjects),
        };

        if let Some(row_idx) = find_unspecializable_row(&m, col) {
            let mut rows = m.rows;
            let row = rows.remove(row_idx);
            let subjects = m.subjects.clone();
            let rest = CompileMatrix {
                subjects: m.subjects,
                rows,
            };
            let on_fail = self.compile_inner(rest)?;
            return self.per_row_to_matcher_node(&subjects, &row, on_fail);
        }

        self.specialize_and_compile(m, col)
    }

    fn leaf_or_rejecting_chain(
        &mut self,
        mut rows: Vec<Row>,
        subjects: Vec<SubjectRef>,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        let row = rows.remove(0);
        let reject = if row_can_reject(&row) {
            Some(self.compile_inner(CompileMatrix {
                subjects: subjects.clone(),
                rows,
            })?)
        } else {
            None
        };
        self.leaf_from_row(row, &subjects, reject)
    }

    fn leaf_from_row(
        &mut self,
        row: Row,
        subjects: &[SubjectRef],
        on_reject: Option<crate::matcher::NodeId>,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        let mut bindings = row.bindings.clone();
        bindings.extend(collect_var_bindings(&row.patterns, subjects));
        let matcher_bindings = bindings
            .iter()
            .map(|(name, subject)| {
                Ok(crate::matcher::MatcherBinding {
                    name: name.clone(),
                    source: subject_to_matcher_ref(subject, &self.input_by_var)?,
                    span: crate::diag::Span::DUMMY,
                })
            })
            .collect::<Result<Vec<_>, MatcherCompileError>>()?;
        let leaf = self.push(crate::matcher::MatcherNode::Leaf(
            crate::matcher::MatcherLeaf {
                body_id: row.body_id,
                bindings: matcher_bindings.clone(),
                span: crate::diag::Span::DUMMY,
            },
        ));
        let guarded = guard_to_matcher_node(
            row.guard.as_ref(),
            &matcher_bindings,
            &self.pinned_by_name,
            leaf,
            on_reject,
            &mut self.nodes,
            &mut self.prepared_keys,
            self.guard_call_resolver,
        )?;
        preconditions_to_matcher_nodes(
            &row.preconditions,
            &self.input_by_var,
            guarded,
            on_reject,
            &mut self.nodes,
        )
    }

    fn per_row_to_matcher_node(
        &mut self,
        subjects: &[SubjectRef],
        row: &Row,
        on_fail: crate::matcher::NodeId,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        let mut tests = Vec::new();
        let mut bindings = Vec::new();
        for (pattern, subject) in row.patterns.iter().zip(subjects.iter()) {
            let subject = subject_to_matcher_ref(subject, &self.input_by_var)?;
            append_pattern_ops(
                &pattern.node,
                subject,
                &self.pinned_by_name,
                &mut self.prepared_keys,
                &mut tests,
                &mut bindings,
            )?;
        }
        let leaf = self.push(crate::matcher::MatcherNode::Leaf(
            crate::matcher::MatcherLeaf {
                body_id: row.body_id,
                bindings: bindings.clone(),
                span: crate::diag::Span::DUMMY,
            },
        ));
        let guarded = guard_to_matcher_node(
            row.guard.as_ref(),
            &bindings,
            &self.pinned_by_name,
            leaf,
            Some(on_fail),
            &mut self.nodes,
            &mut self.prepared_keys,
            self.guard_call_resolver,
        )?;
        let mut current = preconditions_to_matcher_nodes(
            &row.preconditions,
            &self.input_by_var,
            guarded,
            Some(on_fail),
            &mut self.nodes,
        )?;
        for test in tests.into_iter().rev() {
            current = self.push(crate::matcher::MatcherNode::Test {
                test,
                on_true: current,
                on_false: on_fail,
                span: crate::diag::Span::DUMMY,
            });
        }
        Ok(current)
    }

    fn specialize_and_compile(
        &mut self,
        m: CompileMatrix,
        col: usize,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        let subject = m.subjects[col].clone();
        let kind = pick_kind_for_column(&m, col);
        match kind {
            SwitchKind::TupleArity => self.specialize_tuple_arity(m, col, subject),
            SwitchKind::Atom => self.specialize_atom(m, col, subject),
            SwitchKind::Int => self.specialize_int(m, col, subject),
            SwitchKind::Float => self.specialize_float(m, col, subject),
            SwitchKind::Bool => self.specialize_bool(m, col, subject),
            SwitchKind::Nil => self.specialize_nil(m, col, subject),
            SwitchKind::Binary => self.specialize_binary(m, col, subject),
            SwitchKind::ListCons => self.specialize_listcons(m, col, subject),
        }
    }

    fn switch_node(
        &mut self,
        subject: SubjectRef,
        kind: SwitchKind,
        cases: Vec<(SwitchKey, crate::matcher::NodeId)>,
        default: crate::matcher::NodeId,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        let subject = subject_to_matcher_ref(&subject, &self.input_by_var)?;
        Ok(self.push(crate::matcher::MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            span: crate::diag::Span::DUMMY,
        }))
    }

    fn specialize_tuple_arity(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        use std::collections::BTreeMap;
        let mut by_arity: BTreeMap<u32, Vec<Row>> = BTreeMap::new();
        let mut default_rows: Vec<Row> = Vec::new();
        let mut other_rows: Vec<Row> = Vec::new();

        for row in m.rows {
            let mut row = row;
            let (_, inner_pat) = peel_to_inner_with_bind(&row.patterns[col]);
            row.patterns[col] = inner_pat;

            let p = &row.patterns[col].node;
            match p {
                Pattern::Tuple(fields) => {
                    let arity = fields.len() as u32;
                    let mut new_row = row.clone();
                    record_removed_column_bindings(&mut new_row, col, &subject);
                    new_row.patterns.splice(col..=col, fields.iter().cloned());
                    by_arity.entry(arity).or_default().push(new_row);
                }
                Pattern::Wildcard | Pattern::Var(_) => default_rows.push(row),
                _ => other_rows.push(row),
            }
        }

        let mut cases: Vec<(SwitchKey, crate::matcher::NodeId)> = Vec::new();
        for (arity, rows) in by_arity {
            let mut all_rows = rows;
            for d in &default_rows {
                let mut dr = d.clone();
                record_removed_column_bindings(&mut dr, col, &subject);
                let span = dr.patterns[col].span;
                let wilds: Vec<Spanned<Pattern>> = (0..arity)
                    .map(|_| Spanned::new(Pattern::Wildcard, span))
                    .collect();
                dr.patterns.splice(col..=col, wilds);
                all_rows.push(dr);
            }
            all_rows.sort_by_key(|r| r.body_id);
            let mut new_subjects = m.subjects.clone();
            let projections: Vec<SubjectRef> = (0..arity)
                .map(|i| SubjectRef::TupleField {
                    tuple: Box::new(subject.clone()),
                    index: i,
                })
                .collect();
            new_subjects.splice(col..=col, projections);

            let sub = self.compile_inner(CompileMatrix {
                subjects: new_subjects,
                rows: all_rows,
            })?;
            cases.push((SwitchKey::Arity(arity), sub));
        }

        let default = if default_rows.is_empty() && other_rows.is_empty() {
            self.push(crate::matcher::MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            })
        } else if other_rows.is_empty() {
            let mut new_subjects = m.subjects.clone();
            new_subjects.remove(col);
            let new_rows: Vec<Row> = default_rows
                .into_iter()
                .map(|mut r| {
                    record_removed_column_bindings(&mut r, col, &subject);
                    r.patterns.remove(col);
                    r
                })
                .collect();
            self.compile_inner(CompileMatrix {
                subjects: new_subjects,
                rows: new_rows,
            })?
        } else {
            let mut rows: Vec<Row> = other_rows.into_iter().chain(default_rows).collect();
            rows.sort_by_key(|r| r.body_id);
            self.compile_inner(CompileMatrix {
                subjects: m.subjects.clone(),
                rows,
            })?
        };

        self.switch_node(subject, SwitchKind::TupleArity, cases, default)
    }

    fn specialize_atom(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        self.specialize_literal(m, col, subject, SwitchKind::Atom, |p| match p {
            Pattern::Atom(s) => Some(SwitchKey::AtomName(s.clone())),
            _ => None,
        })
    }

    fn specialize_int(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        self.specialize_literal(m, col, subject, SwitchKind::Int, |p| match p {
            Pattern::Int(n) => Some(SwitchKey::Int(*n)),
            _ => None,
        })
    }

    fn specialize_float(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        self.specialize_literal(m, col, subject, SwitchKind::Float, |p| match p {
            Pattern::Float(n) => Some(SwitchKey::FloatBits(n.to_bits())),
            _ => None,
        })
    }

    fn specialize_bool(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        self.specialize_literal(m, col, subject, SwitchKind::Bool, |p| match p {
            Pattern::Bool(b) => Some(SwitchKey::Bool(*b)),
            _ => None,
        })
    }

    fn specialize_nil(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        self.specialize_literal(m, col, subject, SwitchKind::Nil, |p| match p {
            Pattern::Nil => Some(SwitchKey::Nil),
            _ => None,
        })
    }

    fn specialize_binary(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        self.specialize_literal(m, col, subject, SwitchKind::Binary, |p| match p {
            Pattern::Binary(bytes) => Some(SwitchKey::Utf8Binary(bytes.clone())),
            _ => None,
        })
    }

    fn specialize_listcons(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError> {
        use std::collections::BTreeMap;
        let mut by_key: BTreeMap<SwitchKey, Vec<Row>> = BTreeMap::new();
        let mut default_rows: Vec<Row> = Vec::new();

        for row in m.rows {
            let mut row = row;
            let (_, inner_pat) = peel_to_inner_with_bind(&row.patterns[col]);
            row.patterns[col] = inner_pat;
            let p = &row.patterns[col].node;
            match p {
                Pattern::Nil => {
                    let mut r = row.clone();
                    record_removed_column_bindings(&mut r, col, &subject);
                    r.patterns.remove(col);
                    by_key.entry(SwitchKey::Nil).or_default().push(r);
                }
                Pattern::List(elems, tail) => {
                    if elems.is_empty() && tail.is_none() {
                        let mut r = row.clone();
                        record_removed_column_bindings(&mut r, col, &subject);
                        r.patterns.remove(col);
                        by_key.entry(SwitchKey::EmptyList).or_default().push(r);
                    } else if elems.is_empty() {
                        continue;
                    } else {
                        let mut r = row.clone();
                        record_removed_column_bindings(&mut r, col, &subject);
                        let head = elems[0].clone();
                        let tail_pattern = if elems.len() == 1 {
                            tail.as_deref().cloned().unwrap_or_else(|| {
                                Spanned::new(Pattern::List(vec![], None), head.span)
                            })
                        } else {
                            Spanned::new(
                                Pattern::List(
                                    elems[1..].to_vec(),
                                    tail.as_ref().map(|p| Box::new((**p).clone())),
                                ),
                                head.span,
                            )
                        };
                        r.patterns.splice(col..=col, [head, tail_pattern]);
                        by_key.entry(SwitchKey::Cons).or_default().push(r);
                    }
                }
                Pattern::Wildcard | Pattern::Var(_) => default_rows.push(row),
                _ => {}
            }
        }

        let mut cases: Vec<(SwitchKey, crate::matcher::NodeId)> = Vec::new();
        for (key, mut rows) in by_key {
            for d in &default_rows {
                let mut dr = d.clone();
                record_removed_column_bindings(&mut dr, col, &subject);
                if matches!(key, SwitchKey::Cons) {
                    let span = dr.patterns[col].span;
                    dr.patterns.splice(
                        col..=col,
                        [
                            Spanned::new(Pattern::Wildcard, span),
                            Spanned::new(Pattern::Wildcard, span),
                        ],
                    );
                } else {
                    dr.patterns.remove(col);
                }
                rows.push(dr);
            }
            rows.sort_by_key(|r| r.body_id);
            let column_already_removed = matches!(key, SwitchKey::Nil | SwitchKey::EmptyList);
            let new_subjects = if column_already_removed {
                let mut s = m.subjects.clone();
                s.remove(col);
                s
            } else {
                let mut s = m.subjects.clone();
                s.splice(
                    col..=col,
                    [
                        SubjectRef::ListHead(Box::new(subject.clone())),
                        SubjectRef::ListTail(Box::new(subject.clone())),
                    ],
                );
                s
            };
            let sub = self.compile_inner(CompileMatrix {
                subjects: new_subjects,
                rows,
            })?;
            cases.push((key, sub));
        }

        let mut new_subjects = m.subjects.clone();
        new_subjects.remove(col);
        let new_rows: Vec<Row> = default_rows
            .into_iter()
            .map(|mut r| {
                record_removed_column_bindings(&mut r, col, &subject);
                r.patterns.remove(col);
                r
            })
            .collect();
        let default = self.compile_inner(CompileMatrix {
            subjects: new_subjects,
            rows: new_rows,
        })?;

        self.switch_node(subject, SwitchKind::ListCons, cases, default)
    }

    fn specialize_literal<G>(
        &mut self,
        m: CompileMatrix,
        col: usize,
        subject: SubjectRef,
        kind: SwitchKind,
        key_for: G,
    ) -> Result<crate::matcher::NodeId, MatcherCompileError>
    where
        G: Fn(&Pattern) -> Option<SwitchKey>,
    {
        use std::collections::BTreeMap;
        let mut by_key: BTreeMap<String, (SwitchKey, Vec<Row>)> = BTreeMap::new();
        let mut default_rows: Vec<Row> = Vec::new();
        let mut other_rows: Vec<Row> = Vec::new();

        for row in m.rows {
            let mut row = row;
            let (_, inner_pat) = peel_to_inner_with_bind(&row.patterns[col]);
            row.patterns[col] = inner_pat;
            let p = &row.patterns[col].node;
            if let Some(k) = key_for(p) {
                let kstr = format!("{:?}", k);
                let mut nr = row.clone();
                record_removed_column_bindings(&mut nr, col, &subject);
                nr.patterns.remove(col);
                by_key
                    .entry(kstr)
                    .or_insert_with(|| (k, Vec::new()))
                    .1
                    .push(nr);
            } else if matches!(p, Pattern::Wildcard | Pattern::Var(_)) {
                default_rows.push(row);
            } else {
                other_rows.push(row);
            }
        }

        let mut cases: Vec<(SwitchKey, crate::matcher::NodeId)> = Vec::new();
        for (_, (key, mut rows)) in by_key {
            for d in &default_rows {
                let mut dr = d.clone();
                record_removed_column_bindings(&mut dr, col, &subject);
                dr.patterns.remove(col);
                rows.push(dr);
            }
            rows.sort_by_key(|r| r.body_id);
            let mut new_subjects = m.subjects.clone();
            new_subjects.remove(col);
            let sub = self.compile_inner(CompileMatrix {
                subjects: new_subjects,
                rows,
            })?;
            cases.push((key, sub));
        }

        let default = if other_rows.is_empty() {
            let mut new_subjects = m.subjects.clone();
            new_subjects.remove(col);
            let new_rows: Vec<Row> = default_rows
                .into_iter()
                .map(|mut r| {
                    record_removed_column_bindings(&mut r, col, &subject);
                    r.patterns.remove(col);
                    r
                })
                .collect();
            self.compile_inner(CompileMatrix {
                subjects: new_subjects,
                rows: new_rows,
            })?
        } else {
            let mut rows: Vec<Row> = other_rows.into_iter().chain(default_rows).collect();
            rows.sort_by_key(|r| r.body_id);
            self.compile_inner(CompileMatrix {
                subjects: m.subjects.clone(),
                rows,
            })?
        };

        self.switch_node(subject, kind, cases, default)
    }
}

pub fn collect_matcher_pattern_bindings(
    patterns: &[Spanned<Pattern>],
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
) -> Result<Vec<crate::matcher::MatcherBinding>, MatcherCompileError> {
    let mut tests = Vec::new();
    let mut bindings = Vec::new();
    let mut prepared_keys = Vec::new();
    for (index, pattern) in patterns.iter().enumerate() {
        append_pattern_ops(
            &pattern.node,
            crate::matcher::SubjectRef::Input(crate::matcher::InputId(index as u32)),
            pinned_by_name,
            &mut prepared_keys,
            &mut tests,
            &mut bindings,
        )?;
    }
    Ok(bindings)
}

pub fn compile_guard_expr_subset<F>(
    expr: &Expr,
    bindings: &[crate::matcher::MatcherBinding],
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    guard_call_resolver: &mut F,
) -> Result<crate::matcher::GuardExpr, MatcherCompileError>
where
    F: FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<Option<crate::matcher::GuardExpr>, MatcherCompileError>,
{
    let mut bound = std::collections::HashMap::new();
    for binding in bindings {
        bound.insert(binding.name.clone(), binding.source.clone());
    }
    guard_expr_to_matcher(expr, &bound, pinned_by_name, guard_call_resolver)
}

fn collect_pinned_names(m: &Matrix) -> Vec<String> {
    let mut out = Vec::new();
    for row in &m.rows {
        let mut bound = std::collections::BTreeSet::new();
        for pattern in &row.patterns {
            collect_pinned_names_in_pattern(&pattern.node, &mut out);
            collect_bound_names_in_pattern(&pattern.node, &mut bound);
        }
        if let Some(guard) = &row.guard {
            collect_guard_capture_names(&guard.node, &bound, &mut out);
        }
    }
    out
}

fn collect_bound_names_in_pattern(pattern: &Pattern, out: &mut std::collections::BTreeSet<String>) {
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
    expr: &Expr,
    bound: &std::collections::BTreeSet<String>,
    out: &mut Vec<String>,
) {
    use crate::ast::Expr;
    match expr {
        Expr::Var(name) if !bound.contains(name) && !out.contains(name) => out.push(name.clone()),
        Expr::BinOp(_, a, b) => {
            collect_guard_capture_names(&a.node, bound, out);
            collect_guard_capture_names(&b.node, bound, out);
        }
        Expr::UnOp(_, a) => collect_guard_capture_names(&a.node, bound, out),
        Expr::Call(target, args) => {
            if !matches!(&target.node, Expr::Var(_) | Expr::FnRef { .. }) {
                collect_guard_capture_names(&target.node, bound, out);
            }
            for arg in args {
                collect_guard_capture_names(&arg.node, bound, out);
            }
        }
        _ => {}
    }
}

fn collect_pinned_names_in_pattern(pattern: &Pattern, out: &mut Vec<String>) {
    match pattern {
        Pattern::Pinned(name) => {
            if !out.contains(name) {
                out.push(name.clone());
            }
        }
        Pattern::Tuple(elems) | Pattern::List(elems, _) => {
            for elem in elems {
                collect_pinned_names_in_pattern(&elem.node, out);
            }
            if let Pattern::List(_, Some(tail)) = pattern {
                collect_pinned_names_in_pattern(&tail.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (key, val) in entries {
                collect_pinned_names_in_pattern(&key.node, out);
                collect_pinned_names_in_pattern(&val.node, out);
            }
        }
        Pattern::As(_, inner) => collect_pinned_names_in_pattern(&inner.node, out),
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pinned_names_in_pattern(&field.value.node, out);
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

fn preconditions_to_matcher_nodes(
    preconditions: &[(Var, crate::types::Ty)],
    input_by_var: &std::collections::HashMap<Var, crate::matcher::InputId>,
    on_true: crate::matcher::NodeId,
    on_false: Option<crate::matcher::NodeId>,
    nodes: &mut Vec<crate::matcher::MatcherNode>,
) -> Result<crate::matcher::NodeId, MatcherCompileError> {
    if preconditions.is_empty() {
        return Ok(on_true);
    }
    let on_false = on_false.unwrap_or_else(|| {
        push_matcher_node(
            nodes,
            crate::matcher::MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            },
        )
    });
    let mut current = on_true;
    for (var, ty) in preconditions.iter().rev() {
        let input = input_by_var
            .get(var)
            .copied()
            .ok_or(MatcherCompileError::UnknownSubject(*var))?;
        current = push_matcher_node(
            nodes,
            crate::matcher::MatcherNode::Test {
                test: crate::matcher::MatcherTest::Type {
                    subject: crate::matcher::SubjectRef::Input(input),
                    ty: ty.clone(),
                },
                on_true: current,
                on_false,
                span: crate::diag::Span::DUMMY,
            },
        );
    }
    Ok(current)
}

fn guard_to_matcher_node(
    guard: Option<&Spanned<Expr>>,
    bindings: &[crate::matcher::MatcherBinding],
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    on_true: crate::matcher::NodeId,
    on_false: Option<crate::matcher::NodeId>,
    nodes: &mut Vec<crate::matcher::MatcherNode>,
    _prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<
        Option<crate::matcher::GuardExpr>,
        MatcherCompileError,
    >,
) -> Result<crate::matcher::NodeId, MatcherCompileError> {
    let Some(guard) = guard else {
        return Ok(on_true);
    };
    let on_false = on_false.unwrap_or_else(|| {
        push_matcher_node(
            nodes,
            crate::matcher::MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            },
        )
    });
    let mut bound = std::collections::HashMap::new();
    for binding in bindings {
        bound.insert(binding.name.clone(), binding.source.clone());
    }
    let expr = guard_expr_to_matcher(&guard.node, &bound, pinned_by_name, guard_call_resolver)?;
    Ok(push_matcher_node(
        nodes,
        crate::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            span: guard.span,
        },
    ))
}

fn guard_expr_to_matcher(
    expr: &Expr,
    bindings: &std::collections::HashMap<String, crate::matcher::SubjectRef>,
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    guard_call_resolver: &mut impl FnMut(
        &str,
        usize,
        Vec<crate::matcher::GuardExpr>,
    ) -> Result<
        Option<crate::matcher::GuardExpr>,
        MatcherCompileError,
    >,
) -> Result<crate::matcher::GuardExpr, MatcherCompileError> {
    use crate::ast::{BinOp, Expr, UnOp};
    Ok(match expr {
        Expr::Int(n) => crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Int(*n)),
        Expr::Float(n) => {
            crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::FloatBits(n.to_bits()))
        }
        Expr::Binary(bytes) => crate::matcher::GuardExpr::Const(
            crate::matcher::MatcherConst::Utf8Binary(bytes.clone()),
        ),
        Expr::Atom(name) => {
            crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::AtomName(name.clone()))
        }
        Expr::Bool(b) => crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Bool(*b)),
        Expr::Nil => crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Nil),
        Expr::Var(name) => {
            if let Some(subject) = bindings.get(name) {
                crate::matcher::GuardExpr::Subject(subject.clone())
            } else if let Some(pinned) = pinned_by_name.get(name) {
                crate::matcher::GuardExpr::Pinned(*pinned)
            } else {
                return Err(MatcherCompileError::UnknownGuardVar(name.clone()));
            }
        }
        Expr::UnOp(UnOp::Not, a) => crate::matcher::GuardExpr::Unary {
            op: crate::matcher::GuardUnaryOp::Not,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::UnOp(UnOp::Neg, a) => crate::matcher::GuardExpr::Unary {
            op: crate::matcher::GuardUnaryOp::Neg,
            expr: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::BinOp(op, a, b) => crate::matcher::GuardExpr::Binary {
            op: match op {
                BinOp::Add => crate::matcher::GuardBinOp::Add,
                BinOp::Sub => crate::matcher::GuardBinOp::Sub,
                BinOp::Mul => crate::matcher::GuardBinOp::Mul,
                BinOp::Div => crate::matcher::GuardBinOp::Div,
                BinOp::Rem => crate::matcher::GuardBinOp::Rem,
                BinOp::Eq => crate::matcher::GuardBinOp::Eq,
                BinOp::Neq => crate::matcher::GuardBinOp::Neq,
                BinOp::Lt => crate::matcher::GuardBinOp::Lt,
                BinOp::LtEq => crate::matcher::GuardBinOp::LtEq,
                BinOp::Gt => crate::matcher::GuardBinOp::Gt,
                BinOp::GtEq => crate::matcher::GuardBinOp::GtEq,
                BinOp::And => crate::matcher::GuardBinOp::And,
                BinOp::Or => crate::matcher::GuardBinOp::Or,
                BinOp::Pipe | BinOp::Cons => return Err(MatcherCompileError::UnsupportedGuardExpr),
            },
            lhs: Box::new(guard_expr_to_matcher(
                &a.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
            rhs: Box::new(guard_expr_to_matcher(
                &b.node,
                bindings,
                pinned_by_name,
                guard_call_resolver,
            )?),
        },
        Expr::Call(target, args) => {
            let callee = match &target.node {
                Expr::Var(name) => Some((name.as_str(), args.len())),
                Expr::FnRef { name, arity } if *arity == args.len() => {
                    Some((name.as_str(), *arity))
                }
                _ => None,
            };
            let Some((name, arity)) = callee else {
                return Err(MatcherCompileError::UnsupportedGuardExpr);
            };
            let args = args
                .iter()
                .map(|arg| {
                    guard_expr_to_matcher(&arg.node, bindings, pinned_by_name, guard_call_resolver)
                })
                .collect::<Result<Vec<_>, _>>()?;
            match guard_call_resolver(name, arity, args)? {
                Some(expr) => expr,
                None => return Err(MatcherCompileError::UnsupportedGuardExpr),
            }
        }
        _ => return Err(MatcherCompileError::UnsupportedGuardExpr),
    })
}

fn append_pattern_ops(
    pattern: &Pattern,
    subject: crate::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
    tests: &mut Vec<crate::matcher::MatcherTest>,
    bindings: &mut Vec<crate::matcher::MatcherBinding>,
) -> Result<(), MatcherCompileError> {
    match pattern {
        Pattern::Wildcard => {}
        Pattern::Var(name) => bindings.push(crate::matcher::MatcherBinding {
            name: name.clone(),
            source: subject,
            span: crate::diag::Span::DUMMY,
        }),
        Pattern::As(name, inner) => {
            bindings.push(crate::matcher::MatcherBinding {
                name: name.clone(),
                source: subject.clone(),
                span: crate::diag::Span::DUMMY,
            });
            append_pattern_ops(
                &inner.node,
                subject,
                pinned_by_name,
                prepared_keys,
                tests,
                bindings,
            )?;
        }
        Pattern::Pinned(name) => {
            let pinned = *pinned_by_name
                .get(name)
                .ok_or_else(|| MatcherCompileError::UnknownPinned(name.clone()))?;
            tests.push(crate::matcher::MatcherTest::EqPinned { subject, pinned });
        }
        Pattern::Int(n) => tests.push(crate::matcher::MatcherTest::EqConst {
            subject,
            value: crate::matcher::MatcherConst::Int(*n),
        }),
        Pattern::Float(n) => tests.push(crate::matcher::MatcherTest::EqConst {
            subject,
            value: crate::matcher::MatcherConst::FloatBits(n.to_bits()),
        }),
        Pattern::Binary(bytes) => tests.push(crate::matcher::MatcherTest::EqConst {
            subject,
            value: crate::matcher::MatcherConst::Utf8Binary(bytes.clone()),
        }),
        Pattern::Atom(name) => tests.push(crate::matcher::MatcherTest::EqConst {
            subject,
            value: crate::matcher::MatcherConst::AtomName(name.clone()),
        }),
        Pattern::Bool(b) => tests.push(crate::matcher::MatcherTest::EqConst {
            subject,
            value: crate::matcher::MatcherConst::Bool(*b),
        }),
        Pattern::Nil => tests.push(crate::matcher::MatcherTest::EqConst {
            subject,
            value: crate::matcher::MatcherConst::Nil,
        }),
        Pattern::Tuple(elems) => {
            tests.push(crate::matcher::MatcherTest::TupleArity {
                subject: subject.clone(),
                arity: elems.len() as u32,
            });
            for (index, elem) in elems.iter().enumerate() {
                append_pattern_ops(
                    &elem.node,
                    crate::matcher::SubjectRef::TupleField {
                        tuple: Box::new(subject.clone()),
                        index: index as u32,
                    },
                    pinned_by_name,
                    prepared_keys,
                    tests,
                    bindings,
                )?;
            }
        }
        Pattern::List(elems, tail) => append_list_pattern_ops(
            elems,
            tail.as_deref(),
            subject,
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?,
        Pattern::Map(entries) => append_map_pattern_ops(
            entries,
            subject,
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?,
        Pattern::Bitstring(fields) => append_bitstring_pattern_ops(
            fields,
            subject,
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?,
    }
    Ok(())
}

fn append_bitstring_pattern_ops(
    fields: &[crate::ast::BitField<Spanned<Pattern>>],
    subject: crate::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
    tests: &mut Vec<crate::matcher::MatcherTest>,
    bindings: &mut Vec<crate::matcher::MatcherBinding>,
) -> Result<(), MatcherCompileError> {
    let matcher_fields = fields
        .iter()
        .map(|field| crate::matcher::MatcherBitField {
            ty: matcher_bit_type(field.spec.ty),
            size: field.spec.size.as_ref().map(matcher_bit_size),
            endian: matcher_endian(field.spec.endian),
            signed: field.spec.signed,
            unit: field.spec.unit,
            direct_bindings: direct_bitfield_bindings(&field.value.node),
        })
        .collect();
    tests.push(crate::matcher::MatcherTest::Bitstring {
        subject: subject.clone(),
        fields: matcher_fields,
    });
    for (index, field) in fields.iter().enumerate() {
        append_pattern_ops(
            &field.value.node,
            crate::matcher::SubjectRef::BitstringField {
                bitstring: Box::new(subject.clone()),
                index: index as u32,
            },
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?;
    }
    Ok(())
}

fn direct_bitfield_bindings(pattern: &Pattern) -> Vec<String> {
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

fn matcher_bit_size(size: &crate::ast::BitSize) -> crate::matcher::MatcherBitSize {
    match size {
        crate::ast::BitSize::Literal(n) => crate::matcher::MatcherBitSize::Literal(*n),
        crate::ast::BitSize::Var(name) => crate::matcher::MatcherBitSize::BindingName(name.clone()),
    }
}

fn matcher_bit_type(ty: crate::ast::BitType) -> crate::matcher::MatcherBitType {
    match ty {
        crate::ast::BitType::Integer => crate::matcher::MatcherBitType::Integer,
        crate::ast::BitType::Float => crate::matcher::MatcherBitType::Float,
        crate::ast::BitType::Binary => crate::matcher::MatcherBitType::Binary,
        crate::ast::BitType::Bits => crate::matcher::MatcherBitType::Bits,
        crate::ast::BitType::Utf8 => crate::matcher::MatcherBitType::Utf8,
        crate::ast::BitType::Utf16 => crate::matcher::MatcherBitType::Utf16,
        crate::ast::BitType::Utf32 => crate::matcher::MatcherBitType::Utf32,
    }
}

fn matcher_endian(endian: crate::ast::Endian) -> crate::matcher::MatcherEndian {
    match endian {
        crate::ast::Endian::Big => crate::matcher::MatcherEndian::Big,
        crate::ast::Endian::Little => crate::matcher::MatcherEndian::Little,
        crate::ast::Endian::Native => crate::matcher::MatcherEndian::Native,
    }
}

fn append_map_pattern_ops(
    entries: &[(Spanned<Pattern>, Spanned<Pattern>)],
    subject: crate::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
    tests: &mut Vec<crate::matcher::MatcherTest>,
    bindings: &mut Vec<crate::matcher::MatcherBinding>,
) -> Result<(), MatcherCompileError> {
    tests.push(crate::matcher::MatcherTest::MapKind {
        subject: subject.clone(),
    });
    for (key_pat, val_pat) in entries {
        let key = scalar_map_key_const(&key_pat.node, prepared_keys)?;
        tests.push(crate::matcher::MatcherTest::MapHasKey {
            subject: subject.clone(),
            key: key.clone(),
        });
        append_pattern_ops(
            &val_pat.node,
            crate::matcher::SubjectRef::MapValue {
                map: Box::new(subject.clone()),
                key,
            },
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?;
    }
    Ok(())
}

fn scalar_map_key_const(
    pattern: &Pattern,
    prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
) -> Result<crate::matcher::MatcherConst, MatcherCompileError> {
    match pattern {
        Pattern::Int(n) => Ok(crate::matcher::MatcherConst::Int(*n)),
        Pattern::Float(n) => {
            let id = prepared_key_id(
                prepared_keys,
                crate::matcher::MatcherConst::FloatBits(n.to_bits()),
            );
            Ok(crate::matcher::MatcherConst::PreparedKey(id))
        }
        Pattern::Binary(bytes) => {
            let id = prepared_key_id(
                prepared_keys,
                crate::matcher::MatcherConst::Utf8Binary(bytes.clone()),
            );
            Ok(crate::matcher::MatcherConst::PreparedKey(id))
        }
        Pattern::Atom(name) => {
            let id = prepared_key_id(
                prepared_keys,
                crate::matcher::MatcherConst::AtomName(name.clone()),
            );
            Ok(crate::matcher::MatcherConst::PreparedKey(id))
        }
        Pattern::Bool(b) => Ok(crate::matcher::MatcherConst::Bool(*b)),
        Pattern::Nil => Ok(crate::matcher::MatcherConst::Nil),
        _ => Err(MatcherCompileError::UnsupportedMapKey),
    }
}

fn prepared_key_id(
    prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
    key: crate::matcher::MatcherConst,
) -> u32 {
    if let Some(index) = prepared_keys.iter().position(|existing| existing == &key) {
        return index as u32;
    }
    let id = prepared_keys.len() as u32;
    prepared_keys.push(key);
    id
}

fn append_list_pattern_ops(
    elems: &[Spanned<Pattern>],
    tail: Option<&Spanned<Pattern>>,
    subject: crate::matcher::SubjectRef,
    pinned_by_name: &std::collections::HashMap<String, crate::matcher::PinnedId>,
    prepared_keys: &mut Vec<crate::matcher::MatcherConst>,
    tests: &mut Vec<crate::matcher::MatcherTest>,
    bindings: &mut Vec<crate::matcher::MatcherBinding>,
) -> Result<(), MatcherCompileError> {
    if elems.is_empty() {
        match tail {
            Some(tail) => append_pattern_ops(
                &tail.node,
                subject,
                pinned_by_name,
                prepared_keys,
                tests,
                bindings,
            ),
            None => {
                tests.push(crate::matcher::MatcherTest::EqConst {
                    subject,
                    value: crate::matcher::MatcherConst::EmptyList,
                });
                Ok(())
            }
        }
    } else {
        tests.push(crate::matcher::MatcherTest::ListCons {
            subject: subject.clone(),
        });
        append_pattern_ops(
            &elems[0].node,
            crate::matcher::SubjectRef::ListHead(Box::new(subject.clone())),
            pinned_by_name,
            prepared_keys,
            tests,
            bindings,
        )?;
        let tail_subject = crate::matcher::SubjectRef::ListTail(Box::new(subject));
        if elems.len() == 1 {
            match tail {
                Some(tail) => append_pattern_ops(
                    &tail.node,
                    tail_subject,
                    pinned_by_name,
                    prepared_keys,
                    tests,
                    bindings,
                ),
                None => {
                    tests.push(crate::matcher::MatcherTest::EqConst {
                        subject: tail_subject,
                        value: crate::matcher::MatcherConst::EmptyList,
                    });
                    Ok(())
                }
            }
        } else {
            append_list_pattern_ops(
                &elems[1..],
                tail,
                tail_subject,
                pinned_by_name,
                prepared_keys,
                tests,
                bindings,
            )
        }
    }
}

fn push_matcher_node(
    nodes: &mut Vec<crate::matcher::MatcherNode>,
    node: crate::matcher::MatcherNode,
) -> crate::matcher::NodeId {
    let id = crate::matcher::NodeId(nodes.len() as u32);
    nodes.push(node);
    id
}

fn subject_to_matcher_ref(
    subject: &SubjectRef,
    input_by_var: &std::collections::HashMap<Var, crate::matcher::InputId>,
) -> Result<crate::matcher::SubjectRef, MatcherCompileError> {
    Ok(match subject {
        SubjectRef::Var(v) => crate::matcher::SubjectRef::Input(
            *input_by_var
                .get(v)
                .ok_or(MatcherCompileError::UnknownSubject(*v))?,
        ),
        SubjectRef::TupleField { tuple, index } => crate::matcher::SubjectRef::TupleField {
            tuple: Box::new(subject_to_matcher_ref(tuple, input_by_var)?),
            index: *index,
        },
        SubjectRef::ListHead(list) => crate::matcher::SubjectRef::ListHead(Box::new(
            subject_to_matcher_ref(list, input_by_var)?,
        )),
        SubjectRef::ListTail(list) => crate::matcher::SubjectRef::ListTail(Box::new(
            subject_to_matcher_ref(list, input_by_var)?,
        )),
    })
}

#[cfg(test)]
thread_local! {
    static COMPILE_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub fn reset_compile_count() {
    COMPILE_COUNT.with(|count| count.set(0));
}

#[cfg(test)]
pub fn compile_count() -> usize {
    COMPILE_COUNT.with(std::cell::Cell::get)
}

fn is_wildlike(p: &Pattern) -> bool {
    matches!(p, Pattern::Wildcard | Pattern::Var(_))
        || matches!(p, Pattern::As(_, inner) if is_wildlike(&inner.node))
}

fn pick_specialization_column(m: &CompileMatrix) -> Option<usize> {
    // Leftmost column that has any non-wildlike pattern across rows.
    (0..m.subjects.len()).find(|&col| m.rows.iter().any(|r| !is_wildlike(&r.patterns[col].node)))
}

fn find_unspecializable_row(m: &CompileMatrix, col: usize) -> Option<usize> {
    for (i, r) in m.rows.iter().enumerate() {
        // Look through As-patterns.
        let mut p = &r.patterns[col].node;
        while let Pattern::As(_, inner) = p {
            p = &inner.node;
        }
        // fz-puj.20 (H9 / E2) — Pinned patterns dispatch on a
        // runtime-resolved value rather than a constructor; there's no
        // SwitchKind for them. Route the row through PerRow so the
        // backend's per-row pattern walker handles the equality test
        // against `pinned[idx]`.
        if matches!(
            p,
            Pattern::Map(_) | Pattern::Bitstring(_) | Pattern::Pinned(_)
        ) {
            return Some(i);
        }
    }
    None
}

fn row_can_reject(row: &Row) -> bool {
    row.guard.is_some() || !row.preconditions.is_empty()
}

fn record_removed_column_bindings(row: &mut Row, col: usize, subject: &SubjectRef) {
    let mut bindings = Vec::new();
    collect_one(&row.patterns[col].node, subject, &mut bindings);
    row.bindings.extend(bindings);
}

fn collect_var_bindings(
    patterns: &[Spanned<Pattern>],
    subjects: &[SubjectRef],
) -> Vec<(String, SubjectRef)> {
    let mut out = Vec::new();
    for (p, subj) in patterns.iter().zip(subjects.iter()) {
        collect_one(&p.node, subj, &mut out);
    }
    out
}

fn collect_one(p: &Pattern, subj: &SubjectRef, out: &mut Vec<(String, SubjectRef)>) {
    match p {
        Pattern::Var(name) => out.push((name.clone(), subj.clone())),
        Pattern::As(name, inner) => {
            out.push((name.clone(), subj.clone()));
            collect_one(&inner.node, subj, out);
        }
        _ => {}
    }
}

fn pick_kind_for_column(m: &CompileMatrix, col: usize) -> SwitchKind {
    // Use the first row's non-wildlike pattern in this column.
    for r in &m.rows {
        let mut p = &r.patterns[col].node;
        while let Pattern::As(_, inner) = p {
            p = &inner.node;
        }
        match p {
            Pattern::Tuple(_) => return SwitchKind::TupleArity,
            Pattern::Atom(_) => return SwitchKind::Atom,
            Pattern::Int(_) => return SwitchKind::Int,
            Pattern::Float(_) => return SwitchKind::Float,
            Pattern::Bool(_) => return SwitchKind::Bool,
            Pattern::Nil => return SwitchKind::Nil,
            Pattern::Binary(_) => return SwitchKind::Binary,
            Pattern::List(_, _) => return SwitchKind::ListCons,
            _ => continue,
        }
    }
    // Should never reach: pick_specialization_column returned this col
    // because some row was non-wildlike. Fall back conservatively.
    SwitchKind::TupleArity
}

/// Strip As-wrappers off a column pattern. Bindings for removed columns are
/// recorded separately by `record_removed_column_bindings`.
fn peel_to_inner_with_bind(pat: &Spanned<Pattern>) -> (bool, Spanned<Pattern>) {
    let mut had = false;
    let mut cur = pat.clone();
    while let Pattern::As(_, inner) = &cur.node {
        had = true;
        let inner_box = inner.clone();
        cur = (*inner_box).clone();
    }
    (had, cur)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// fz-ul4.45 — Exhaustiveness + unreachability analysis
// ---------------------------------------------------------------------------

/// Body ids that no path through the matcher graph reaches. A row whose
/// body_id is in this set is unreachable — earlier rows fully cover its
/// matching space, OR its pattern conflicts with an earlier specialization.
///
/// fz-rcp.2 — guarded rows do NOT consume coverage. A guard is a runtime
/// predicate that can reject, so a row whose guard fails falls through
/// to the next row. For each row R we ask: "is R's pattern unreachable
/// given only the preceding unguarded rows?" — i.e., we form a sub-matrix
/// containing the unguarded prefix ending with R and check whether R's
/// body_id is reached there. R's own guard doesn't affect the check
/// (we're testing pattern coverage, not whether R itself matches at
/// runtime).
pub fn find_unreachable_rows(matrix: &Matrix) -> Vec<BodyId> {
    // Fast path: no guards anywhere → original single-compile behavior.
    if matrix.rows.iter().all(|r| r.guard.is_none()) {
        let row_bodies: std::collections::BTreeSet<BodyId> =
            matrix.rows.iter().map(|r| r.body_id).collect();
        let matcher = matcher_for_analysis(matrix.clone());
        let mut reached = std::collections::BTreeSet::new();
        collect_reachable_bodies_from_matcher(&matcher, matcher.root, &mut reached);
        return row_bodies.difference(&reached).copied().collect();
    }
    // Guarded matrix: walk row-by-row, accumulating only unguarded rows
    // into the prefix used to test subsequent rows.
    let mut unreachable: Vec<BodyId> = Vec::new();
    let mut unguarded_prefix: Vec<Row> = Vec::new();
    for row in &matrix.rows {
        let mut test_rows = unguarded_prefix.clone();
        let mut test_row = row.clone();
        test_row.guard = None;
        test_rows.push(test_row);
        let test_matrix = Matrix {
            subjects: matrix.subjects.clone(),
            rows: test_rows,
        };
        let matcher = matcher_for_analysis(test_matrix);
        let mut reached = std::collections::BTreeSet::new();
        collect_reachable_bodies_from_matcher(&matcher, matcher.root, &mut reached);
        if !reached.contains(&row.body_id) {
            unreachable.push(row.body_id);
        }
        if row.guard.is_none() {
            unguarded_prefix.push(row.clone());
        }
    }
    unreachable
}

/// True if any path through the matcher graph leads to Fail — i.e., the
/// matrix doesn't cover all possible subject values. Lowerers like
/// lower_case translate this to a runtime `:case_clause` halt; the warning
/// surfaces the gap at compile time.
pub fn is_inexhaustive(matrix: &Matrix) -> bool {
    is_inexhaustive_with_domains(matrix, &[])
}

pub fn is_inexhaustive_with_domains(matrix: &Matrix, domains: &[SubjectDomain]) -> bool {
    let matcher = matcher_for_analysis(normalize_guards_for_analysis(matrix.clone()));
    let domain_by_subject: std::collections::HashMap<Var, SubjectDomain> = matrix
        .subjects
        .iter()
        .copied()
        .zip(domains.iter().copied())
        .collect();
    has_reachable_fail_in_matcher(&matcher, matcher.root, &domain_by_subject)
}

fn matcher_for_analysis(matrix: Matrix) -> crate::matcher::Matcher {
    compile_matcher_subset(matrix).expect("pattern analysis matcher must compile")
}

fn normalize_guards_for_analysis(mut matrix: Matrix) -> Matrix {
    for row in &mut matrix.rows {
        if row.guard.is_some() {
            row.guard = Some(Spanned::dummy(Expr::Bool(true)));
        }
    }
    matrix
}

fn collect_reachable_bodies_from_matcher(
    matcher: &crate::matcher::Matcher,
    node: crate::matcher::NodeId,
    out: &mut std::collections::BTreeSet<BodyId>,
) {
    let Some(node) = matcher.node(node) else {
        return;
    };
    match node {
        crate::matcher::MatcherNode::Fail { .. } => {}
        crate::matcher::MatcherNode::Leaf(leaf) => {
            out.insert(leaf.body_id);
        }
        crate::matcher::MatcherNode::Switch { cases, default, .. } => {
            for (_, sub) in cases {
                collect_reachable_bodies_from_matcher(matcher, *sub, out);
            }
            collect_reachable_bodies_from_matcher(matcher, *default, out);
        }
        crate::matcher::MatcherNode::Test {
            on_true, on_false, ..
        }
        | crate::matcher::MatcherNode::Guard {
            on_true, on_false, ..
        } => {
            collect_reachable_bodies_from_matcher(matcher, *on_true, out);
            collect_reachable_bodies_from_matcher(matcher, *on_false, out);
        }
    }
}

fn has_reachable_fail_in_matcher(
    matcher: &crate::matcher::Matcher,
    node: crate::matcher::NodeId,
    domain_by_subject: &std::collections::HashMap<Var, SubjectDomain>,
) -> bool {
    let Some(node_ref) = matcher.node(node) else {
        return false;
    };
    match node_ref {
        crate::matcher::MatcherNode::Fail { .. } => true,
        crate::matcher::MatcherNode::Leaf(_) => false,
        crate::matcher::MatcherNode::Switch { cases, default, .. } => {
            if cases
                .iter()
                .any(|(_, sub)| has_reachable_fail_in_matcher(matcher, *sub, domain_by_subject))
            {
                return true;
            }
            if list_domain_is_covered_in_matcher(matcher, node, domain_by_subject) {
                return false;
            }
            has_reachable_fail_in_matcher(matcher, *default, domain_by_subject)
        }
        crate::matcher::MatcherNode::Test {
            on_true, on_false, ..
        }
        | crate::matcher::MatcherNode::Guard {
            on_true, on_false, ..
        } => {
            has_reachable_fail_in_matcher(matcher, *on_true, domain_by_subject)
                || has_reachable_fail_in_matcher(matcher, *on_false, domain_by_subject)
        }
    }
}

fn list_domain_is_covered_in_matcher(
    matcher: &crate::matcher::Matcher,
    node: crate::matcher::NodeId,
    domain_by_subject: &std::collections::HashMap<Var, SubjectDomain>,
) -> bool {
    let Some(crate::matcher::MatcherNode::Switch {
        subject,
        kind: crate::matcher::SwitchKind::ListCons,
        cases,
        ..
    }) = matcher.node(node)
    else {
        return false;
    };
    if matcher_subject_root_var(matcher, subject).and_then(|v| domain_by_subject.get(&v).copied())
        != Some(SubjectDomain::List)
    {
        return false;
    }
    let has_empty = cases
        .iter()
        .any(|(key, _)| matches!(key, crate::matcher::SwitchKey::EmptyList));
    let has_cons = cases
        .iter()
        .any(|(key, _)| matches!(key, crate::matcher::SwitchKey::Cons));
    has_empty && has_cons
}

fn matcher_subject_root_var(
    matcher: &crate::matcher::Matcher,
    subject: &crate::matcher::SubjectRef,
) -> Option<Var> {
    let input = match subject {
        crate::matcher::SubjectRef::Input(input) => *input,
        crate::matcher::SubjectRef::TupleField { tuple, .. }
        | crate::matcher::SubjectRef::ListHead(tuple)
        | crate::matcher::SubjectRef::ListTail(tuple)
        | crate::matcher::SubjectRef::MapValue { map: tuple, .. }
        | crate::matcher::SubjectRef::BitstringField {
            bitstring: tuple, ..
        } => return matcher_subject_root_var(matcher, tuple),
    };
    matcher.inputs.get(input.0 as usize).and_then(|i| i.var)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Pattern, Spanned};
    use crate::diag::FileId;

    fn sp<T>(node: T) -> Spanned<T> {
        let _ = FileId(0);
        Spanned::dummy(node)
    }

    fn row(patterns: Vec<Pattern>, body_id: BodyId) -> Row {
        Row {
            patterns: patterns.into_iter().map(sp).collect(),
            preconditions: Vec::new(),
            bindings: Vec::new(),
            guard: None,
            body_id,
        }
    }

    #[test]
    fn matcher_subset_rejects_non_monotonic_body_ids() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Wildcard], 2),
                row(vec![Pattern::Wildcard], 1),
            ],
        };

        assert_eq!(
            compile_matcher_subset(m),
            Err(MatcherCompileError::NonMonotonicBodyId {
                previous: 2,
                current: 1,
            })
        );
    }

    // ── fz-ul4.45 — exhaustiveness + unreachability ─────────────────────

    #[test]
    fn unreachable_row_after_wildcard_detected() {
        // Row 0 wildcard catches everything; row 1 unreachable.
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Int(42)], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![1]);
    }

    #[test]
    fn unreachable_row_after_full_atom_cover() {
        // Two atoms exhaust... no, atom space is infinite via wildcard.
        // Just check: row 0 matches :a, row 1 is :a too (unreachable).
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Atom("a".to_string())], 0),
                row(vec![Pattern::Atom("a".to_string())], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![1]);
    }

    fn row_with_guard(patterns: Vec<Pattern>, body_id: BodyId) -> Row {
        row_with_guard_expr(patterns, body_id, crate::ast::Expr::Bool(true))
    }

    fn row_with_guard_expr(patterns: Vec<Pattern>, body_id: BodyId, guard: Expr) -> Row {
        Row {
            patterns: patterns.into_iter().map(sp).collect(),
            preconditions: Vec::new(),
            bindings: Vec::new(),
            // Analysis cares that a guard can reject; it must not depend on
            // whether the concrete guard expression is executable by Matcher.
            guard: Some(sp(guard)),
            body_id,
        }
    }

    /// fz-rcp.2 — a guarded row does NOT consume coverage. The row
    /// that follows it with the same pattern is reachable (the guard
    /// can reject at runtime).
    #[test]
    fn guarded_row_does_not_dominate_later_row() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert!(
            dead.is_empty(),
            "guarded row should not mark unguarded successor unreachable, got {:?}",
            dead
        );
    }

    #[test]
    fn guarded_reachability_does_not_lower_guard_expression() {
        let unsupported_guard = Expr::Call(Box::new(sp(Expr::Var("opaque".to_string()))), vec![]);
        let reachable = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard_expr(vec![Pattern::Wildcard], 0, unsupported_guard),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        assert!(find_unreachable_rows(&reachable).is_empty());

        let inexhaustive = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row_with_guard_expr(
                vec![Pattern::Wildcard],
                0,
                Expr::Call(Box::new(sp(Expr::Var("opaque".to_string()))), vec![]),
            )],
        };
        assert!(is_inexhaustive(&inexhaustive));
    }

    /// An unguarded wildcard still dominates later rows. Sanity check
    /// the guard-aware path doesn't break the normal case.
    #[test]
    fn unguarded_wildcard_still_dominates() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Wildcard], 1),
                row(vec![Pattern::Int(42)], 2),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![2], "row 2 should be unreachable past row 1");
    }

    /// A guarded row whose pattern is fully covered by an unguarded
    /// predecessor IS unreachable (the predecessor's pattern matches
    /// every value the guarded row could see).
    #[test]
    fn guarded_row_unreachable_under_unguarded_cover() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Wildcard], 0),
                row_with_guard(vec![Pattern::Wildcard], 1),
            ],
        };
        let dead = find_unreachable_rows(&m);
        assert_eq!(dead, vec![1]);
    }

    #[test]
    fn all_reachable_rows_no_warnings() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Int(0)], 0),
                row(vec![Pattern::Int(1)], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };
        assert!(find_unreachable_rows(&m).is_empty());
    }

    #[test]
    fn distinct_utf8_binary_literals_are_reachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Binary(b"hi".to_vec())], 0),
                row(vec![Pattern::Binary(b"bye".to_vec())], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };

        assert!(find_unreachable_rows(&m).is_empty());
        assert!(!is_inexhaustive(&m));
    }

    #[test]
    fn distinct_float_literals_are_reachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Float(1.5)], 0),
                row(vec![Pattern::Float(2.5)], 1),
                row(vec![Pattern::Wildcard], 2),
            ],
        };

        assert!(find_unreachable_rows(&m).is_empty());
        assert!(!is_inexhaustive(&m));
    }

    #[test]
    fn duplicate_float_literal_is_unreachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Float(1.5)], 0),
                row(vec![Pattern::Float(1.5)], 1),
            ],
        };

        assert_eq!(find_unreachable_rows(&m), vec![1]);
    }

    #[test]
    fn duplicate_utf8_binary_literal_is_unreachable() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Binary(b"hi".to_vec())], 0),
                row(vec![Pattern::Binary(b"hi".to_vec())], 1),
            ],
        };

        assert_eq!(find_unreachable_rows(&m), vec![1]);
    }

    #[test]
    fn utf8_binary_literals_without_wildcard_are_inexhaustive() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Binary(b"hi".to_vec())], 0),
                row(vec![Pattern::Binary(b"bye".to_vec())], 1),
            ],
        };

        assert!(is_inexhaustive(&m));
    }

    #[test]
    fn inexhaustive_no_wildcard_flagged() {
        // Two specific ints, no wildcard → default reaches Fail.
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(vec![Pattern::Int(0)], 0), row(vec![Pattern::Int(1)], 1)],
        };
        assert!(is_inexhaustive(&m));
    }

    #[test]
    fn exhaustive_with_wildcard_not_flagged() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Int(0)], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        assert!(!is_inexhaustive(&m));
    }

    #[test]
    fn empty_list_and_cons_exhaust_list_domain() {
        let cons = Pattern::List(
            vec![sp(Pattern::Var("h".to_string()))],
            Some(Box::new(sp(Pattern::Var("t".to_string())))),
        );
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::List(vec![], None)], 0),
                row(vec![cons], 1),
            ],
        };
        assert!(!is_inexhaustive_with_domains(&m, &[SubjectDomain::List]));
    }

    #[test]
    fn empty_list_and_cons_do_not_exhaust_any_domain() {
        let cons = Pattern::List(
            vec![sp(Pattern::Var("h".to_string()))],
            Some(Box::new(sp(Pattern::Var("t".to_string())))),
        );
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::List(vec![], None)], 0),
                row(vec![cons], 1),
            ],
        };
        assert!(is_inexhaustive_with_domains(&m, &[SubjectDomain::Any]));
    }

    #[test]
    fn matcher_subset_var_leaf_preserves_binding() {
        let m = Matrix {
            subjects: vec![Var(42)],
            rows: vec![row(vec![Pattern::Var("x".to_string())], 7)],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(matcher.root) else {
            panic!("expected root leaf, got {:?}", matcher.node(matcher.root));
        };

        assert_eq!(leaf.body_id, 7);
        assert_eq!(leaf.bindings.len(), 1);
        assert_eq!(leaf.bindings[0].name, "x");
        assert_eq!(
            leaf.bindings[0].source,
            crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
        );
    }

    #[test]
    fn matcher_subset_tuple_switch_preserves_shape_and_field_binding() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(
                vec![Pattern::Tuple(vec![
                    sp(Pattern::Atom("ok".to_string())),
                    sp(Pattern::Var("x".to_string())),
                ])],
                3,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        let Some(crate::matcher::MatcherNode::Switch { kind, cases, .. }) =
            matcher.node(matcher.root)
        else {
            panic!("expected root switch, got {:?}", matcher.node(matcher.root));
        };

        assert_eq!(*kind, crate::matcher::SwitchKind::TupleArity);
        assert_eq!(cases[0].0, crate::matcher::SwitchKey::Arity(2));
        let arity_node = cases[0].1;
        let Some(crate::matcher::MatcherNode::Switch {
            kind,
            cases: atom_cases,
            ..
        }) = matcher.node(arity_node)
        else {
            panic!(
                "expected nested atom switch, got {:?}",
                matcher.node(arity_node)
            );
        };
        assert_eq!(*kind, crate::matcher::SwitchKind::Atom);
        assert_eq!(
            atom_cases[0].0,
            crate::matcher::SwitchKey::AtomName("ok".to_string())
        );
        let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(atom_cases[0].1) else {
            panic!(
                "expected atom leaf, got {:?}",
                matcher.node(atom_cases[0].1)
            );
        };
        assert_eq!(
            leaf.bindings[0].source,
            crate::matcher::SubjectRef::TupleField {
                tuple: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                    0
                ))),
                index: 1,
            }
        );
    }

    #[test]
    fn matcher_subset_tuple_default_preserves_removed_column_binding() {
        let m = Matrix {
            subjects: vec![Var(2)],
            rows: vec![
                row(
                    vec![Pattern::Tuple(vec![
                        sp(Pattern::Atom("ok".to_string())),
                        sp(Pattern::Wildcard),
                    ])],
                    0,
                ),
                row(vec![Pattern::Var("fallback".to_string())], 1),
            ],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        let Some(crate::matcher::MatcherNode::Switch { default, .. }) = matcher.node(matcher.root)
        else {
            panic!(
                "expected tuple switch, got {:?}",
                matcher.node(matcher.root)
            );
        };
        let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(*default) else {
            panic!("expected default leaf, got {:?}", matcher.node(*default));
        };

        assert_eq!(leaf.body_id, 1);
        assert_eq!(leaf.bindings.len(), 1);
        assert_eq!(leaf.bindings[0].name, "fallback");
        assert_eq!(
            leaf.bindings[0].source,
            crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
        );
    }

    #[test]
    fn matcher_subset_list_cons_preserves_head_tail_refs() {
        let m = Matrix {
            subjects: vec![Var(3)],
            rows: vec![row(
                vec![Pattern::List(
                    vec![sp(Pattern::Var("h".to_string()))],
                    Some(Box::new(sp(Pattern::Var("t".to_string())))),
                )],
                0,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        let Some(crate::matcher::MatcherNode::Switch { cases, .. }) = matcher.node(matcher.root)
        else {
            panic!("expected list switch, got {:?}", matcher.node(matcher.root));
        };
        let (_, cons_node) = cases
            .iter()
            .find(|(key, _)| *key == crate::matcher::SwitchKey::Cons)
            .expect("cons case");
        let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(*cons_node) else {
            panic!("expected cons leaf, got {:?}", matcher.node(*cons_node));
        };

        assert_eq!(
            leaf.bindings[0].source,
            crate::matcher::SubjectRef::ListHead(Box::new(crate::matcher::SubjectRef::Input(
                crate::matcher::InputId(0),
            )))
        );
        assert_eq!(
            leaf.bindings[1].source,
            crate::matcher::SubjectRef::ListTail(Box::new(crate::matcher::SubjectRef::Input(
                crate::matcher::InputId(0),
            )))
        );
    }

    #[test]
    fn matcher_subset_list_default_preserves_removed_column_binding() {
        let m = Matrix {
            subjects: vec![Var(4)],
            rows: vec![
                row(
                    vec![Pattern::List(
                        vec![sp(Pattern::Var("head".to_string()))],
                        Some(Box::new(sp(Pattern::Var("tail".to_string())))),
                    )],
                    0,
                ),
                row(vec![Pattern::Var("fallback".to_string())], 1),
            ],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        let Some(crate::matcher::MatcherNode::Switch { default, .. }) = matcher.node(matcher.root)
        else {
            panic!("expected list switch, got {:?}", matcher.node(matcher.root));
        };
        let Some(crate::matcher::MatcherNode::Leaf(leaf)) = matcher.node(*default) else {
            panic!("expected default leaf, got {:?}", matcher.node(*default));
        };

        assert_eq!(leaf.body_id, 1);
        assert_eq!(leaf.bindings.len(), 1);
        assert_eq!(leaf.bindings[0].name, "fallback");
        assert_eq!(
            leaf.bindings[0].source,
            crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
        );
    }

    #[test]
    fn matcher_subset_lowers_guard_to_guard_node() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard(vec![Pattern::Wildcard], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        let matcher = compile_matcher_subset(m).expect("compile guarded matcher");
        let Some(crate::matcher::MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        }) = matcher.node(matcher.root)
        else {
            panic!("expected guard root, got {:?}", matcher.node(matcher.root));
        };
        assert!(matches!(
            expr,
            crate::matcher::GuardExpr::Const(crate::matcher::MatcherConst::Bool(true))
        ));
        let Some(crate::matcher::MatcherNode::Leaf(true_leaf)) = matcher.node(*on_true) else {
            panic!("expected guard true leaf, got {:?}", matcher.node(*on_true));
        };
        assert_eq!(true_leaf.body_id, 0);
        let Some(crate::matcher::MatcherNode::Leaf(false_leaf)) = matcher.node(*on_false) else {
            panic!(
                "expected guard false fallthrough leaf, got {:?}",
                matcher.node(*on_false)
            );
        };
        assert_eq!(false_leaf.body_id, 1);
    }

    #[test]
    fn matcher_subset_guard_capture_walks_call_args_without_capturing_callee() {
        let guard = Expr::Call(
            Box::new(sp(Expr::Var("positive".to_string()))),
            vec![sp(Expr::BinOp(
                crate::ast::BinOp::Add,
                Box::new(sp(Expr::Var("x".to_string()))),
                Box::new(sp(Expr::Var("limit".to_string()))),
            ))],
        );
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row_with_guard_expr(vec![Pattern::Var("x".to_string())], 0, guard),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        let mut resolver = |_name: &str, _arity: usize, _args: Vec<crate::matcher::GuardExpr>| {
            Ok(Some(crate::matcher::GuardExpr::Const(
                crate::matcher::MatcherConst::Bool(true),
            )))
        };
        let matcher =
            compile_matcher_subset_with_guard_resolver(m, &mut resolver).expect("compile matcher");

        assert_eq!(matcher.pinned.len(), 1);
        assert_eq!(matcher.pinned[0].name, "limit");
    }

    #[test]
    fn matcher_subset_lowers_pinned_per_row_to_eq_pinned_test() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Pinned("want".to_string())], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");

        assert_eq!(matcher.pinned.len(), 1);
        assert_eq!(matcher.pinned[0].name, "want");
        let Some(crate::matcher::MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        }) = matcher.node(matcher.root)
        else {
            panic!(
                "expected pinned test root, got {:?}",
                matcher.node(matcher.root)
            );
        };
        assert_eq!(
            *test,
            crate::matcher::MatcherTest::EqPinned {
                subject: crate::matcher::SubjectRef::Input(crate::matcher::InputId(0)),
                pinned: crate::matcher::PinnedId(0),
            }
        );
        assert!(matches!(
            matcher.node(*on_true),
            Some(crate::matcher::MatcherNode::Leaf(
                crate::matcher::MatcherLeaf { body_id: 0, .. }
            ))
        ));
        assert!(matches!(
            matcher.node(*on_false),
            Some(crate::matcher::MatcherNode::Leaf(
                crate::matcher::MatcherLeaf { body_id: 1, .. }
            ))
        ));
    }

    #[test]
    fn matcher_subset_lowers_tuple_field_pinned_with_var_binding() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(
                vec![Pattern::Tuple(vec![
                    sp(Pattern::Atom("reply".to_string())),
                    sp(Pattern::Pinned("ref".to_string())),
                    sp(Pattern::Var("payload".to_string())),
                ])],
                0,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        let pinned_test = matcher
            .nodes
            .iter()
            .find_map(|node| match node {
                crate::matcher::MatcherNode::Test {
                    test: test @ crate::matcher::MatcherTest::EqPinned { .. },
                    ..
                } => Some(test),
                _ => None,
            })
            .expect("pinned test");

        assert_eq!(matcher.pinned[0].name, "ref");
        assert_eq!(
            *pinned_test,
            crate::matcher::MatcherTest::EqPinned {
                subject: crate::matcher::SubjectRef::TupleField {
                    tuple: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                        0
                    ))),
                    index: 1,
                },
                pinned: crate::matcher::PinnedId(0),
            }
        );
        let payload_binding = matcher.nodes.iter().find_map(|node| match node {
            crate::matcher::MatcherNode::Leaf(leaf) => leaf
                .bindings
                .iter()
                .find(|binding| binding.name == "payload"),
            _ => None,
        });
        assert_eq!(
            payload_binding.map(|binding| binding.source.clone()),
            Some(crate::matcher::SubjectRef::TupleField {
                tuple: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                    0
                ))),
                index: 2,
            })
        );
    }

    #[test]
    fn matcher_subset_lowers_empty_map_to_map_kind_test() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![
                row(vec![Pattern::Map(vec![])], 0),
                row(vec![Pattern::Wildcard], 1),
            ],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");

        let Some(crate::matcher::MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        }) = matcher.node(matcher.root)
        else {
            panic!(
                "expected map-kind test root, got {:?}",
                matcher.node(matcher.root)
            );
        };
        assert_eq!(
            *test,
            crate::matcher::MatcherTest::MapKind {
                subject: crate::matcher::SubjectRef::Input(crate::matcher::InputId(0)),
            }
        );
        assert!(matches!(
            matcher.node(*on_true),
            Some(crate::matcher::MatcherNode::Leaf(
                crate::matcher::MatcherLeaf { body_id: 0, .. }
            ))
        ));
        assert!(matches!(
            matcher.node(*on_false),
            Some(crate::matcher::MatcherNode::Leaf(
                crate::matcher::MatcherLeaf { body_id: 1, .. }
            ))
        ));
    }

    #[test]
    fn matcher_subset_lowers_scalar_map_key_to_has_key_and_value_subject() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(
                vec![Pattern::Map(vec![(
                    sp(Pattern::Atom("id".to_string())),
                    sp(Pattern::Int(42)),
                )])],
                0,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        assert_eq!(
            matcher.prepared_keys,
            vec![crate::matcher::MatcherConst::AtomName("id".to_string())]
        );
        let map_key = crate::matcher::MatcherConst::PreparedKey(0);

        assert!(matcher.nodes.iter().any(|node| matches!(
            node,
            crate::matcher::MatcherNode::Test {
                test: crate::matcher::MatcherTest::MapHasKey {
                    subject: crate::matcher::SubjectRef::Input(crate::matcher::InputId(0)),
                    key,
                },
                ..
            } if *key == map_key
        )));
        assert!(matcher.nodes.iter().any(|node| matches!(
            node,
            crate::matcher::MatcherNode::Test {
                test: crate::matcher::MatcherTest::EqConst {
                    subject: crate::matcher::SubjectRef::MapValue { map, key },
                    value: crate::matcher::MatcherConst::Int(42),
                },
                ..
            } if **map == crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
                && *key == map_key
        )));
    }

    #[test]
    fn matcher_subset_checks_key_presence_before_matching_nil_value() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(
                vec![Pattern::Map(vec![(sp(Pattern::Int(7)), sp(Pattern::Nil))])],
                0,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");

        let Some(crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::MapKind { .. },
            on_true: has_key,
            ..
        }) = matcher.node(matcher.root)
        else {
            panic!(
                "expected map-kind root, got {:?}",
                matcher.node(matcher.root)
            );
        };
        let Some(crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::MapHasKey { .. },
            on_true: value_test,
            ..
        }) = matcher.node(*has_key)
        else {
            panic!("expected map-has-key after kind test");
        };
        assert!(matches!(
            matcher.node(*value_test),
            Some(crate::matcher::MatcherNode::Test {
                test: crate::matcher::MatcherTest::EqConst {
                    subject: crate::matcher::SubjectRef::MapValue { .. },
                    value: crate::matcher::MatcherConst::Nil,
                },
                ..
            })
        ));
    }

    #[test]
    fn matcher_subset_lowers_heap_map_keys_to_prepared_slots() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(
                vec![Pattern::Map(vec![(
                    sp(Pattern::Binary(b"id".to_vec())),
                    sp(Pattern::Wildcard),
                )])],
                0,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");
        assert_eq!(
            matcher.prepared_keys,
            vec![crate::matcher::MatcherConst::Utf8Binary(b"id".to_vec())]
        );
        assert!(matcher.nodes.iter().any(|node| matches!(
            node,
            crate::matcher::MatcherNode::Test {
                test: crate::matcher::MatcherTest::MapHasKey {
                    key: crate::matcher::MatcherConst::PreparedKey(0),
                    ..
                },
                ..
            }
        )));
    }

    #[test]
    fn matcher_subset_lowers_empty_bitstring_to_bitstring_test() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(vec![Pattern::Bitstring(vec![])], 0)],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");

        let Some(crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::Bitstring { subject, fields },
            ..
        }) = matcher.node(matcher.root)
        else {
            panic!(
                "expected bitstring test root, got {:?}",
                matcher.node(matcher.root)
            );
        };
        assert_eq!(
            *subject,
            crate::matcher::SubjectRef::Input(crate::matcher::InputId(0))
        );
        assert!(fields.is_empty());
    }

    #[test]
    fn matcher_subset_lowers_bitstring_field_specs_and_bindings() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(
                vec![Pattern::Bitstring(vec![crate::ast::BitField {
                    value: sp(Pattern::Var("byte".to_string())),
                    spec: crate::ast::BitFieldSpec {
                        ty: crate::ast::BitType::Integer,
                        size: Some(crate::ast::BitSize::Literal(8)),
                        endian: crate::ast::Endian::Little,
                        signed: true,
                        unit: Some(1),
                    },
                }])],
                0,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");

        let Some(crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::Bitstring { fields, .. },
            ..
        }) = matcher.node(matcher.root)
        else {
            panic!("expected bitstring root");
        };
        assert_eq!(
            fields,
            &vec![crate::matcher::MatcherBitField {
                ty: crate::matcher::MatcherBitType::Integer,
                size: Some(crate::matcher::MatcherBitSize::Literal(8)),
                endian: crate::matcher::MatcherEndian::Little,
                signed: true,
                unit: Some(1),
                direct_bindings: vec!["byte".to_string()],
            }]
        );
        let byte_binding = matcher.nodes.iter().find_map(|node| match node {
            crate::matcher::MatcherNode::Leaf(leaf) => {
                leaf.bindings.iter().find(|binding| binding.name == "byte")
            }
            _ => None,
        });
        assert_eq!(
            byte_binding.map(|binding| binding.source.clone()),
            Some(crate::matcher::SubjectRef::BitstringField {
                bitstring: Box::new(crate::matcher::SubjectRef::Input(crate::matcher::InputId(
                    0
                ))),
                index: 0,
            })
        );
    }

    #[test]
    fn matcher_subset_lowers_dynamic_bitstring_size_by_binding_name() {
        let m = Matrix {
            subjects: vec![Var(0)],
            rows: vec![row(
                vec![Pattern::Bitstring(vec![
                    crate::ast::BitField {
                        value: sp(Pattern::Var("n".to_string())),
                        spec: crate::ast::BitFieldSpec {
                            size: Some(crate::ast::BitSize::Literal(8)),
                            ..Default::default()
                        },
                    },
                    crate::ast::BitField {
                        value: sp(Pattern::Var("payload".to_string())),
                        spec: crate::ast::BitFieldSpec {
                            ty: crate::ast::BitType::Binary,
                            size: Some(crate::ast::BitSize::Var("n".to_string())),
                            ..Default::default()
                        },
                    },
                ])],
                0,
            )],
        };
        let matcher = compile_matcher_subset(m).expect("compile matcher subset");

        let Some(crate::matcher::MatcherNode::Test {
            test: crate::matcher::MatcherTest::Bitstring { fields, .. },
            ..
        }) = matcher.node(matcher.root)
        else {
            panic!("expected bitstring root");
        };
        assert_eq!(
            fields[1].size,
            Some(crate::matcher::MatcherBitSize::BindingName("n".to_string()))
        );
    }
}
