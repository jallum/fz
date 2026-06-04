use crate::ast::{Pattern, Spanned};
use crate::diag::Span;
use crate::exec::matcher::{
    GuardExpr, InputId, MatcherBinding, MatcherConst, MatcherLeaf, MatcherNode, NodeId, PinnedId, SwitchKey, SwitchKind,
};
use crate::fz_ir::Var;
use std::collections::{BTreeMap, HashMap};

use super::collect::collect_var_bindings;
use super::guard::{guard_to_matcher_node, preconditions_to_matcher_nodes};
use super::pattern_ops::{
    append_pattern_ops, find_unspecializable_row, is_wildlike, peel_to_inner_with_bind, pick_kind_for_column,
    pick_specialization_column, push_matcher_node, record_removed_column_bindings, row_can_reject,
    subject_to_matcher_ref,
};
use super::{CompilePatternMatrix, PatternMatrixCompileError, Row, SubjectRef};

pub(crate) struct MatcherBuilder<'a, F>
where
    F: FnMut(&str, usize, Vec<GuardExpr>) -> Result<Option<GuardExpr>, PatternMatrixCompileError>,
{
    pub(crate) input_by_var: HashMap<Var, InputId>,
    pub(crate) pinned_by_name: HashMap<String, PinnedId>,
    pub(crate) nodes: Vec<MatcherNode>,
    pub(crate) prepared_keys: Vec<MatcherConst>,
    pub(crate) guard_call_resolver: &'a mut F,
}

impl<F> MatcherBuilder<'_, F>
where
    F: FnMut(&str, usize, Vec<GuardExpr>) -> Result<Option<GuardExpr>, PatternMatrixCompileError>,
{
    fn push(&mut self, node: MatcherNode) -> NodeId {
        push_matcher_node(&mut self.nodes, node)
    }

    pub(crate) fn compile_inner(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        if pattern_matrix.rows.is_empty() {
            return Ok(self.push(MatcherNode::Fail { span: Span::DUMMY }));
        }
        if pattern_matrix.subjects.is_empty() {
            return self.leaf_or_rejecting_chain(pattern_matrix.rows, vec![]);
        }

        if pattern_matrix
            .rows
            .first()
            .map(|r| r.patterns.iter().all(|p| is_wildlike(&p.node)))
            .unwrap_or(false)
            && pattern_matrix
                .rows
                .first()
                .is_some_and(|r| r.guard.is_none() && r.preconditions.is_empty())
        {
            return self.leaf_or_rejecting_chain(pattern_matrix.rows, pattern_matrix.subjects);
        }

        let col = match pick_specialization_column(&pattern_matrix) {
            Some(c) => c,
            None => {
                return self.leaf_or_rejecting_chain(pattern_matrix.rows, pattern_matrix.subjects);
            }
        };

        if let Some(row_idx) = find_unspecializable_row(&pattern_matrix, col) {
            let mut rows = pattern_matrix.rows;
            let row = rows.remove(row_idx);
            let subjects = pattern_matrix.subjects.clone();
            let rest = CompilePatternMatrix {
                subjects: pattern_matrix.subjects,
                rows,
            };
            let on_fail = self.compile_inner(rest)?;
            return self.per_row_to_matcher_node(&subjects, &row, on_fail);
        }

        self.specialize_and_compile(pattern_matrix, col)
    }

    fn leaf_or_rejecting_chain(
        &mut self,
        mut rows: Vec<Row>,
        subjects: Vec<SubjectRef>,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        let row = rows.remove(0);
        let reject = if row_can_reject(&row) {
            Some(self.compile_inner(CompilePatternMatrix {
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
        on_reject: Option<NodeId>,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        let mut bindings = row.bindings.clone();
        bindings.extend(collect_var_bindings(&row.patterns, subjects));
        let matcher_bindings = bindings
            .iter()
            .map(|(name, subject)| {
                Ok(MatcherBinding {
                    name: name.clone(),
                    source: subject_to_matcher_ref(subject, &self.input_by_var)?,
                    span: Span::DUMMY,
                })
            })
            .collect::<Result<Vec<_>, PatternMatrixCompileError>>()?;
        let leaf = self.push(MatcherNode::Leaf(MatcherLeaf {
            body_id: row.body_id,
            bindings: matcher_bindings.clone(),
            span: Span::DUMMY,
        }));
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
        on_fail: NodeId,
    ) -> Result<NodeId, PatternMatrixCompileError> {
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
        let leaf = self.push(MatcherNode::Leaf(MatcherLeaf {
            body_id: row.body_id,
            bindings: bindings.clone(),
            span: Span::DUMMY,
        }));
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
            current = self.push(MatcherNode::Test {
                test,
                on_true: current,
                on_false: on_fail,
                span: Span::DUMMY,
            });
        }
        Ok(current)
    }

    fn specialize_and_compile(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        let subject = pattern_matrix.subjects[col].clone();
        let kind = pick_kind_for_column(&pattern_matrix, col);
        match kind {
            SwitchKind::TupleArity => self.specialize_tuple_arity(pattern_matrix, col, subject),
            SwitchKind::Atom => self.specialize_atom(pattern_matrix, col, subject),
            SwitchKind::Int => self.specialize_int(pattern_matrix, col, subject),
            SwitchKind::Float => self.specialize_float(pattern_matrix, col, subject),
            SwitchKind::Bool => self.specialize_bool(pattern_matrix, col, subject),
            SwitchKind::Nil => self.specialize_nil(pattern_matrix, col, subject),
            SwitchKind::Binary => self.specialize_binary(pattern_matrix, col, subject),
            SwitchKind::ListCons => self.specialize_listcons(pattern_matrix, col, subject),
        }
    }

    fn switch_node(
        &mut self,
        subject: SubjectRef,
        kind: SwitchKind,
        cases: Vec<(SwitchKey, NodeId)>,
        default: NodeId,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        let subject = subject_to_matcher_ref(&subject, &self.input_by_var)?;
        Ok(self.push(MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            span: Span::DUMMY,
        }))
    }

    fn specialize_tuple_arity(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        let mut by_arity: BTreeMap<u32, Vec<Row>> = BTreeMap::new();
        let mut default_rows: Vec<Row> = Vec::new();
        let mut other_rows: Vec<Row> = Vec::new();

        for row in pattern_matrix.rows {
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

        let mut cases: Vec<(SwitchKey, NodeId)> = Vec::new();
        for (arity, rows) in by_arity {
            let mut all_rows = rows;
            for d in &default_rows {
                let mut dr = d.clone();
                record_removed_column_bindings(&mut dr, col, &subject);
                let span = dr.patterns[col].span;
                let wilds: Vec<Spanned<Pattern>> = (0..arity).map(|_| Spanned::new(Pattern::Wildcard, span)).collect();
                dr.patterns.splice(col..=col, wilds);
                all_rows.push(dr);
            }
            all_rows.sort_by_key(|r| r.body_id);
            let mut new_subjects = pattern_matrix.subjects.clone();
            let projections: Vec<SubjectRef> = (0..arity)
                .map(|i| SubjectRef::TupleField {
                    tuple: Box::new(subject.clone()),
                    index: i,
                })
                .collect();
            new_subjects.splice(col..=col, projections);

            let sub = self.compile_inner(CompilePatternMatrix {
                subjects: new_subjects,
                rows: all_rows,
            })?;
            cases.push((SwitchKey::Arity(arity), sub));
        }

        let default = if default_rows.is_empty() && other_rows.is_empty() {
            self.push(MatcherNode::Fail { span: Span::DUMMY })
        } else if other_rows.is_empty() {
            let mut new_subjects = pattern_matrix.subjects.clone();
            new_subjects.remove(col);
            let new_rows: Vec<Row> = default_rows
                .into_iter()
                .map(|mut r| {
                    record_removed_column_bindings(&mut r, col, &subject);
                    r.patterns.remove(col);
                    r
                })
                .collect();
            self.compile_inner(CompilePatternMatrix {
                subjects: new_subjects,
                rows: new_rows,
            })?
        } else {
            let mut rows: Vec<Row> = other_rows.into_iter().chain(default_rows).collect();
            rows.sort_by_key(|r| r.body_id);
            self.compile_inner(CompilePatternMatrix {
                subjects: pattern_matrix.subjects.clone(),
                rows,
            })?
        };

        self.switch_node(subject, SwitchKind::TupleArity, cases, default)
    }

    fn specialize_atom(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        self.specialize_literal(pattern_matrix, col, subject, SwitchKind::Atom, |p| match p {
            Pattern::Atom(s) => Some(SwitchKey::AtomName(s.clone())),
            _ => None,
        })
    }

    fn specialize_int(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        self.specialize_literal(pattern_matrix, col, subject, SwitchKind::Int, |p| match p {
            Pattern::Int(n) => Some(SwitchKey::Int(*n)),
            _ => None,
        })
    }

    fn specialize_float(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        self.specialize_literal(pattern_matrix, col, subject, SwitchKind::Float, |p| match p {
            Pattern::Float(n) => Some(SwitchKey::FloatBits(n.to_bits())),
            _ => None,
        })
    }

    fn specialize_bool(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        self.specialize_literal(pattern_matrix, col, subject, SwitchKind::Bool, |p| match p {
            Pattern::Bool(b) => Some(SwitchKey::Bool(*b)),
            _ => None,
        })
    }

    fn specialize_nil(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        self.specialize_literal(pattern_matrix, col, subject, SwitchKind::Nil, |p| match p {
            Pattern::Nil => Some(SwitchKey::Nil),
            _ => None,
        })
    }

    fn specialize_binary(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        self.specialize_literal(pattern_matrix, col, subject, SwitchKind::Binary, |p| match p {
            Pattern::Binary(bytes) => Some(SwitchKey::Utf8Binary(bytes.clone())),
            _ => None,
        })
    }

    fn specialize_listcons(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
    ) -> Result<NodeId, PatternMatrixCompileError> {
        let mut by_key: BTreeMap<SwitchKey, Vec<Row>> = BTreeMap::new();
        let mut default_rows: Vec<Row> = Vec::new();

        for row in pattern_matrix.rows {
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
                            tail.as_deref()
                                .cloned()
                                .unwrap_or_else(|| Spanned::new(Pattern::List(vec![], None), head.span))
                        } else {
                            Spanned::new(
                                Pattern::List(elems[1..].to_vec(), tail.as_ref().map(|p| Box::new((**p).clone()))),
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

        let mut cases: Vec<(SwitchKey, NodeId)> = Vec::new();
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
                let mut s = pattern_matrix.subjects.clone();
                s.remove(col);
                s
            } else {
                let mut s = pattern_matrix.subjects.clone();
                s.splice(
                    col..=col,
                    [
                        SubjectRef::ListHead(Box::new(subject.clone())),
                        SubjectRef::ListTail(Box::new(subject.clone())),
                    ],
                );
                s
            };
            let sub = self.compile_inner(CompilePatternMatrix {
                subjects: new_subjects,
                rows,
            })?;
            cases.push((key, sub));
        }

        let mut new_subjects = pattern_matrix.subjects.clone();
        new_subjects.remove(col);
        let new_rows: Vec<Row> = default_rows
            .into_iter()
            .map(|mut r| {
                record_removed_column_bindings(&mut r, col, &subject);
                r.patterns.remove(col);
                r
            })
            .collect();
        let default = self.compile_inner(CompilePatternMatrix {
            subjects: new_subjects,
            rows: new_rows,
        })?;

        self.switch_node(subject, SwitchKind::ListCons, cases, default)
    }

    fn specialize_literal<G>(
        &mut self,
        pattern_matrix: CompilePatternMatrix,
        col: usize,
        subject: SubjectRef,
        kind: SwitchKind,
        key_for: G,
    ) -> Result<NodeId, PatternMatrixCompileError>
    where
        G: Fn(&Pattern) -> Option<SwitchKey>,
    {
        let mut by_key: BTreeMap<SwitchKey, Vec<Row>> = BTreeMap::new();
        let mut default_rows: Vec<Row> = Vec::new();
        let mut other_rows: Vec<Row> = Vec::new();

        for row in pattern_matrix.rows {
            let mut row = row;
            let (_, inner_pat) = peel_to_inner_with_bind(&row.patterns[col]);
            row.patterns[col] = inner_pat;
            let p = &row.patterns[col].node;
            if let Some(k) = key_for(p) {
                let mut nr = row.clone();
                record_removed_column_bindings(&mut nr, col, &subject);
                nr.patterns.remove(col);
                by_key.entry(k).or_default().push(nr);
            } else if matches!(p, Pattern::Wildcard | Pattern::Var(_)) {
                default_rows.push(row);
            } else {
                other_rows.push(row);
            }
        }

        let mut cases: Vec<(SwitchKey, NodeId)> = Vec::new();
        for (key, mut rows) in by_key {
            for d in &default_rows {
                let mut dr = d.clone();
                record_removed_column_bindings(&mut dr, col, &subject);
                dr.patterns.remove(col);
                rows.push(dr);
            }
            rows.sort_by_key(|r| r.body_id);
            let mut new_subjects = pattern_matrix.subjects.clone();
            new_subjects.remove(col);
            let sub = self.compile_inner(CompilePatternMatrix {
                subjects: new_subjects,
                rows,
            })?;
            cases.push((key, sub));
        }

        let default = if other_rows.is_empty() {
            let mut new_subjects = pattern_matrix.subjects.clone();
            new_subjects.remove(col);
            let new_rows: Vec<Row> = default_rows
                .into_iter()
                .map(|mut r| {
                    record_removed_column_bindings(&mut r, col, &subject);
                    r.patterns.remove(col);
                    r
                })
                .collect();
            self.compile_inner(CompilePatternMatrix {
                subjects: new_subjects,
                rows: new_rows,
            })?
        } else {
            let mut rows: Vec<Row> = other_rows.into_iter().chain(default_rows).collect();
            rows.sort_by_key(|r| r.body_id);
            self.compile_inner(CompilePatternMatrix {
                subjects: pattern_matrix.subjects.clone(),
                rows,
            })?
        };

        self.switch_node(subject, kind, cases, default)
    }
}
