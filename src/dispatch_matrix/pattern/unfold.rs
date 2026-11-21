//! A guard helper call, read as the facts its clauses state.
//!
//! A helper's clauses are a disjunction. A clause holds for some arguments when
//! its patterns and guard hold over them and its body is true. A clause whose
//! body raises answers nothing, because an exception in a guard fails the
//! guard. So a call the caller makes in a guard unfolds into the facts of the
//! one clause that can answer true: questions on the caller's subjects, which
//! the dispatch matrix asks and decides by type, plus whatever the clauses
//! state that is not a question, kept as a run-time guard expression.
//!
//! A literal argument is substituted, and every conjunct that is then made of
//! constants alone is evaluated here. A helper that cannot be read this way
//! (two clauses that can answer true, a clause that only a negation could
//! separate from an earlier one, an argument that is not a variable or a
//! literal) stays the embedded plan it has always been.

use super::{
    GuardCallee, PatternDispatchProducer, PatternGuardBinOp, PatternGuardExpr, PatternGuardUnaryOp, PatternResolver,
    SourcePatternError, and_chain, guard_expr_from_ast, intern_prepared_key,
};
use crate::ast::{BinOp, Callee, Expr, Spanned, UnOp, Var};
use crate::dispatch_matrix::{
    ComparisonValue, GroundValue, ListRegion, ProjectionKind, Region, RegionPredicate, RegionQuestion, Subject,
    SubjectId, SubjectSource,
};
use crate::fast_hash::HashMap;

/// Why a conjunction can never hold, which matters only to a caller that
/// negates the answer: `not` of a clause that answered false holds, and `not`
/// of one that raised fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Refusal {
    /// A conjunct is the constant `false`.
    False,
    /// A conjunct raises, which fails the guard.
    Fails,
    /// Some clause refused it and the cause was not kept.
    Either,
}

/// Facts that all hold together: questions on subjects, and the guard
/// expressions that are not questions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Conjunction<TypeHandle> {
    pub(crate) questions: Vec<RegionQuestion<TypeHandle>>,
    pub(crate) residual: Vec<PatternGuardExpr<TypeHandle>>,
    pub(crate) refused: Option<Refusal>,
}

impl<TypeHandle> Default for Conjunction<TypeHandle> {
    fn default() -> Self {
        Self {
            questions: Vec::new(),
            residual: Vec::new(),
            refused: None,
        }
    }
}

impl<TypeHandle: Clone + PartialEq> Conjunction<TypeHandle> {
    pub(crate) fn ask(&mut self, question: RegionQuestion<TypeHandle>) {
        if !self.questions.contains(&question) {
            self.questions.push(question);
        }
    }

    fn refuse(&mut self, why: Refusal) {
        self.refused.get_or_insert(why);
    }

    fn absorb(&mut self, other: Conjunction<TypeHandle>) {
        for question in other.questions {
            self.ask(question);
        }
        self.residual.extend(other.residual);
        if let Some(why) = other.refused {
            self.refuse(why);
        }
    }

    /// Whether it asks nothing and can fail nothing: it holds for any subject.
    fn holds_always(&self) -> bool {
        self.refused.is_none() && self.questions.is_empty() && self.residual.is_empty()
    }

    /// The guard expression the residual amounts to, `false` for a refusal.
    pub(crate) fn guard_expr(self) -> Option<PatternGuardExpr<TypeHandle>> {
        if self.refused.is_some() {
            return Some(PatternGuardExpr::Const(GroundValue::Bool(false)));
        }
        self.residual.into_iter().reduce(|lhs, rhs| PatternGuardExpr::Binary {
            op: PatternGuardBinOp::And,
            lhs: Box::new(lhs),
            rhs: Box::new(rhs),
        })
    }
}

/// What a clause answers once its patterns and guard matched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Answer<TypeHandle> {
    /// The body is true when these facts hold.
    Holds(Conjunction<TypeHandle>),
    /// The body is never true.
    Refused(Refusal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClauseFacts<TypeHandle> {
    /// The patterns, annotations and guard of the clause.
    pub(crate) matches: Conjunction<TypeHandle>,
    pub(crate) answer: Answer<TypeHandle>,
}

/// A helper's clauses as facts over the helper's own subjects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct GuardFacts<TypeHandle> {
    pub(crate) subjects: Vec<Subject>,
    pub(crate) clauses: Vec<ClauseFacts<TypeHandle>>,
}

impl<TypeHandle> GuardFacts<TypeHandle> {
    /// Whether every subject and question can be carried to another matrix:
    /// a bitstring field names other subjects inside its own extraction.
    pub(crate) fn is_portable(&self) -> bool {
        !self.subjects.iter().any(|subject| {
            matches!(
                &subject.source,
                SubjectSource::Projection(projection) if matches!(projection.kind, ProjectionKind::BitstringField(_))
            )
        })
    }

    pub(crate) fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> GuardFacts<MappedHandle> {
        GuardFacts {
            subjects: self.subjects.clone(),
            clauses: self
                .clauses
                .iter()
                .map(|clause| ClauseFacts {
                    matches: clause.matches.map_type_handle(map),
                    answer: match &clause.answer {
                        Answer::Holds(conjunction) => Answer::Holds(conjunction.map_type_handle(map)),
                        Answer::Refused(why) => Answer::Refused(*why),
                    },
                })
                .collect(),
        }
    }
}

impl<TypeHandle> Conjunction<TypeHandle> {
    fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> Conjunction<MappedHandle> {
        Conjunction {
            questions: self.questions.iter().map(|q| q.map_type_handle(map)).collect(),
            residual: self.residual.iter().map(|e| e.map_type_handle(map)).collect(),
            refused: self.refused,
        }
    }
}

/// One argument of a call: a subject of the caller, a literal, or something
/// the facts cannot be carried over.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Arg {
    Subject(SubjectId),
    Const(GroundValue),
    Opaque,
}

/// How a helper's clauses are read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reading {
    /// The call is a conjunct: its facts replace it.
    Replace,
    /// The call is inside a larger expression, which still makes the call.
    /// Only what must hold for the call to answer at all is asked, an
    /// argument that is not a variable asks nothing, and a residual is only
    /// counted, never evaluated or kept.
    Require,
}

/// Whether a conjunct made only of constants is decided on the spot. The
/// conjuncts of a clause body are: `true` adds nothing and `false` answers
/// false. A clause's own written guard is not: it stays the guard it was
/// written as, and only a helper call's body, with its arguments substituted,
/// is evaluated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Literals {
    Decided,
    Kept,
}

/// What a clause or a whole helper amounts to at one call.
enum Resolved<TypeHandle> {
    /// No clause can answer true.
    Never,
    /// Exactly one clause can, when these facts hold.
    Live(Conjunction<TypeHandle>),
}

enum Rebased<TypeHandle> {
    /// The clause cannot match these arguments.
    Never,
    Matches {
        matches: Conjunction<TypeHandle>,
        answer: Answer<TypeHandle>,
    },
}

enum Asked<TypeHandle> {
    Question(RegionQuestion<TypeHandle>),
    Holds,
    Refused,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Evaluated {
    Value(GroundValue),
    Fails,
}

type Bound = HashMap<Var, SubjectId>;

impl<TypeHandle: Clone + PartialEq + Eq> PatternDispatchProducer<TypeHandle> {
    /// The facts of a guard: each conjunct unfolded, asked, or kept as a run-time expression.
    pub(super) fn admit_guard<F: PatternResolver<TypeHandle>>(
        &mut self,
        guard: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
    ) -> Result<Conjunction<TypeHandle>, SourcePatternError> {
        self.admit(guard, bound, resolver, Literals::Kept)
    }

    fn admit<F: PatternResolver<TypeHandle>>(
        &mut self,
        guard: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
        literals: Literals,
    ) -> Result<Conjunction<TypeHandle>, SourcePatternError> {
        let mut admitted = Conjunction::default();
        for conjunct in and_chain(guard) {
            self.admit_conjunct(conjunct, bound, resolver, literals, &mut admitted)?;
            if admitted.refused.is_some() {
                break;
            }
        }
        Ok(admitted)
    }

    fn admit_conjunct<F: PatternResolver<TypeHandle>>(
        &mut self,
        conjunct: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
        literals: Literals,
        admitted: &mut Conjunction<TypeHandle>,
    ) -> Result<(), SourcePatternError> {
        if literals == Literals::Decided {
            match &conjunct.node {
                Expr::Bool(true) => return Ok(()),
                Expr::Bool(false) => {
                    admitted.refuse(Refusal::False);
                    return Ok(());
                }
                _ => {}
            }
        }
        if let Some(unfolded) = self.unfold_call(conjunct, bound, resolver)? {
            admitted.absorb(unfolded);
            return Ok(());
        }
        self.ask_what_its_calls_need(conjunct, bound, resolver, admitted)?;
        let expr = guard_expr_from_ast(
            &conjunct.node,
            bound,
            &self.pinned_by_name,
            &mut self.prepared_keys,
            resolver,
        )?;
        if literals == Literals::Kept {
            admitted.residual.push(expr);
            return Ok(());
        }
        match self.evaluate(&expr, resolver) {
            Some(Evaluated::Value(GroundValue::Bool(true))) => {}
            Some(Evaluated::Value(_)) => admitted.refuse(Refusal::False),
            Some(Evaluated::Fails) => admitted.refuse(Refusal::Fails),
            None => admitted.residual.push(expr),
        }
        Ok(())
    }

    /// What a clause body adds, as the answer of its clause.
    pub(super) fn admit_body<F: PatternResolver<TypeHandle>>(
        &mut self,
        body: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
    ) -> Result<Answer<TypeHandle>, SourcePatternError> {
        let admitted = self.admit(body, bound, resolver, Literals::Decided)?;
        Ok(match admitted.refused {
            Some(why) => Answer::Refused(why),
            None => Answer::Holds(admitted),
        })
    }

    /// The facts a call to a helper stands for, when it is a call whose
    /// arguments are variables or literals and whose helper can be read.
    fn unfold_call<F: PatternResolver<TypeHandle>>(
        &mut self,
        call: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
    ) -> Result<Option<Conjunction<TypeHandle>>, SourcePatternError> {
        let Some((callee, call_args)) = guard_callee_of(call, resolver)? else {
            return Ok(None);
        };
        if callee.always_fails() {
            let mut failing = Conjunction::default();
            failing.refuse(Refusal::Fails);
            return Ok(Some(failing));
        }
        let GuardCallee::Helper(helper) = callee else {
            return Ok(None);
        };
        let args: Vec<Arg> = call_args.iter().map(|arg| arg_of(&arg.node, bound)).collect();
        if args.contains(&Arg::Opaque) {
            return Ok(None);
        }
        if let Some(asked) = domain_at_literals(call, &args, resolver)? {
            return Ok(Some(asked));
        }
        let Some(facts) = helper.facts.as_ref() else {
            return Ok(None);
        };
        Ok(match self.resolve(facts, &args, resolver)? {
            None => None,
            Some(Resolved::Never) => {
                let mut refused = Conjunction::default();
                refused.refuse(Refusal::Either);
                Some(refused)
            }
            Some(Resolved::Live(live)) => Some(live),
        })
    }

    /// What a call must have for it to answer at all, whatever it answers: the
    /// questions every clause that can answer asks. An argument that is not a
    /// variable asks nothing.
    fn what_a_call_needs<F: PatternResolver<TypeHandle>>(
        &mut self,
        call: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
    ) -> Result<Vec<RegionQuestion<TypeHandle>>, SourcePatternError> {
        let Some((GuardCallee::Helper(helper), call_args)) = guard_callee_of(call, resolver)? else {
            return Ok(Vec::new());
        };
        let Some(facts) = helper.facts.as_ref() else {
            return Ok(Vec::new());
        };
        let args: Vec<Arg> = call_args.iter().map(|arg| arg_of(&arg.node, bound)).collect();
        let mut asked_by_each: Option<Vec<RegionQuestion<TypeHandle>>> = None;
        for clause in &facts.clauses {
            let Some(rebased) = self.rebase_clause(facts, clause, &args, Reading::Require, resolver)? else {
                return Ok(Vec::new());
            };
            let Rebased::Matches { matches, answer } = rebased else {
                continue;
            };
            let certain = matches.holds_always();
            let asked = match answer {
                Answer::Refused(Refusal::Fails) => None,
                Answer::Refused(_) => Some(matches.questions),
                Answer::Holds(body) => Some(matches.questions.into_iter().chain(body.questions).collect()),
            };
            if let Some(asked) = asked {
                asked_by_each = Some(match asked_by_each {
                    None => asked,
                    Some(common) => common.into_iter().filter(|question| asked.contains(question)).collect(),
                });
            }
            if certain {
                break;
            }
        }
        Ok(asked_by_each.unwrap_or_default())
    }

    /// The questions each call `expr` is sure to make needs answered for the
    /// call to answer at all. A call under `and` or `or` may not be made, so
    /// it asks nothing.
    fn ask_what_its_calls_need<F: PatternResolver<TypeHandle>>(
        &mut self,
        expr: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
        admitted: &mut Conjunction<TypeHandle>,
    ) -> Result<(), SourcePatternError> {
        let mut pending = vec![expr];
        while let Some(expr) = pending.pop() {
            match &expr.node {
                Expr::BinOp(BinOp::And | BinOp::Or, _, _) => {}
                Expr::BinOp(_, lhs, rhs) => pending.extend([&**lhs, &**rhs]),
                Expr::UnOp(_, arg) | Expr::Ascribe(arg, _) => pending.push(arg),
                Expr::Call(_, args) => {
                    // A call that only aborts reads none of its arguments.
                    if guard_callee_of(expr, resolver)?.is_some_and(|(callee, _)| callee.always_fails()) {
                        continue;
                    }
                    pending.extend(args);
                    for question in self.what_a_call_needs(expr, bound, resolver)? {
                        admitted.ask(question);
                    }
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// The one clause of `facts` that can answer true for `args`, or that none
    /// can. `None` when the clauses cannot be read as one set of facts: more
    /// than one can answer true, or an earlier clause that answers false or
    /// raises may or may not match, which only a negation could separate.
    fn resolve<F: PatternResolver<TypeHandle>>(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        args: &[Arg],
        resolver: &mut F,
    ) -> Result<Option<Resolved<TypeHandle>>, SourcePatternError> {
        let mut live: Option<Conjunction<TypeHandle>> = None;
        let mut an_earlier_may_refuse = false;
        for clause in &facts.clauses {
            let Some(rebased) = self.rebase_clause(facts, clause, args, Reading::Replace, resolver)? else {
                return Ok(None);
            };
            let Rebased::Matches { matches, answer } = rebased else {
                continue;
            };
            let certain = matches.holds_always();
            match answer {
                Answer::Holds(body) => {
                    if live.is_some() || an_earlier_may_refuse {
                        return Ok(None);
                    }
                    let mut whole = matches;
                    whole.absorb(body);
                    live = Some(whole);
                }
                Answer::Refused(_) => an_earlier_may_refuse |= !certain,
            }
            if certain {
                break;
            }
        }
        Ok(Some(live.map_or(Resolved::Never, Resolved::Live)))
    }

    fn rebase_clause<F: PatternResolver<TypeHandle>>(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        clause: &ClauseFacts<TypeHandle>,
        args: &[Arg],
        reading: Reading,
        resolver: &mut F,
    ) -> Result<Option<Rebased<TypeHandle>>, SourcePatternError> {
        if clause.matches.refused.is_some() {
            return Ok(Some(Rebased::Never));
        }
        let Some(matches) = self.rebase_conjunction(facts, &clause.matches, args, reading, resolver)? else {
            return Ok(None);
        };
        let matches = match matches {
            Err(_) => return Ok(Some(Rebased::Never)),
            Ok(matches) => matches,
        };
        let answer = match &clause.answer {
            Answer::Refused(why) => Answer::Refused(*why),
            Answer::Holds(body) => match self.rebase_conjunction(facts, body, args, reading, resolver)? {
                None => return Ok(None),
                Some(Ok(body)) => Answer::Holds(body),
                Some(Err(why)) => Answer::Refused(why),
            },
        };
        Ok(Some(Rebased::Matches { matches, answer }))
    }

    /// One conjunction of a helper, over the call's arguments. `Err` is the
    /// reason it can never hold there.
    fn rebase_conjunction<F: PatternResolver<TypeHandle>>(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        conjunction: &Conjunction<TypeHandle>,
        args: &[Arg],
        reading: Reading,
        resolver: &mut F,
    ) -> Result<Option<Result<Conjunction<TypeHandle>, Refusal>>, SourcePatternError> {
        let mut rebased = Conjunction::default();
        for question in &conjunction.questions {
            match self.rebase_question(facts, args, question, reading, resolver)? {
                None => return Ok(None),
                Some(Asked::Holds) => {}
                Some(Asked::Refused) => return Ok(Some(Err(Refusal::False))),
                Some(Asked::Question(question)) => rebased.ask(question),
            }
        }
        for expr in &conjunction.residual {
            let Some(expr) = self.rebase_expr(facts, args, expr)? else {
                // A requirement reads only whether a residual exists, never
                // what it says, so the stand-in is neither evaluated nor kept.
                if reading == Reading::Require {
                    rebased.residual.push(expr.clone());
                    continue;
                }
                return Ok(None);
            };
            match self.evaluate(&expr, resolver) {
                Some(Evaluated::Value(GroundValue::Bool(true))) => {}
                Some(Evaluated::Value(_)) => return Ok(Some(Err(Refusal::False))),
                Some(Evaluated::Fails) => return Ok(Some(Err(Refusal::Fails))),
                None => rebased.residual.push(expr),
            }
        }
        Ok(Some(Ok(rebased)))
    }

    fn rebase_question<F: PatternResolver<TypeHandle>>(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        args: &[Arg],
        question: &RegionQuestion<TypeHandle>,
        reading: Reading,
        resolver: &mut F,
    ) -> Result<Option<Asked<TypeHandle>>, SourcePatternError> {
        let Some(subject) = self.rebase_subject(facts, args, question.predicate.subject)? else {
            return Ok(None);
        };
        let subject = match subject {
            Arg::Subject(subject) => subject,
            Arg::Const(value) => return Ok(decide_at_constant(&question.predicate.region, &value, resolver)),
            Arg::Opaque => {
                return Ok((reading == Reading::Require).then_some(Asked::Holds));
            }
        };
        let mut rebased = question.clone();
        rebased.predicate = RegionPredicate::new(subject, question.predicate.region.clone());
        for proof in rebased
            .match_evidence
            .proofs
            .iter_mut()
            .chain(&mut rebased.miss_evidence.proofs)
        {
            let Some(Arg::Subject(target)) = self.rebase_subject(facts, args, proof.predicate.subject)? else {
                return Ok(None);
            };
            proof.predicate.subject = target;
        }
        for projected in rebased
            .match_evidence
            .projections
            .iter_mut()
            .chain(&mut rebased.miss_evidence.projections)
        {
            let Some(Arg::Subject(target)) = self.rebase_subject(facts, args, *projected)? else {
                return Ok(None);
            };
            *projected = target;
        }
        match &question.predicate.region {
            Region::Bitstring(_) | Region::Guard(_) | Region::Equal(ComparisonValue::Pinned(_)) => return Ok(None),
            Region::MapKeyPresent {
                key: ComparisonValue::Const(key),
            }
            | Region::Equal(ComparisonValue::Const(key)) => self.prepare_heap_key(key),
            _ => {}
        }
        Ok(Some(Asked::Question(rebased)))
    }

    /// Where a subject of the helper is in the caller.
    fn rebase_subject(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        args: &[Arg],
        subject: SubjectId,
    ) -> Result<Option<Arg>, SourcePatternError> {
        let Some(entry) = facts.subjects.get(subject.0 as usize) else {
            return Ok(None);
        };
        match &entry.source {
            SubjectSource::Input { ordinal } => Ok(args.get(*ordinal as usize).cloned()),
            SubjectSource::Projection(projection) => {
                if matches!(projection.kind, ProjectionKind::BitstringField(_)) {
                    return Ok(None);
                }
                Ok(match self.rebase_subject(facts, args, projection.source)? {
                    Some(Arg::Subject(source)) => {
                        if let ProjectionKind::MapValue {
                            key: ComparisonValue::Const(key),
                        } = &projection.kind
                        {
                            self.prepare_heap_key(key);
                        }
                        Some(Arg::Subject(self.project(source, projection.kind.clone())?))
                    }
                    Some(Arg::Opaque) => Some(Arg::Opaque),
                    Some(Arg::Const(_)) | None => None,
                })
            }
        }
    }

    fn rebase_expr(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        args: &[Arg],
        expr: &PatternGuardExpr<TypeHandle>,
    ) -> Result<Option<PatternGuardExpr<TypeHandle>>, SourcePatternError> {
        Ok(Some(match expr {
            PatternGuardExpr::Const(value) => PatternGuardExpr::Const(value.clone()),
            PatternGuardExpr::Fails => PatternGuardExpr::Fails,
            PatternGuardExpr::Pinned(_) => return Ok(None),
            PatternGuardExpr::Subject(subject) => match self.rebase_subject(facts, args, *subject)? {
                Some(Arg::Subject(subject)) => PatternGuardExpr::Subject(subject),
                Some(Arg::Const(value)) => PatternGuardExpr::Const(value),
                Some(Arg::Opaque) | None => return Ok(None),
            },
            PatternGuardExpr::Unary { op, expr } => {
                let Some(expr) = self.rebase_expr(facts, args, expr)? else {
                    return Ok(None);
                };
                PatternGuardExpr::Unary {
                    op: *op,
                    expr: Box::new(expr),
                }
            }
            PatternGuardExpr::Binary { op, lhs, rhs } => {
                let (Some(lhs), Some(rhs)) = (self.rebase_expr(facts, args, lhs)?, self.rebase_expr(facts, args, rhs)?)
                else {
                    return Ok(None);
                };
                PatternGuardExpr::Binary {
                    op: *op,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                }
            }
            PatternGuardExpr::Dispatch { inputs, dispatch, .. } => {
                let mut rebased = Vec::with_capacity(inputs.len());
                for input in inputs {
                    let Some(input) = self.rebase_expr(facts, args, input)? else {
                        return Ok(None);
                    };
                    rebased.push(input);
                }
                let prepared = dispatch
                    .plan
                    .prepared_keys
                    .iter()
                    .map(|key| intern_prepared_key(&mut self.prepared_keys, key))
                    .collect();
                PatternGuardExpr::Dispatch {
                    inputs: rebased,
                    prepared,
                    dispatch: std::sync::Arc::clone(dispatch),
                }
            }
            PatternGuardExpr::Extern {
                extern_fn,
                args: operands,
            } => {
                let mut rebased = Vec::with_capacity(operands.len());
                for operand in operands {
                    let Some(operand) = self.rebase_expr(facts, args, operand)? else {
                        return Ok(None);
                    };
                    rebased.push(operand);
                }
                PatternGuardExpr::Extern {
                    extern_fn: std::sync::Arc::clone(extern_fn),
                    args: rebased,
                }
            }
        }))
    }

    /// What an expression made of constants alone evaluates to, the way the
    /// guard evaluators would; `None` when it reads anything else.
    fn evaluate<F: PatternResolver<TypeHandle>>(
        &mut self,
        expr: &PatternGuardExpr<TypeHandle>,
        resolver: &mut F,
    ) -> Option<Evaluated> {
        match expr {
            PatternGuardExpr::Const(value) => Some(Evaluated::Value(value.clone())),
            PatternGuardExpr::Fails => Some(Evaluated::Fails),
            PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) | PatternGuardExpr::Extern { .. } => None,
            PatternGuardExpr::Unary {
                op: PatternGuardUnaryOp::Not,
                expr,
            } => match self.evaluate(expr, resolver)? {
                Evaluated::Value(GroundValue::Bool(value)) => Some(Evaluated::Value(GroundValue::Bool(!value))),
                Evaluated::Fails | Evaluated::Value(_) => Some(Evaluated::Fails),
            },
            PatternGuardExpr::Binary { op, lhs, rhs } => self.evaluate_binary(*op, lhs, rhs, resolver),
            PatternGuardExpr::Dispatch { inputs, dispatch, .. } => {
                let facts = dispatch.facts.as_ref()?;
                let mut args = Vec::with_capacity(inputs.len());
                for input in inputs {
                    match self.evaluate(input, resolver)? {
                        Evaluated::Value(value) => args.push(Arg::Const(value)),
                        Evaluated::Fails => return Some(Evaluated::Fails),
                    }
                }
                self.answer_at_constants(facts, &args, resolver)
            }
        }
    }

    fn evaluate_binary<F: PatternResolver<TypeHandle>>(
        &mut self,
        op: PatternGuardBinOp,
        lhs: &PatternGuardExpr<TypeHandle>,
        rhs: &PatternGuardExpr<TypeHandle>,
        resolver: &mut F,
    ) -> Option<Evaluated> {
        let left = self.evaluate(lhs, resolver)?;
        let boolean = |value: &Evaluated| match value {
            Evaluated::Value(GroundValue::Bool(value)) => Some(*value),
            _ => None,
        };
        match (op, &left) {
            (_, Evaluated::Fails) => return Some(Evaluated::Fails),
            (PatternGuardBinOp::And, left) => {
                return match boolean(left) {
                    Some(false) => Some(Evaluated::Value(GroundValue::Bool(false))),
                    Some(true) => {
                        let right = self.evaluate(rhs, resolver)?;
                        Some(
                            boolean(&right)
                                .map_or(Evaluated::Fails, |value| Evaluated::Value(GroundValue::Bool(value))),
                        )
                    }
                    None => Some(Evaluated::Fails),
                };
            }
            (PatternGuardBinOp::Or, left) => {
                return match boolean(left) {
                    Some(true) => Some(Evaluated::Value(GroundValue::Bool(true))),
                    Some(false) => {
                        let right = self.evaluate(rhs, resolver)?;
                        Some(
                            boolean(&right)
                                .map_or(Evaluated::Fails, |value| Evaluated::Value(GroundValue::Bool(value))),
                        )
                    }
                    None => Some(Evaluated::Fails),
                };
            }
            _ => {}
        }
        let Evaluated::Value(left) = left else {
            unreachable!("a failure returned above")
        };
        let Evaluated::Value(right) = self.evaluate(rhs, resolver)? else {
            return Some(Evaluated::Fails);
        };
        let verdict = match (&left, &right) {
            (GroundValue::Int(l), GroundValue::Int(r)) => match op {
                PatternGuardBinOp::Eq => l == r,
                PatternGuardBinOp::Neq => l != r,
                PatternGuardBinOp::Lt => l < r,
                PatternGuardBinOp::LtEq => l <= r,
                PatternGuardBinOp::Gt => l > r,
                PatternGuardBinOp::GtEq => l >= r,
                PatternGuardBinOp::And | PatternGuardBinOp::Or => unreachable!("handled above"),
            },
            (l, r) if l.is_atom() && r.is_atom() => match op {
                PatternGuardBinOp::Eq => atom_name(l) == atom_name(r),
                PatternGuardBinOp::Neq => atom_name(l) != atom_name(r),
                _ => return None,
            },
            _ => return None,
        };
        Some(Evaluated::Value(GroundValue::Bool(verdict)))
    }

    /// What a call to a helper answers when every argument is a constant.
    fn answer_at_constants<F: PatternResolver<TypeHandle>>(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        args: &[Arg],
        resolver: &mut F,
    ) -> Option<Evaluated> {
        for clause in &facts.clauses {
            let Rebased::Matches { matches, answer } = self
                .rebase_clause(facts, clause, args, Reading::Replace, resolver)
                .ok()??
            else {
                continue;
            };
            if !matches.holds_always() {
                return None;
            }
            return match answer {
                Answer::Refused(Refusal::False) => Some(Evaluated::Value(GroundValue::Bool(false))),
                Answer::Refused(Refusal::Fails) => Some(Evaluated::Fails),
                Answer::Refused(Refusal::Either) => None,
                Answer::Holds(body) if body.holds_always() => Some(Evaluated::Value(GroundValue::Bool(true))),
                Answer::Holds(_) => None,
            };
        }
        Some(Evaluated::Fails)
    }
}

/// A guard call's callee and the arguments it was given.
type CalledGuard<'e, TypeHandle> = (GuardCallee<TypeHandle>, &'e [Spanned<Expr>]);

/// The types a helper's guard domain asks of the call's variable arguments,
/// when the helper has a domain at the call's literals. A domain that asks a
/// literal argument something is not read as questions.
fn domain_at_literals<TypeHandle: Clone + PartialEq, F: PatternResolver<TypeHandle>>(
    call: &Spanned<Expr>,
    args: &[Arg],
    resolver: &mut F,
) -> Result<Option<Conjunction<TypeHandle>>, SourcePatternError> {
    let Expr::Call(target, call_args) = &call.node else {
        return Ok(None);
    };
    let Some(callee) = Callee::for_call(&target.node, call_args.len()) else {
        return Ok(None);
    };
    let literals: Vec<Option<GroundValue>> = args
        .iter()
        .map(|arg| match arg {
            Arg::Const(value) => Some(value.clone()),
            _ => None,
        })
        .collect();
    let Some(asked) = resolver.guard_domain(&callee, &literals)? else {
        return Ok(None);
    };
    let mut conjunction = Conjunction::default();
    for (argument, ty) in asked {
        let Arg::Subject(subject) = &args[argument as usize] else {
            return Ok(None);
        };
        conjunction.ask(RegionQuestion::type_region(*subject, ty));
    }
    Ok(Some(conjunction))
}

/// The callee a call in a guard reaches, with the arguments it was given.
fn guard_callee_of<'e, TypeHandle, F: PatternResolver<TypeHandle>>(
    call: &'e Spanned<Expr>,
    resolver: &mut F,
) -> Result<Option<CalledGuard<'e, TypeHandle>>, SourcePatternError> {
    let Expr::Call(target, args) = &call.node else {
        return Ok(None);
    };
    let Some(callee) = Callee::for_call(&target.node, args.len()) else {
        return Ok(None);
    };
    Ok(resolver
        .guard_call(&callee, args.len())?
        .map(|callee| (callee, args.as_slice())))
}

fn atom_name(value: &GroundValue) -> &str {
    match value {
        GroundValue::Atom(name) => name,
        GroundValue::Bool(true) => "true",
        GroundValue::Bool(false) => "false",
        _ => "nil",
    }
}

/// A literal is a value no tuple, list or map is, and the facts that name a
/// type or a constant are decided by the value itself.
fn decide_at_constant<TypeHandle, F: PatternResolver<TypeHandle>>(
    region: &Region<TypeHandle>,
    value: &GroundValue,
    resolver: &mut F,
) -> Option<Asked<TypeHandle>> {
    let verdict = match region {
        Region::Type(ty) => resolver.ground_has_type(value, ty)?,
        Region::Equal(ComparisonValue::Const(constant)) => constant == value,
        Region::TupleArity(_) | Region::MapKind | Region::MapKeyPresent { .. } => false,
        Region::List(ListRegion::Empty | ListRegion::Cons) => false,
        Region::Equal(ComparisonValue::Pinned(_)) | Region::Bitstring(_) | Region::Guard(_) => return None,
    };
    Some(if verdict { Asked::Holds } else { Asked::Refused })
}

/// What a call argument is to the facts.
fn arg_of(expr: &Expr, bound: &Bound) -> Arg {
    match expr {
        Expr::Var(name) => bound.get(name).map_or(Arg::Opaque, |subject| Arg::Subject(*subject)),
        Expr::Int(value) => Arg::Const(GroundValue::Int(*value)),
        Expr::Float(value) => Arg::Const(GroundValue::Float(value.to_bits())),
        Expr::Atom(name) => Arg::Const(GroundValue::Atom(name.clone())),
        Expr::Bool(value) => Arg::Const(GroundValue::Bool(*value)),
        Expr::Nil => Arg::Const(GroundValue::Nil),
        Expr::UnOp(UnOp::Neg, operand) => match &operand.node {
            Expr::Int(value) => value
                .checked_neg()
                .map_or(Arg::Opaque, |value| Arg::Const(GroundValue::Int(value))),
            _ => Arg::Opaque,
        },
        Expr::Ascribe(inner, _) => arg_of(&inner.node, bound),
        _ => Arg::Opaque,
    }
}
