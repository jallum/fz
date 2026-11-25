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
//!
//! Facts that can hold in more than one way are `Alternatives`: an `or` in a
//! guard or in a helper's body, and the `and` of two such, which distributes.
//! Each alternative becomes a row of the caller's matrix that leads to the one
//! clause, so each side of an `or` decides and narrows like a test of its own.
//! The sides are tried in order and an exception in a guard fails the whole
//! guard, so every side but the last must be unable to raise, or its row could
//! be skipped where Elixir stops; an `or` that cannot promise that stays one
//! run-time guard expression.

use super::{
    GuardCallee, PatternDispatchProducer, PatternGuardBinOp, PatternGuardExpr, PatternGuardUnaryOp, PatternResolver,
    SourcePatternError, and_chain, guard_expr_from_ast, intern_prepared_key, or_chain,
};
use crate::ast::{BinOp, Callee, Expr, Spanned, UnOp, Var};
use crate::dispatch_matrix::{
    ComparisonValue, GroundValue, ListRegion, ProjectedProperty, ProjectionKind, Region, RegionPredicate,
    RegionQuestion, Subject, SubjectId, SubjectSource,
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
    /// A helper call these facts came from has no clause for some arguments,
    /// and a call with no clause raises: the facts fail there instead of
    /// answering false.
    pub(crate) partial: bool,
}

impl<TypeHandle> Default for Conjunction<TypeHandle> {
    fn default() -> Self {
        Self {
            questions: Vec::new(),
            residual: Vec::new(),
            refused: None,
            partial: false,
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
        self.partial |= other.partial;
    }

    /// Whether it asks nothing and can fail nothing: it holds for any subject.
    fn holds_always(&self) -> bool {
        self.refused.is_none() && self.questions.is_empty() && self.residual.is_empty() && !self.partial
    }

    /// Whether evaluating it can only answer true or false. Questions are
    /// patterns and annotations, which mismatch and never raise, so what can
    /// raise is a residual expression, a helper call with no clause for some
    /// arguments, and a refusal that is not a plain false.
    pub(crate) fn cannot_raise(&self) -> bool {
        self.residual.is_empty() && !self.partial && matches!(self.refused, None | Some(Refusal::False))
    }

    /// The facts that hold where these do not: one way for each question, which
    /// that question's complement asks (`not (a and b)` is `not a or not b`).
    fn negated(
        &self,
        complement: &mut impl FnMut(&Region<TypeHandle>) -> Option<Region<TypeHandle>>,
    ) -> Option<Alternatives<TypeHandle>> {
        if !self.cannot_raise() {
            return None;
        }
        if self.refused.is_some() {
            return Some(Alternatives::single(Self::default()));
        }
        if self.questions.is_empty() {
            return Some(Alternatives::refused(Refusal::False));
        }
        let ways = self
            .questions
            .iter()
            .map(|question| {
                let region = complement(&question.predicate.region)?;
                let mut way = Self::default();
                way.ask(RegionQuestion::new(RegionPredicate::new(
                    question.predicate.subject,
                    region,
                )));
                Some(way)
            })
            .collect::<Option<Vec<_>>>()?;
        Some(Alternatives::normalized(ways))
    }

    /// These facts asked after `prefix`, the questions it already asks left out.
    pub(crate) fn after(&self, prefix: &[RegionQuestion<TypeHandle>]) -> Self {
        let mut questions = prefix.to_vec();
        for question in &self.questions {
            if !questions.contains(question) {
                questions.push(question.clone());
            }
        }
        Self {
            questions,
            ..self.clone()
        }
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

/// Most ways facts may hold at once. A disjunction with more than one live
/// side is not split into a row for each side: it stays one row, with the
/// disjunction as the guard residue the row still runs. Only a conjunction of
/// single ways, a complement of one, and an `or` with one live side unfold.
const MAX_ALTERNATIVES: usize = 1;

/// Facts that hold when any one of several conjunctions does, tried in order.
/// There is always at least one. A refused alternative is never beside another
/// one: a refusal beside a way to hold says nothing, so only an all-refused
/// set keeps one, with the reason every alternative shared.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Alternatives<TypeHandle> {
    ways: Vec<Conjunction<TypeHandle>>,
}

impl<TypeHandle: Clone + PartialEq> Alternatives<TypeHandle> {
    pub(crate) fn single(way: Conjunction<TypeHandle>) -> Self {
        Self { ways: vec![way] }
    }

    pub(crate) fn refused(why: Refusal) -> Self {
        let mut way = Conjunction::default();
        way.refuse(why);
        Self::single(way)
    }

    /// The alternatives, in the order they are tried.
    pub(crate) fn ways(&self) -> &[Conjunction<TypeHandle>] {
        &self.ways
    }

    fn normalized(ways: Vec<Conjunction<TypeHandle>>) -> Self {
        let mut live: Vec<Conjunction<TypeHandle>> = Vec::new();
        for way in ways.iter().filter(|way| way.refused.is_none()) {
            if !live.contains(way) {
                live.push(way.clone());
            }
        }
        if !live.is_empty() {
            return Self { ways: live };
        }
        let mut reasons = ways.iter().filter_map(|way| way.refused);
        let first = reasons.next().expect("an alternative set is never empty");
        Self::refused(if reasons.all(|why| why == first) {
            first
        } else {
            Refusal::Either
        })
    }

    /// Why none of them can hold, when none can.
    pub(crate) fn refusal(&self) -> Option<Refusal> {
        match self.ways.as_slice() {
            [only] => only.refused,
            _ => None,
        }
    }

    fn holds_always(&self) -> bool {
        self.ways.iter().any(Conjunction::holds_always)
    }

    fn cannot_raise(&self) -> bool {
        self.ways.iter().all(Conjunction::cannot_raise)
    }

    fn made_partial(mut self) -> Self {
        for way in &mut self.ways {
            way.partial = true;
        }
        self
    }

    /// The questions each way asks, which any answer needs asked.
    fn questions_every_way_asks(&self) -> Vec<RegionQuestion<TypeHandle>> {
        let mut ways = self.ways.iter().filter(|way| way.refused.is_none());
        let Some(first) = ways.next() else {
            return Vec::new();
        };
        first
            .questions
            .iter()
            .filter(|question| ways.clone().all(|way| way.questions.contains(question)))
            .cloned()
            .collect()
    }

    pub(crate) fn after(&self, prefix: &[RegionQuestion<TypeHandle>]) -> Self {
        Self {
            ways: self.ways.iter().map(|way| way.after(prefix)).collect(),
        }
    }

    /// Both hold: each way of this one with each way of the other. A way that
    /// is refused already is not added to, as `and` stops at the first false.
    /// `None` when the product is longer than a plan keeps.
    fn and(&self, other: &Self) -> Option<Self> {
        let mut ways = Vec::new();
        for left in &self.ways {
            if left.refused.is_some() {
                ways.push(left.clone());
                continue;
            }
            for right in &other.ways {
                let mut both = left.clone();
                both.absorb(right.clone());
                ways.push(both);
            }
        }
        (ways.len() <= MAX_ALTERNATIVES).then(|| Self::normalized(ways))
    }

    /// None of them hold: the ways, each negated and all of those holding together.
    /// Every way has to be questions that each have a complement, and none may
    /// raise, because `not` of an exception is the exception. `None` otherwise,
    /// or when the product is longer than a plan keeps.
    fn negated(&self, complement: &mut impl FnMut(&Region<TypeHandle>) -> Option<Region<TypeHandle>>) -> Option<Self> {
        let mut none_hold = Self::single(Conjunction::default());
        for way in &self.ways {
            none_hold = none_hold.and(&way.negated(complement)?)?;
        }
        Some(none_hold)
    }

    /// Either holds, the sides tried in order. `None` when an earlier side may
    /// raise, because a row cannot tell an exception that ends the guard from
    /// a false that goes on to the next side, or when the sum is longer than a
    /// plan keeps.
    fn or(sides: Vec<Self>) -> Option<Self> {
        let (last, earlier) = sides.split_last()?;
        if !earlier.iter().all(Self::cannot_raise) {
            return None;
        }
        let ways: Vec<_> = sides.iter().flat_map(|side| side.ways.iter().cloned()).collect();
        let live = ways.iter().filter(|way| way.refused.is_none()).count();
        if live > MAX_ALTERNATIVES {
            return None;
        }
        if live == 0 {
            return Some(last.clone());
        }
        Some(Self::normalized(ways))
    }
}

impl<TypeHandle> Alternatives<TypeHandle> {
    fn map_type_handle<MappedHandle>(
        &self,
        map: &mut impl FnMut(&TypeHandle) -> MappedHandle,
    ) -> Alternatives<MappedHandle> {
        Alternatives {
            ways: self.ways.iter().map(|way| way.map_type_handle(map)).collect(),
        }
    }
}

/// What a clause answers once its patterns and guard matched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Answer<TypeHandle> {
    /// The body is true when these facts hold.
    Holds(Alternatives<TypeHandle>),
    /// The body is never true.
    Refused(Refusal),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClauseFacts<TypeHandle> {
    /// The patterns, annotations and guard of the clause.
    pub(crate) matches: Alternatives<TypeHandle>,
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
            partial: self.partial,
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
    /// Exactly one clause can, when one of these ways holds.
    Live(Alternatives<TypeHandle>),
}

enum Rebased<TypeHandle> {
    /// The clause cannot match these arguments.
    Never,
    Matches {
        matches: Alternatives<TypeHandle>,
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
    /// The facts of a guard: each conjunct unfolded, asked,
    /// or kept as a run-time expression.
    pub(super) fn admit_guard<F: PatternResolver<TypeHandle>>(
        &mut self,
        guard: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
    ) -> Result<Alternatives<TypeHandle>, SourcePatternError> {
        self.admit(guard, bound, resolver, Literals::Kept)
    }

    fn admit<F: PatternResolver<TypeHandle>>(
        &mut self,
        guard: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
        literals: Literals,
    ) -> Result<Alternatives<TypeHandle>, SourcePatternError> {
        let mut admitted = Alternatives::single(Conjunction::default());
        for conjunct in and_chain(guard) {
            let ways = self.admit_conjunct(conjunct, bound, resolver, literals)?;
            admitted = match admitted.and(&ways) {
                Some(both) => both,
                None => {
                    let kept_whole = self.admit_opaque(conjunct, bound, resolver, literals)?;
                    admitted
                        .and(&kept_whole)
                        .expect("a conjunct kept whole is one way, which no product outgrows")
                }
            };
            if admitted.refusal().is_some() {
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
    ) -> Result<Alternatives<TypeHandle>, SourcePatternError> {
        if literals == Literals::Decided {
            match &conjunct.node {
                Expr::Bool(true) => return Ok(Alternatives::single(Conjunction::default())),
                Expr::Bool(false) => return Ok(Alternatives::refused(Refusal::False)),
                _ => {}
            }
        }
        if let Some(split) = self.admit_or(conjunct, bound, resolver, literals)? {
            return Ok(split);
        }
        if let Some(negated) = self.admit_not(conjunct, bound, resolver, literals)? {
            return Ok(negated);
        }
        if let Some(unfolded) = self.unfold_call(conjunct, bound, resolver)? {
            return Ok(unfolded);
        }
        if let Some(projected) = self.admit_projection(conjunct, bound, resolver)? {
            return Ok(projected);
        }
        self.admit_opaque(conjunct, bound, resolver, literals)
    }

    /// A conjunct that compares a projection with a constant, as the one
    /// question it asks of the projected subject. `None` when it is not such a
    /// comparison, and it stays a guard.
    fn admit_projection<F: PatternResolver<TypeHandle>>(
        &mut self,
        conjunct: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
    ) -> Result<Option<Alternatives<TypeHandle>>, SourcePatternError> {
        let Expr::BinOp(BinOp::Eq, lhs, rhs) = &conjunct.node else {
            return Ok(None);
        };
        if !matches!((&lhs.node, &rhs.node), (Expr::Int(_), _) | (_, Expr::Int(_))) {
            return Ok(None);
        }
        let comparison = guard_expr_from_ast(
            &conjunct.node,
            bound,
            &self.pinned_by_name,
            &mut self.prepared_keys,
            resolver,
        )?;
        Ok(self
            .projection_question(&comparison, resolver)?
            .map(Alternatives::single))
    }

    /// The facts of `projection == constant`, either way round, where the
    /// projection reads one property of one subject: that property of the
    /// subject has that size, and whatever the projection needs to answer at all.
    fn projection_question<F: PatternResolver<TypeHandle>>(
        &mut self,
        comparison: &PatternGuardExpr<TypeHandle>,
        resolver: &mut F,
    ) -> Result<Option<Conjunction<TypeHandle>>, SourcePatternError> {
        let PatternGuardExpr::Binary {
            op: PatternGuardBinOp::Eq,
            lhs,
            rhs,
        } = comparison
        else {
            return Ok(None);
        };
        let (read, size) = match (&**lhs, &**rhs) {
            (read, PatternGuardExpr::Const(GroundValue::Int(size)))
            | (PatternGuardExpr::Const(GroundValue::Int(size)), read) => (read, *size),
            _ => return Ok(None),
        };
        let Ok(size) = u32::try_from(size) else {
            return Ok(None);
        };
        let Some((property, subject, mut facts)) = self.projection_read(read, resolver)? else {
            return Ok(None);
        };
        facts.ask(property.question(subject, size));
        Ok(Some(facts))
    }

    /// The property and the subject a call reads, and the facts the call needs
    /// to answer. An extern the library declares `projects:` reads its one
    /// argument; a helper reads what its one clause that can answer returns,
    /// when that is such an extern's call.
    fn projection_read<F: PatternResolver<TypeHandle>>(
        &mut self,
        call: &PatternGuardExpr<TypeHandle>,
        resolver: &mut F,
    ) -> Result<Option<(ProjectedProperty, SubjectId, Conjunction<TypeHandle>)>, SourcePatternError> {
        match call {
            PatternGuardExpr::Extern { extern_fn, args } => Ok(match (extern_fn.projects, args.as_slice()) {
                (Some(property), [PatternGuardExpr::Subject(subject)]) => {
                    Some((property, *subject, Conjunction::default()))
                }
                _ => None,
            }),
            PatternGuardExpr::Dispatch { inputs, dispatch, .. } => {
                let Some(facts) = dispatch.facts.as_ref() else {
                    return Ok(None);
                };
                let Some(args) = inputs.iter().map(arg_of_expr).collect::<Option<Vec<_>>>() else {
                    return Ok(None);
                };
                let Some(Resolved::Live(live)) = self.resolve(facts, &args, resolver)? else {
                    return Ok(None);
                };
                let [way] = live.ways() else {
                    return Ok(None);
                };
                let [PatternGuardExpr::Extern { extern_fn, args }] = way.residual.as_slice() else {
                    return Ok(None);
                };
                let (Some(property), [PatternGuardExpr::Subject(subject)]) = (extern_fn.projects, args.as_slice())
                else {
                    return Ok(None);
                };
                let needs = Conjunction {
                    residual: Vec::new(),
                    ..way.clone()
                };
                Ok(Some((property, *subject, needs)))
            }
            _ => Ok(None),
        }
    }

    /// A conjunct that is `not` of facts whose every question has a
    /// complement, as the facts of those complements. `None` when it is not a
    /// `not` or the operand cannot be negated, and it stays a guard.
    fn admit_not<F: PatternResolver<TypeHandle>>(
        &mut self,
        conjunct: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
        literals: Literals,
    ) -> Result<Option<Alternatives<TypeHandle>>, SourcePatternError> {
        let Expr::UnOp(UnOp::Not, operand) = &conjunct.node else {
            return Ok(None);
        };
        let admitted = self.admit(operand, bound, resolver, literals)?;
        Ok(admitted.negated(&mut |region| resolver.complement(region)))
    }

    /// A conjunct that is an `or` with one live side, as the facts of that
    /// side: each side is admitted as a guard of its own, so it unfolds and asks
    /// as one does. `None` when it is not an `or`, when more than one side is
    /// live, or when a side before the last may raise; it stays one guard.
    fn admit_or<F: PatternResolver<TypeHandle>>(
        &mut self,
        conjunct: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
        literals: Literals,
    ) -> Result<Option<Alternatives<TypeHandle>>, SourcePatternError> {
        if !matches!(conjunct.node, Expr::BinOp(BinOp::Or, _, _)) {
            return Ok(None);
        }
        let sides = or_chain(conjunct);
        let mut admitted = Vec::with_capacity(sides.len());
        for (index, side) in sides.iter().enumerate() {
            let ways = self.admit(side, bound, resolver, literals)?;
            let is_last = index + 1 == sides.len();
            if !is_last && !ways.cannot_raise() {
                return Ok(None);
            }
            admitted.push(ways);
        }
        Ok(Alternatives::or(admitted))
    }

    /// A conjunct as the one way it can be read when nothing in it unfolds:
    /// what its calls need asked, and the expression itself kept to run, or
    /// evaluated on the spot when it is made of constants.
    fn admit_opaque<F: PatternResolver<TypeHandle>>(
        &mut self,
        conjunct: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
        literals: Literals,
    ) -> Result<Alternatives<TypeHandle>, SourcePatternError> {
        let mut admitted = Conjunction::default();
        self.ask_what_its_calls_need(conjunct, bound, resolver, &mut admitted)?;
        let expr = guard_expr_from_ast(
            &conjunct.node,
            bound,
            &self.pinned_by_name,
            &mut self.prepared_keys,
            resolver,
        )?;
        if literals == Literals::Kept {
            admitted.residual.push(expr);
            return Ok(Alternatives::single(admitted));
        }
        match self.evaluate(&expr, resolver) {
            Some(Evaluated::Value(GroundValue::Bool(true))) => {}
            Some(Evaluated::Value(_)) => admitted.refuse(Refusal::False),
            Some(Evaluated::Fails) => admitted.refuse(Refusal::Fails),
            None => admitted.residual.push(expr),
        }
        Ok(Alternatives::single(admitted))
    }

    /// What a clause body adds, as the answer of its clause.
    pub(super) fn admit_body<F: PatternResolver<TypeHandle>>(
        &mut self,
        body: &Spanned<Expr>,
        bound: &Bound,
        resolver: &mut F,
    ) -> Result<Answer<TypeHandle>, SourcePatternError> {
        let admitted = self.admit(body, bound, resolver, Literals::Decided)?;
        Ok(match admitted.refusal() {
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
    ) -> Result<Option<Alternatives<TypeHandle>>, SourcePatternError> {
        let Some((callee, call_args)) = guard_callee_of(call, resolver)? else {
            return Ok(None);
        };
        if callee.always_fails() {
            return Ok(Some(Alternatives::refused(Refusal::Fails)));
        }
        let GuardCallee::Helper(helper) = callee else {
            return Ok(None);
        };
        let args: Vec<Arg> = call_args.iter().map(|arg| arg_of(&arg.node, bound)).collect();
        if args.contains(&Arg::Opaque) {
            return Ok(None);
        }
        let Some(facts) = helper.facts.as_ref() else {
            return Ok(None);
        };
        Ok(match self.resolve(facts, &args, resolver)? {
            None => None,
            Some(Resolved::Never) => Some(Alternatives::refused(Refusal::Either)),
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
                Answer::Refused(_) => Some(matches.questions_every_way_asks()),
                Answer::Holds(body) => Some(
                    matches
                        .questions_every_way_asks()
                        .into_iter()
                        .chain(body.questions_every_way_asks())
                        .collect(),
                ),
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
        let mut live: Option<Alternatives<TypeHandle>> = None;
        let mut an_earlier_may_refuse = false;
        let mut has_a_clause_for_any_arguments = false;
        let mut fails_where_it_does_not_answer = false;
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
                    let Some(whole) = matches.and(&body) else {
                        return Ok(None);
                    };
                    live = Some(whole);
                }
                Answer::Refused(why) => {
                    an_earlier_may_refuse |= !certain;
                    fails_where_it_does_not_answer |= certain && why != Refusal::False;
                }
            }
            if certain {
                has_a_clause_for_any_arguments = true;
                break;
            }
        }
        Ok(Some(live.map_or(Resolved::Never, |live| {
            Resolved::Live(if has_a_clause_for_any_arguments && !fails_where_it_does_not_answer {
                live
            } else {
                live.made_partial()
            })
        })))
    }

    fn rebase_clause<F: PatternResolver<TypeHandle>>(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        clause: &ClauseFacts<TypeHandle>,
        args: &[Arg],
        reading: Reading,
        resolver: &mut F,
    ) -> Result<Option<Rebased<TypeHandle>>, SourcePatternError> {
        if clause.matches.refusal().is_some() {
            return Ok(Some(Rebased::Never));
        }
        let Some(matches) = self.rebase_alternatives(facts, &clause.matches, args, reading, resolver)? else {
            return Ok(None);
        };
        let matches = match matches {
            Err(_) => return Ok(Some(Rebased::Never)),
            Ok(matches) => matches,
        };
        let answer = match &clause.answer {
            Answer::Refused(why) => Answer::Refused(*why),
            Answer::Holds(body) => match self.rebase_alternatives(facts, body, args, reading, resolver)? {
                None => return Ok(None),
                Some(Ok(body)) => Answer::Holds(body),
                Some(Err(why)) => Answer::Refused(why),
            },
        };
        Ok(Some(Rebased::Matches { matches, answer }))
    }

    /// The alternatives of a helper, over the call's arguments: the ones that
    /// can still hold there. `Err` is the reason none can.
    fn rebase_alternatives<F: PatternResolver<TypeHandle>>(
        &mut self,
        facts: &GuardFacts<TypeHandle>,
        alternatives: &Alternatives<TypeHandle>,
        args: &[Arg],
        reading: Reading,
        resolver: &mut F,
    ) -> Result<Option<Result<Alternatives<TypeHandle>, Refusal>>, SourcePatternError> {
        let mut ways = Vec::with_capacity(alternatives.ways().len());
        let mut refusals = Vec::new();
        for way in alternatives.ways() {
            match self.rebase_conjunction(facts, way, args, reading, resolver)? {
                None => return Ok(None),
                Some(Ok(way)) => ways.push(way),
                Some(Err(why)) => refusals.push(why),
            }
        }
        if ways.is_empty() {
            let first = refusals[0];
            return Ok(Some(Err(if refusals.iter().all(|why| *why == first) {
                first
            } else {
                Refusal::Either
            })));
        }
        Ok(Some(Ok(Alternatives::normalized(ways))))
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
        let mut rebased = Conjunction {
            partial: conjunction.partial,
            ..Conjunction::default()
        };
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
                None => match self.projection_question(&expr, resolver)? {
                    Some(asked) => rebased.absorb(asked),
                    None => rebased.residual.push(expr),
                },
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
            Region::Bitstring(_)
            | Region::Guard(_)
            | Region::Equal(ComparisonValue::Pinned(_) | ComparisonValue::Subject(_)) => return Ok(None),
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
        Region::TupleArity(_)
        | Region::Arity(_)
        | Region::MapSize(_)
        | Region::MapKind
        | Region::MapKeyPresent { .. } => false,
        Region::ByteSize(size) => match value {
            GroundValue::Binary(bytes) | GroundValue::Utf8Binary(bytes) => bytes.len() == *size as usize,
            _ => false,
        },
        Region::List(ListRegion::Empty | ListRegion::Cons) => false,
        Region::Equal(ComparisonValue::Pinned(_) | ComparisonValue::Subject(_))
        | Region::Bitstring(_)
        | Region::Guard(_) => {
            return None;
        }
    };
    Some(if verdict { Asked::Holds } else { Asked::Refused })
}

/// What an argument expression already built is to the facts: a subject or a
/// constant, and nothing a guard computed.
fn arg_of_expr<TypeHandle>(expr: &PatternGuardExpr<TypeHandle>) -> Option<Arg> {
    match expr {
        PatternGuardExpr::Subject(subject) => Some(Arg::Subject(*subject)),
        PatternGuardExpr::Const(value) => Some(Arg::Const(value.clone())),
        _ => None,
    }
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
