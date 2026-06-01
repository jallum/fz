use super::{ResolvedSpec, ResolvedSpecSet, SchemeInstantiation, SchemeMatch, instantiate_match};
use crate::types::{ClosureLitInfo, ClosureTarget, ClosureTypes, Ty};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum AppliedSpecArrowStatus {
    Known,
    Underconstrained,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AppliedSpecArrow<R> {
    pub params: Vec<Ty>,
    pub result: Ty,
    pub status: AppliedSpecArrowStatus,
    pub complete: bool,
    pub reads: Vec<R>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SpecApplication<R> {
    pub matched_arrows: Vec<AppliedSpecArrow<R>>,
    pub result: Ty,
    pub complete: bool,
    pub reads: Vec<R>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct SpecUnderconstrainedApplication<R> {
    pub matched_arrows: Vec<AppliedSpecArrow<R>>,
    pub partial_result: Option<Ty>,
    pub complete: bool,
    pub reads: Vec<R>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum SpecApplicationOutcome<R> {
    Known(SpecApplication<R>),
    Underconstrained(SpecUnderconstrainedApplication<R>),
    NoMatch,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CallbackReturnDemand {
    Value,
    TupleFields(usize),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CallbackReturnQuery<'a> {
    pub target: ClosureTarget,
    pub captures: &'a [Ty],
    pub args: &'a [Ty],
    pub demand: CallbackReturnDemand,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CallbackReturnFact<R> {
    Known { result: Ty, read: R, complete: bool },
    Pending { read: R },
}

pub(crate) fn apply_spec_set<T, R, F>(
    t: &mut T,
    spec_set: &ResolvedSpecSet,
    arg_tys: &[Ty],
    mut callback_returns: F,
) -> SpecApplicationOutcome<R>
where
    T: ClosureTypes<Ty = Ty>,
    R: Clone,
    F: FnMut(&mut T, CallbackReturnQuery<'_>) -> Option<CallbackReturnFact<R>>,
{
    let mut known_result = None;
    let mut partial_result = None;
    let mut matched_arrows = Vec::new();
    let mut reads = Vec::new();
    let mut complete = true;

    for spec in &spec_set.arrows {
        let arrow = match apply_spec_arrow(t, spec, arg_tys, &mut callback_returns) {
            ArrowApplication::Matched(arrow) => arrow,
            ArrowApplication::NoMatch => continue,
        };
        complete &= arrow.complete;
        reads.extend(arrow.reads.iter().cloned());
        if arrow.status == AppliedSpecArrowStatus::Known {
            known_result = Some(match known_result {
                Some(prev) => t.union(prev, arrow.result.clone()),
                None => arrow.result.clone(),
            });
        } else {
            complete = false;
        }
        partial_result = Some(match partial_result {
            Some(prev) => t.union(prev, arrow.result.clone()),
            None => arrow.result.clone(),
        });
        matched_arrows.push(arrow);
    }

    if let Some(result) = known_result {
        return SpecApplicationOutcome::Known(SpecApplication {
            matched_arrows,
            result,
            complete,
            reads,
        });
    }

    if !matched_arrows.is_empty() || arg_tys.iter().any(|ty| t.has_vars(ty)) {
        return SpecApplicationOutcome::Underconstrained(SpecUnderconstrainedApplication {
            matched_arrows,
            partial_result,
            complete: false,
            reads,
        });
    }

    SpecApplicationOutcome::NoMatch
}

enum ArrowApplication<R> {
    Matched(AppliedSpecArrow<R>),
    NoMatch,
}

fn apply_spec_arrow<T, R, F>(
    t: &mut T,
    spec: &ResolvedSpec,
    arg_tys: &[Ty],
    callback_returns: &mut F,
) -> ArrowApplication<R>
where
    T: ClosureTypes<Ty = Ty>,
    R: Clone,
    F: FnMut(&mut T, CallbackReturnQuery<'_>) -> Option<CallbackReturnFact<R>>,
{
    let Some(initial) = successful_arrow_match(t, spec, arg_tys) else {
        return ArrowApplication::NoMatch;
    };

    let mut witnesses = initial.witnesses;
    let mut complete = true;
    let mut reads = Vec::new();

    for (slot, ((pattern, matched_param), witness)) in spec
        .params
        .iter()
        .zip(initial.matched.params.iter())
        .zip(arg_tys.iter())
        .enumerate()
    {
        let refinement =
            higher_order_refinement(t, pattern, matched_param, witness, callback_returns);
        complete &= refinement.complete;
        reads.extend(refinement.reads);
        if let Some(refined) = refinement.ty {
            witnesses[slot] = t.union(witness.clone(), refined);
        }
    }

    match instantiate_match(t, &spec.params, &spec.result, &spec.constraints, &witnesses) {
        SchemeInstantiation::Known(SchemeMatch { params, result }) => {
            ArrowApplication::Matched(AppliedSpecArrow {
                params,
                result,
                status: AppliedSpecArrowStatus::Known,
                complete,
                reads,
            })
        }
        SchemeInstantiation::Underconstrained(SchemeMatch { params, result }) => {
            let status = if t.has_vars(&result) {
                AppliedSpecArrowStatus::Underconstrained
            } else {
                AppliedSpecArrowStatus::Known
            };
            ArrowApplication::Matched(AppliedSpecArrow {
                params,
                result,
                status,
                complete,
                reads,
            })
        }
        SchemeInstantiation::Invalid => ArrowApplication::NoMatch,
    }
}

struct ArrowMatch {
    matched: SchemeMatch<Ty>,
    witnesses: Vec<Ty>,
}

fn successful_arrow_match<T>(t: &mut T, spec: &ResolvedSpec, arg_tys: &[Ty]) -> Option<ArrowMatch>
where
    T: ClosureTypes<Ty = Ty>,
{
    let direct = instantiate_match(t, &spec.params, &spec.result, &spec.constraints, arg_tys);
    match direct {
        SchemeInstantiation::Known(matched) => {
            return Some(ArrowMatch {
                matched,
                witnesses: arg_tys.to_vec(),
            });
        }
        SchemeInstantiation::Underconstrained(matched) if !t.has_vars(&matched.result) => {
            return Some(ArrowMatch {
                matched,
                witnesses: arg_tys.to_vec(),
            });
        }
        SchemeInstantiation::Underconstrained(matched) => {
            if let Some(overlap) = overlap_arrow_match(t, spec, arg_tys) {
                return Some(overlap);
            }
            return Some(ArrowMatch {
                matched,
                witnesses: arg_tys.to_vec(),
            });
        }
        SchemeInstantiation::Invalid => {}
    }

    overlap_arrow_match(t, spec, arg_tys)
}

fn overlap_arrow_match<T>(t: &mut T, spec: &ResolvedSpec, arg_tys: &[Ty]) -> Option<ArrowMatch>
where
    T: ClosureTypes<Ty = Ty>,
{
    let witnesses = spec_param_overlap_witnesses(t, &spec.params, arg_tys)?;
    match instantiate_match(t, &spec.params, &spec.result, &spec.constraints, &witnesses) {
        SchemeInstantiation::Known(matched) | SchemeInstantiation::Underconstrained(matched) => {
            Some(ArrowMatch { matched, witnesses })
        }
        SchemeInstantiation::Invalid => None,
    }
}

fn spec_param_overlap_witnesses<T>(t: &mut T, params: &[Ty], args: &[Ty]) -> Option<Vec<Ty>>
where
    T: ClosureTypes<Ty = Ty>,
{
    if params.len() != args.len() {
        return None;
    }
    let mut witnesses = Vec::with_capacity(params.len());
    for (param, arg) in params.iter().zip(args) {
        let meet = t.intersect(param.clone(), arg.clone());
        if t.is_empty(&meet) {
            return None;
        }
        witnesses.push(meet);
    }
    Some(witnesses)
}

struct HigherOrderRefinement<R> {
    ty: Option<Ty>,
    complete: bool,
    reads: Vec<R>,
}

impl<R> HigherOrderRefinement<R> {
    fn empty() -> Self {
        Self {
            ty: None,
            complete: true,
            reads: Vec::new(),
        }
    }
}

fn higher_order_refinement<T, R, F>(
    t: &mut T,
    pattern: &Ty,
    matched_param: &Ty,
    witness: &Ty,
    callback_returns: &mut F,
) -> HigherOrderRefinement<R>
where
    T: ClosureTypes<Ty = Ty>,
    R: Clone,
    F: FnMut(&mut T, CallbackReturnQuery<'_>) -> Option<CallbackReturnFact<R>>,
{
    let Some(pattern_clauses) = t.callable_clauses(pattern) else {
        return HigherOrderRefinement::empty();
    };
    if !pattern_clauses.iter().any(|clause| t.has_vars(&clause.ret)) {
        return HigherOrderRefinement::empty();
    }
    let Some(matched_clauses) = t.callable_clauses(matched_param) else {
        return HigherOrderRefinement::empty();
    };
    let Some(witness_clauses) = t.callable_clauses(witness) else {
        return HigherOrderRefinement::empty();
    };
    let closure_lits = witness_clauses
        .into_iter()
        .filter_map(|clause| clause.closure)
        .collect::<Vec<_>>();
    if closure_lits.is_empty() {
        return HigherOrderRefinement::empty();
    }

    let mut refined = None;
    let mut complete = true;
    let mut reads = Vec::new();
    for matched_clause in matched_clauses {
        let demand = demand_for_callable_result(t, &matched_clause.ret);
        for ClosureLitInfo { target, captures } in &closure_lits {
            let query = CallbackReturnQuery {
                target: *target,
                captures,
                args: &matched_clause.args,
                demand,
            };
            let Some(fact) = callback_returns(t, query) else {
                continue;
            };
            match fact {
                CallbackReturnFact::Known {
                    result,
                    read,
                    complete: fact_complete,
                } => {
                    reads.push(read);
                    complete &= fact_complete;
                    let arrow = t.arrow(&matched_clause.args, result);
                    refined = Some(match refined {
                        Some(prev) => t.union(prev, arrow),
                        None => arrow,
                    });
                }
                CallbackReturnFact::Pending { read } => {
                    reads.push(read);
                    complete = false;
                }
            }
        }
    }

    HigherOrderRefinement {
        ty: refined,
        complete,
        reads,
    }
}

fn demand_for_callable_result<T>(t: &T, result: &Ty) -> CallbackReturnDemand
where
    T: ClosureTypes<Ty = Ty>,
{
    let arity = t.max_tuple_arity(result);
    if arity > 0 {
        CallbackReturnDemand::TupleFields(arity)
    } else {
        CallbackReturnDemand::Value
    }
}
