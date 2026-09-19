//! The return-flow companion carried beside an activation's ordinary return
//! type.
//!
//! `evaluate_activation` (in `semantic.rs`) already computes `return_evidence:
//! Option<Ty>` by joining every clause's tail evidence. Alongside that join,
//! it builds a `ReturnFlow` that describes symbolically how the same value
//! was produced: a call resolved to a compiler activation is addressed by
//! `Local(callee key)`, never guessed at as `Bottom` or `Published` merely
//! because that callee's evidence has not arrived yet, and every structural
//! step (tuple/list/map/struct construction, projection, a `Deliver` entry,
//! a capture, a branch/dispatch/receive join) carries its operands'
//! companions through in step with the `Ty` it also builds -- one
//! `ReturnExpression` form per `Types` constructor the walk calls, so a
//! twin function can never build a companion shaped differently from the
//! real value beside it. An operation with no structural rule of its own
//! (arithmetic, a map update) never had one to begin with: its result is
//! `Published` outright, exactly as it always was, independent of whether
//! its operands are still open. A debug assertion at each activation's join
//! proves the two views still agree. The recursive-return solver that will
//! later substitute a settled sibling's expression into a still-open
//! `Local` does not exist yet; until it does, an ordinary (non-component)
//! activation lowers its own `Local` references from `walk_member_map`
//! (in `semantic.rs`) -- the exact value this walk's own calls observed,
//! not `World`'s published `ReturnType`, which only widens round over
//! round and is strictly wider than what one walk ever consumed.

use std::collections::HashMap;

use super::super::identity::{ActivationKey, ModuleId};
use super::super::types::{MapKey, Ty, Types};
use crate::modules::identity::ModuleName;

/// A return type and the symbolic expression that produced it, kept in
/// lock-step. `observed` is the ordinary evidence exactly as
/// `join_evidence` always computed it; `expression` is `to_ty`'s source.
#[derive(Debug, Clone)]
pub(super) struct ReturnFlow {
    pub(super) observed: Option<Ty>,
    pub(super) expression: ReturnExpression,
}

impl ReturnFlow {
    /// The join identity: no path has produced a value yet.
    pub(super) fn bottom() -> Self {
        Self {
            observed: None,
            expression: ReturnExpression::Bottom,
        }
    }

    /// A concrete observed return type.
    pub(super) fn published(ty: Ty) -> Self {
        Self {
            observed: Some(ty),
            expression: ReturnExpression::Published(ty),
        }
    }

    /// Join two path results, the companion of `jobs::semantic::join_evidence`.
    /// `Bottom` is the identity; evidence joins by union. The expression
    /// joins the same way, one layer behind -- it is what `to_ty` must
    /// reproduce for the debug assertion at the activation's join to hold.
    /// A separate function from `join_evidence` on purpose: that helper also
    /// merges call-target summaries that carry no companion at all, so this
    /// step only touches the paths that build one.
    pub(super) fn join(types: &mut Types, a: ReturnFlow, b: ReturnFlow) -> ReturnFlow {
        let observed = match (a.observed, b.observed) {
            (None, x) | (x, None) => x,
            (Some(x), Some(y)) if x == y => Some(x),
            (Some(x), Some(y)) => Some(types.union(x, y)),
        };
        let expression = ReturnExpression::union(a.expression, b.expression);
        ReturnFlow { observed, expression }
    }
}

/// A symbolic description of how a return value's type was produced.
/// `Bottom` and `Published` mirror the two states `Option<Ty>` evidence can
/// hold; `Local` addresses a still-unsolved sibling activation by its key,
/// and the rest describe a value's shape one layer at a time, over children
/// that are themselves any of these constructors.
#[derive(Debug, Clone)]
pub(super) enum ReturnExpression {
    /// No path has produced a value yet -- the join identity.
    Bottom,
    /// A concrete observed return type.
    Published(Ty),
    /// Another activation's return, addressed by its key. An ordinary
    /// activation lowers it to the value its own walk observed for that
    /// call (`walk_member_map`); the recursive-return solver will instead
    /// substitute the sibling's settled expression.
    Local(ActivationKey),
    /// The join of several return paths (an `if`, a dispatch, a receive).
    Union(Vec<ReturnExpression>),
    Tuple(Vec<ReturnExpression>),
    /// A possibly-empty list: `Types::list`. Built for a cons onto a tail
    /// that is itself list-shaped, where the result is never provably
    /// non-empty on its own (the tail might be).
    List(Box<ReturnExpression>),
    /// A provably non-empty list: `Types::non_empty_list`. Built for a flat
    /// literal (`[a, b, c]`) or a cons onto a tail with no known list shape
    /// -- in both cases the head alone already proves at least one element.
    NonEmptyList(Box<ReturnExpression>),
    Map(Vec<(MapKey, ReturnExpression)>),
    Struct(ModuleId, ModuleName, Vec<(MapKey, ReturnExpression)>),
}

impl ReturnExpression {
    /// Combine two expressions the way `ReturnFlow::join` combines its two
    /// paths' companions, and the way a structural construction step folds
    /// its children into one uniform-element companion (a list's elements,
    /// several matched protocol targets for one call). `Bottom` is the
    /// identity, so a single real contribution never gets wrapped in a
    /// `Union` of one. A repeated fold over more than two paths (three or
    /// more clauses, three or more dispatch outcomes) calls this pairwise,
    /// left to right; an existing `Union` on either side is the same join
    /// still in progress; flattening into it keeps that fold's result one
    /// flat, stably ordered list instead of a binary tree of one-off pairs.
    /// Type union is associative, so this never changes what `to_ty` lowers
    /// the result to -- only how many `Union` layers wrap it.
    pub(super) fn union(a: ReturnExpression, b: ReturnExpression) -> ReturnExpression {
        match (a, b) {
            (ReturnExpression::Bottom, x) | (x, ReturnExpression::Bottom) => x,
            (ReturnExpression::Union(mut members), ReturnExpression::Union(more)) => {
                members.extend(more);
                ReturnExpression::Union(members)
            }
            (ReturnExpression::Union(mut members), x) => {
                members.push(x);
                ReturnExpression::Union(members)
            }
            (x, ReturnExpression::Union(mut members)) => {
                members.insert(0, x);
                ReturnExpression::Union(members)
            }
            (x, y) => ReturnExpression::Union(vec![x, y]),
        }
    }

    /// Lower this expression to the `Ty` it denotes, using the same
    /// calculator methods the ordinary walk uses to build a `Ty` directly.
    /// `member_map` resolves a `Local` reference to another activation's
    /// already-solved return.
    ///
    /// An unmapped `Local` is a modeling error, not an approximation: this
    /// step never constructs one, so reaching this arm means a caller built
    /// an expression it cannot yet lower, and `any` would hide that rather
    /// than surface it.
    pub(super) fn to_ty(&self, types: &mut Types, member_map: &HashMap<ActivationKey, Ty>) -> Option<Ty> {
        match self {
            ReturnExpression::Bottom => None,
            ReturnExpression::Published(ty) => Some(*ty),
            ReturnExpression::Local(key) => Some(*member_map.get(key).unwrap_or_else(|| {
                panic!(
                    "ReturnExpression::Local({key:?}) has no member_map entry: every Local \
                     reference must resolve to a solved activation return before lowering"
                )
            })),
            ReturnExpression::Union(members) => {
                let mut joined: Option<Ty> = None;
                for member in members {
                    let member_ty = member.to_ty(types, member_map);
                    joined = match (joined, member_ty) {
                        (None, x) | (x, None) => x,
                        (Some(a), Some(b)) if a == b => Some(a),
                        (Some(a), Some(b)) => Some(types.union(a, b)),
                    };
                }
                joined
            }
            ReturnExpression::Tuple(elems) => {
                let elems = elems
                    .iter()
                    .map(|elem| elem.to_ty(types, member_map))
                    .collect::<Option<Vec<_>>>()?;
                Some(types.tuple(&elems))
            }
            ReturnExpression::List(elem) => {
                let elem_ty = elem.to_ty(types, member_map)?;
                Some(types.list(elem_ty))
            }
            ReturnExpression::NonEmptyList(elem) => {
                let elem_ty = elem.to_ty(types, member_map)?;
                Some(types.non_empty_list(elem_ty))
            }
            ReturnExpression::Map(fields) => {
                let fields = fields
                    .iter()
                    .map(|(key, value)| Some((key.clone(), value.to_ty(types, member_map)?)))
                    .collect::<Option<Vec<_>>>()?;
                Some(types.map(&fields))
            }
            ReturnExpression::Struct(module, name, fields) => {
                let fields = fields
                    .iter()
                    .map(|(key, value)| Some((key.clone(), value.to_ty(types, member_map)?)))
                    .collect::<Option<Vec<_>>>()?;
                Some(types.struct_map(*module, name.clone(), &fields))
            }
        }
    }
}

#[cfg(test)]
#[path = "return_flow_test.rs"]
mod return_flow_test;
