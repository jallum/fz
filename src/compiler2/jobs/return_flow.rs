//! The return-flow companion carried beside an activation's ordinary return
//! type.
//!
//! `evaluate_activation` (in `semantic.rs`) already computes `return_evidence:
//! Option<Ty>` by joining every clause's tail evidence. Alongside that join,
//! it builds a `ReturnFlow` that describes symbolically how the same value
//! was produced. Today every companion built by the walk is `Published` or
//! `Bottom`, so the two views carry the same information in two shapes; a
//! debug assertion at the join proves they agree. The remaining
//! `ReturnExpression` constructors exist for the recursive-return solver
//! that will construct them from a still-unsolved sibling activation.

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
        let expression = match (a.expression, b.expression) {
            (ReturnExpression::Bottom, x) | (x, ReturnExpression::Bottom) => x,
            (x, y) => ReturnExpression::Union(vec![x, y]),
        };
        ReturnFlow { observed, expression }
    }
}

/// A symbolic description of how a return value's type was produced.
/// `Bottom` and `Published` mirror the two states `Option<Ty>` evidence can
/// hold; the rest describe a value's shape one layer at a time, addressing a
/// still-unsolved sibling by `Local`, for a solver that does not run yet.
///
/// `Local`, `Tuple`, `List`, `Map` and `Struct` are exercised by `to_ty`'s
/// tests but not yet built by the walk: the recursive-return solver that
/// constructs them is not wired in, so a plain library build never
/// constructs one. Each carries `#[allow(dead_code)]` for exactly that
/// reason.
#[derive(Debug, Clone)]
pub(super) enum ReturnExpression {
    /// No path has produced a value yet -- the join identity.
    Bottom,
    /// A concrete observed return type.
    Published(Ty),
    /// Another activation's still-unsolved return, addressed by its key.
    #[allow(dead_code)]
    Local(ActivationKey),
    /// The join of several return paths (an `if`, a dispatch, a receive).
    Union(Vec<ReturnExpression>),
    #[allow(dead_code)]
    Tuple(Vec<ReturnExpression>),
    #[allow(dead_code)]
    List(Box<ReturnExpression>),
    #[allow(dead_code)]
    Map(Vec<(MapKey, ReturnExpression)>),
    #[allow(dead_code)]
    Struct(ModuleId, ModuleName, Vec<(MapKey, ReturnExpression)>),
}

impl ReturnExpression {
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
