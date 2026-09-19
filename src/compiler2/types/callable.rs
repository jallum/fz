//! Exact ground application of a literal-free callable overload set.
//!
//! A funcs-axis DNF clause is one possible callable value. Its positive arrow
//! factors are constraints on that same value, so their domains cover an input
//! row collectively and their returns meet where those domains overlap.

use super::{ArrowSig, Ty, Types};

/// What the callable algebra can prove for one ground input row.
pub(crate) enum CallableApplication {
    /// Every possible callable value covers the row and these are its returns.
    Known(Ty),
    /// A definitely-callable value has no arm set covering the complete row.
    Uncovered,
    /// The value may be callable, but negatives, literals, or free variables
    /// prevent this ground positive-arrow evaluator from proving an answer.
    Opaque,
    /// At least one possible value is provably not callable.
    NotCallable,
}

pub(super) fn return_on_inputs(types: &mut Types, callable: Ty, args: &[Ty]) -> CallableApplication {
    if args.iter().any(|arg| types.has_vars(arg)) {
        return CallableApplication::Opaque;
    }
    // A free alternative may later resolve to a callable. It cannot prove the
    // guaranteed-callability mismatch that a concrete non-callable axis can.
    if types.has_vars(&callable) {
        return CallableApplication::Opaque;
    }
    let descr = types.descr(&callable);
    if !descr.is_pure_callable() {
        return CallableApplication::NotCallable;
    }
    let clauses = descr
        .cases
        .iter()
        .flat_map(|case| case.structure.funcs.iter().cloned())
        .collect::<Vec<_>>();
    if clauses.iter().any(|clause| {
        !clause.neg.is_empty() || clause.pos.is_empty() || clause.pos.iter().any(|arrow| arrow.lit.is_some())
    }) {
        return CallableApplication::Opaque;
    }

    let input = types.tuple(args);
    let mut returned = types.none();
    for clause in clauses {
        let Some(clause_return) = overload_return_on_input(types, input, args.len(), &clause.pos) else {
            return CallableApplication::Uncovered;
        };
        returned = types.union(returned, clause_return);
    }
    CallableApplication::Known(returned)
}

/// One callable value's return over `input`. A recursive partition avoids a
/// fixed-width subset mask: every leaf describes exactly one arm-membership
/// region of the input row.
fn overload_return_on_input(types: &mut Types, input: Ty, arity: usize, arms: &[ArrowSig]) -> Option<Ty> {
    let mut domains = Vec::new();
    let mut returns = Vec::new();
    for arm in arms {
        if arm.args.len() != arity {
            continue;
        }
        domains.push(types.tuple(&arm.args));
        returns.push(arm.ret);
    }
    if domains.is_empty() {
        return None;
    }

    let mut covered = types.none();
    for domain in &domains {
        covered = types.union(covered, *domain);
    }
    if !types.is_subtype(&input, &covered) {
        return None;
    }

    let mut returned = types.none();
    let any = types.any();
    collect_region_returns(types, input, &domains, &returns, 0, false, any, &mut returned);
    Some(returned)
}

fn collect_region_returns(
    types: &mut Types,
    region: Ty,
    domains: &[Ty],
    returns: &[Ty],
    index: usize,
    selected_any: bool,
    selected_return: Ty,
    returned: &mut Ty,
) {
    if types.is_empty(&region) {
        return;
    }
    if index == domains.len() {
        if selected_any {
            *returned = types.union(*returned, selected_return);
        }
        return;
    }

    let outside = types.difference(region, domains[index]);
    collect_region_returns(
        types,
        outside,
        domains,
        returns,
        index + 1,
        selected_any,
        selected_return,
        returned,
    );

    let inside = types.intersect(region, domains[index]);
    let selected_return = types.intersect(selected_return, returns[index]);
    collect_region_returns(
        types,
        inside,
        domains,
        returns,
        index + 1,
        true,
        selected_return,
        returned,
    );
}
