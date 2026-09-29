//! Compiler2's callee-owned function contract facts.
//!
//! A contract is the resolved type surface declared by source. Direct-call
//! resolution applies it to observed arguments before minting callee
//! activations or deriving callable-boundary demand.
//!
//! A contract clause is one interned ADDRESSED ARROW plus its variable bounds
//! (fz-hwn.27.9). The arrow's variables are structural addresses — the resolver
//! assigns them at the binder (fz-hwn.27.14), so two alpha-equivalent contracts
//! intern byte-identical — and the bounds are keyed by those same addresses, so
//! application instantiates the arrow through the bounds sidecar with no bespoke
//! substitution. The hand-rolled witness/substitution walk that used to live here
//! is the Types calculator now (`Types::match_arrow`, `types::arrow_match`,
//! fz-hwn.27.4); contract application is a calculator decision on the arrow.
//! Input-domain projection likewise delegates substitution to
//! `Types::instantiate`, closing dependent bounds to a fixed point while leaving
//! unbounded or cyclic variables polymorphic.

use std::collections::{BTreeSet, HashMap};

use crate::type_expr::ResolvedSpecDecl;

use super::identity::FunctionId;
use super::protocol::ProtocolDomainObligation;
use super::types::{ArrowMatch, Ty, TypeVarId, Types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ResolvedContractArrow {
    decl: ResolvedSpecDecl<Ty>,
    protocol_domain_obligations: BTreeSet<ProtocolDomainObligation>,
}

impl ResolvedContractArrow {
    pub(crate) fn classify(types: &Types, decl: ResolvedSpecDecl<Ty>) -> Self {
        let protocol_domain_obligations = types.protocol_domain_obligations(
            decl.params.iter().copied().chain(std::iter::once(decl.result)),
            &decl.constraints,
        );
        Self {
            decl,
            protocol_domain_obligations,
        }
    }

    #[cfg(test)]
    pub(crate) fn with_obligations(
        decl: ResolvedSpecDecl<Ty>,
        protocol_domain_obligations: BTreeSet<ProtocolDomainObligation>,
    ) -> Self {
        Self {
            decl,
            protocol_domain_obligations,
        }
    }
}

/// One resolved contract clause: the addressed arrow surface and its
/// address-keyed variable bounds. Protocol-domain obligations are classified
/// from the resolved `Ty` marker tags, so current structural enforceability is
/// derived from `protocol_domain_obligations.is_empty()`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractArrow {
    pub arrow: Ty,
    pub bounds: HashMap<TypeVarId, Ty>,
    pub protocol_domain_obligations: BTreeSet<ProtocolDomainObligation>,
    /// A variadic extern's tail: the type every argument past the arrow's
    /// declared parameters must belong to. `None` for an ordinary arrow.
    pub variadic_tail: Option<Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionContract {
    pub arrows: Vec<ContractArrow>,
    /// An extern's wire ABI: how its declared surface crosses into foreign
    /// code. `None` for an ordinary function, which has a lowered body
    /// instead. This is the one resolution of an extern's declared surface;
    /// nothing else derives it a second time.
    pub extern_wire: Option<super::body::LoweredExtern>,
}

/// The contract applied to observed arguments: the instantiated parameter
/// surface of each clause that matched (used to refine the call's inputs), and
/// the joined result. The per-clause result is folded into `result`, so the
/// matched arrows carry only the parameter projection the caller consumes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppliedFunctionContract {
    pub matched_arrows: Vec<Vec<Ty>>,
    pub result: Option<Ty>,
    pub satisfied: bool,
    pub enforceable: bool,
    pub enforceable_satisfied: bool,
}

#[derive(Debug, Default)]
pub struct FunctionContractMap {
    slots: Vec<Option<FunctionContract>>,
}

impl FunctionContract {
    pub fn from_resolved(types: &mut Types, arrows: Vec<ResolvedSpecDecl<Ty>>) -> Self {
        let arrows = arrows
            .into_iter()
            .map(|decl| ResolvedContractArrow::classify(types, decl))
            .collect();
        Self::from_classified_arrows(types, arrows)
    }

    /// A variadic extern's contract: every clause additionally accepts any
    /// number of arguments past its declared parameters, each drawn from
    /// `tail` (`extern_contract::variadic_tail_domain`).
    pub(crate) fn from_resolved_variadic(types: &mut Types, arrows: Vec<ResolvedSpecDecl<Ty>>, tail: Ty) -> Self {
        let arrows = arrows
            .into_iter()
            .map(|decl| ResolvedContractArrow::classify(types, decl))
            .collect();
        Self::from_classified_arrows_with_tail(types, arrows, Some(tail))
    }

    pub(crate) fn from_classified_arrows(types: &mut Types, arrows: Vec<ResolvedContractArrow>) -> Self {
        Self::from_classified_arrows_with_tail(types, arrows, None)
    }

    fn from_classified_arrows_with_tail(
        types: &mut Types,
        arrows: Vec<ResolvedContractArrow>,
        variadic_tail: Option<Ty>,
    ) -> Self {
        Self {
            arrows: arrows
                .into_iter()
                .map(|arrow| ContractArrow {
                    // params/result arrive addressed from the resolver binder
                    // (fz-hwn.27.14), so this packs them into the interned arrow
                    // surface; the bounds are already keyed by those addresses.
                    arrow: types.arrow(&arrow.decl.params, arrow.decl.result),
                    bounds: arrow.decl.constraints,
                    protocol_domain_obligations: arrow.protocol_domain_obligations,
                    variadic_tail,
                })
                .collect(),
            extern_wire: None,
        }
    }

    /// Attaches the wire ABI this contract's own extern declaration resolves
    /// to. The one place that calls this is `derive_function_contract`,
    /// which is also the one place with a declared surface to resolve it
    /// from.
    pub(crate) fn with_extern_wire(mut self, wire: super::body::LoweredExtern) -> Self {
        self.extern_wire = Some(wire);
        self
    }

    pub fn apply(&self, types: &mut Types, arg_tys: &[Ty]) -> AppliedFunctionContract {
        let mut matched_arrows = Vec::new();
        let mut result = None;
        let mut matched_any = false;
        let mut enforceable = false;
        let mut enforceable_matched = false;
        for clause in &self.arrows {
            let clause_enforceable = clause.protocol_domain_obligations.is_empty();
            enforceable |= clause_enforceable;
            let params = clause.matched_params(types, arg_tys.len());
            let clause_result = types
                .arrow_result(&clause.arrow)
                .expect("a contract clause is an arrow with a result slot");
            match types.match_arrow(&params, &clause_result, &clause.bounds, arg_tys) {
                ArrowMatch::Known {
                    params,
                    result: matched,
                } => {
                    result = Some(match result {
                        Some(current) => types.union(current, matched),
                        None => matched,
                    });
                    matched_arrows.push(params);
                    matched_any = true;
                    enforceable_matched |= clause_enforceable;
                }
                ArrowMatch::Underconstrained { params, result: _ } => {
                    matched_arrows.push(params);
                    matched_any = true;
                    enforceable_matched |= clause_enforceable;
                }
                ArrowMatch::Invalid => {}
            }
        }
        if enforceable && !enforceable_matched && self.arrow_set_covers(types, arg_tys) {
            enforceable_matched = true;
            matched_any = true;
            for clause in &self.arrows {
                let Some(narrowed) = clause.narrow_args(types, arg_tys) else {
                    continue;
                };
                let params = types.arrow_params(&clause.arrow);
                let clause_result = types
                    .arrow_result(&clause.arrow)
                    .expect("a contract clause is an arrow with a result slot");
                if let ArrowMatch::Known {
                    params,
                    result: matched,
                } = types.match_arrow(&params, &clause_result, &clause.bounds, &narrowed)
                {
                    result = Some(match result {
                        Some(current) => types.union(current, matched),
                        None => matched,
                    });
                    matched_arrows.push(params);
                }
            }
        }
        AppliedFunctionContract {
            matched_arrows,
            result,
            satisfied: self.arrows.is_empty() || matched_any,
            enforceable,
            enforceable_satisfied: !enforceable || enforceable_matched,
        }
    }

    /// Every clause's domain, rendered for naming what a rejected call of
    /// `row_len` arguments was measured against: one string per clause, in
    /// declaration order. Built from `ContractArrow::matched_params`, the
    /// exact row `apply` widens by the tail and matches the call against, so
    /// the message can never claim a domain the check did not use.
    pub(crate) fn matched_domain_rows(&self, types: &mut Types, row_len: usize) -> Vec<String> {
        self.arrows
            .iter()
            .map(|clause| clause.matched_domain_display(types, row_len))
            .collect()
    }

    /// Arrow-SET coverage of a ground argument row: no single arrow accepted
    /// the arguments, but the arguments may still be covered member-by-member
    /// by different arrows (e.g. `(int | float, int)` against `+/2`'s
    /// `(int, int)` and `(float, int)` clauses). The argument product is a
    /// tuple type and each enforceable ground clause domain is a tuple type,
    /// so coverage is exactly tuple subsumption against the domain union —
    /// the Types calculator decides it set-theoretically, decomposing unions
    /// across positions. Non-ground arguments never reach a violation anyway.
    ///
    /// A clause variable still free after its bounds are closed accepts
    /// anything, so the DOMAIN of a var-carrying clause is that row read at
    /// `any`. Skipping such a row instead would report no coverage where
    /// coverage holds: `pick({integer, a})` and `pick({binary, a})` together
    /// accept every value of `{binary, int} | {int, int}`, member by member,
    /// and a legal program would be diagnosed as a spec violation (fz-kdt.192).
    fn arrow_set_covers(&self, types: &mut Types, arg_tys: &[Ty]) -> bool {
        if arg_tys.iter().any(|ty| types.has_vars(ty)) {
            return false;
        }
        let mut domain: Option<Ty> = None;
        for clause in &self.arrows {
            if !clause.protocol_domain_obligations.is_empty() {
                continue;
            }
            let row = clause.input_domain_row(types);
            if row.len() != arg_tys.len() {
                continue;
            }
            let row = domain_row_at_any(types, row);
            let row_tuple = types.tuple(&row);
            domain = Some(match domain {
                Some(current) => types.union(current, row_tuple),
                None => row_tuple,
            });
        }
        let Some(domain) = domain else {
            return false;
        };
        let observed = types.tuple(arg_tys);
        types.is_subtype(&observed, &domain)
    }
}

impl ContractArrow {
    /// The clause's parameter list, widened to a variadic row: a tail domain
    /// repeats past the declared parameters until the lists are the same
    /// length. A row no longer than the parameters is untouched, so
    /// `match_arrow`'s own arity check still refuses one that is too short.
    fn matched_params(&self, types: &Types, row_len: usize) -> Vec<Ty> {
        let params = types.arrow_params(&self.arrow);
        let Some(tail) = self.variadic_tail else {
            return params;
        };
        if row_len <= params.len() {
            return params;
        }
        let mut widened = params;
        widened.resize(row_len, tail);
        widened
    }

    pub(crate) fn input_domain_row(&self, types: &mut Types) -> Vec<Ty> {
        let params = types.arrow_params(&self.arrow);
        types.clause_domain_row(&params, &self.bounds)
    }

    /// This clause's domain for a call of `row_len` arguments, rendered as a
    /// single readable string: each fixed position named individually, and,
    /// past them, the variadic tail's type named once and marked `...` (the
    /// widened positions all share that one type, so they name nothing new
    /// repeated).
    fn matched_domain_display(&self, types: &mut Types, row_len: usize) -> String {
        let fixed_len = types.arrow_params(&self.arrow).len();
        let widened = self.matched_params(types, row_len);
        let tail = widened.get(fixed_len).copied();
        let mut parts: Vec<String> = widened[..fixed_len.min(widened.len())]
            .iter()
            .map(|ty| types.display_for_diag(ty))
            .collect();
        if let Some(tail) = tail {
            parts.push(format!("...{}", types.display_for_diag(&tail)));
        }
        parts.join(", ")
    }

    /// This clause's own domain row, narrowed against `arg_tys` position by
    /// position; `None` when the clause overlaps no member of the arguments.
    fn narrow_args(&self, types: &mut Types, arg_tys: &[Ty]) -> Option<Vec<Ty>> {
        let params = types.arrow_params(&self.arrow);
        if params.len() != arg_tys.len() {
            return None;
        }
        let domain = types.clause_domain_row(&params, &self.bounds);
        let mut narrowed = Vec::with_capacity(arg_tys.len());
        for (arg, domain) in arg_tys.iter().zip(domain.iter()) {
            let narrowed_col = types.narrow_to_clause_domain(*arg, domain);
            if types.is_empty(&narrowed_col) {
                return None;
            }
            narrowed.push(narrowed_col);
        }
        Some(narrowed)
    }
}

/// One clause domain row read at `any`: a clause variable still free after its
/// bounds are closed accepts anything, so that is what the position admits.
fn domain_row_at_any(types: &mut Types, row: Vec<Ty>) -> Vec<Ty> {
    let any = types.any();
    row.into_iter()
        .map(|param| {
            let free_at_any: HashMap<TypeVarId, Ty> =
                types.free_var_ids(&param).into_iter().map(|var| (var, any)).collect();
            types.instantiate(&param, &free_at_any)
        })
        .collect()
}

impl FunctionContractMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, function: FunctionId, contract: FunctionContract) -> bool {
        self.ensure(function);
        let slot = &mut self.slots[function.as_u32() as usize];
        let changed = slot.as_ref() != Some(&contract);
        *slot = Some(contract);
        changed
    }

    pub fn get(&self, function: FunctionId) -> Option<&FunctionContract> {
        self.slots.get(function.as_u32() as usize)?.as_ref()
    }

    fn ensure(&mut self, function: FunctionId) {
        let index = function.as_u32() as usize;
        if self.slots.len() <= index {
            self.slots.resize_with(index + 1, || None);
        }
    }
}
