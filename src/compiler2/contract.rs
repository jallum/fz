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

use std::collections::HashMap;

use crate::type_expr::ResolvedSpecDecl;

use super::identity::FunctionId;
use super::types::{ArrowMatch, Ty, TypeVarId, Types};

/// One resolved contract clause: the addressed arrow surface and its
/// address-keyed variable bounds.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContractArrow {
    pub arrow: Ty,
    pub bounds: HashMap<TypeVarId, Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionContract {
    pub arrows: Vec<ContractArrow>,
}

/// The contract applied to observed arguments: the instantiated parameter
/// surface of each clause that matched (used to refine the call's inputs), and
/// the joined result. The per-clause result is folded into `result`, so the
/// matched arrows carry only the parameter projection the caller consumes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppliedFunctionContract {
    pub matched_arrows: Vec<Vec<Ty>>,
    pub result: Option<Ty>,
}

#[derive(Debug, Default)]
pub struct FunctionContractMap {
    slots: Vec<Option<FunctionContract>>,
}

impl FunctionContract {
    pub fn from_resolved(types: &mut Types, arrows: Vec<ResolvedSpecDecl<Ty>>) -> Self {
        Self {
            arrows: arrows
                .into_iter()
                .map(|arrow| ContractArrow {
                    // params/result arrive addressed from the resolver binder
                    // (fz-hwn.27.14), so this packs them into the interned arrow
                    // surface; the bounds are already keyed by those addresses.
                    arrow: types.arrow(&arrow.params, arrow.result),
                    bounds: arrow.constraints,
                })
                .collect(),
        }
    }

    pub fn apply(&self, types: &mut Types, arg_tys: &[Ty]) -> AppliedFunctionContract {
        let mut matched_arrows = Vec::new();
        let mut result = None;
        for clause in &self.arrows {
            let params = types.arrow_params(&clause.arrow);
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
                }
                ArrowMatch::Underconstrained { params, result: _ } => {
                    matched_arrows.push(params);
                }
                ArrowMatch::Invalid => {}
            }
        }
        AppliedFunctionContract { matched_arrows, result }
    }
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
