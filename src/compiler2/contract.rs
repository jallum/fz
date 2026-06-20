//! Compiler2's callee-owned function contract facts.
//!
//! A contract is the resolved type surface declared by source. Direct-call
//! resolution applies it to observed arguments before minting callee
//! activations or deriving callable-boundary demand.
//!
//! Trash markers (fz-hwn.27, The Addressed Arrow): the remaining `Trash*` types
//! (`TrashContractArrow`, `TrashAppliedContractArrow`) are the separable
//! params/result/constraints surface, superseded by the addressed arrow `Ty`
//! plus a bounds sidecar in fz-hwn.27.9. The hand-rolled witness/substitution
//! engine that used to live here was relocated to the Types calculator
//! (`Types::match_arrow`, `types::arrow_match`) in fz-hwn.27.4, so contract
//! application is now a calculator decision rather than a bespoke walk.

use std::collections::HashMap;

use crate::type_expr::ResolvedSpecDecl;

use super::identity::FunctionId;
use super::types::{ArrowMatch, Ty, TypeVarId, Types};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrashContractArrow {
    pub params: Vec<Ty>,
    pub result: Ty,
    pub constraints: HashMap<TypeVarId, Ty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionContract {
    pub arrows: Vec<TrashContractArrow>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TrashAppliedContractArrow {
    pub params: Vec<Ty>,
    pub result: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppliedFunctionContract {
    pub matched_arrows: Vec<TrashAppliedContractArrow>,
    pub result: Option<Ty>,
}

#[derive(Debug, Default)]
pub struct FunctionContractMap {
    slots: Vec<Option<FunctionContract>>,
}

impl FunctionContract {
    pub fn from_resolved(arrows: Vec<ResolvedSpecDecl<Ty>>) -> Self {
        Self {
            arrows: arrows
                .into_iter()
                .map(|arrow| TrashContractArrow {
                    params: arrow.params,
                    result: arrow.result,
                    constraints: arrow.constraints,
                })
                .collect(),
        }
    }

    pub fn apply(&self, types: &mut Types, arg_tys: &[Ty]) -> AppliedFunctionContract {
        let mut matched_arrows = Vec::new();
        let mut result = None;
        for arrow in &self.arrows {
            match types.match_arrow(&arrow.params, &arrow.result, &arrow.constraints, arg_tys) {
                ArrowMatch::Known {
                    params,
                    result: matched,
                } => {
                    result = Some(match result {
                        Some(current) => types.union(current, matched),
                        None => matched,
                    });
                    matched_arrows.push(TrashAppliedContractArrow {
                        params,
                        result: matched,
                    });
                }
                ArrowMatch::Underconstrained {
                    params,
                    result: matched,
                } => {
                    matched_arrows.push(TrashAppliedContractArrow {
                        params,
                        result: matched,
                    });
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
