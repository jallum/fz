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

impl StructuralSurface {
    /// `None` when the clause declares no protocol-domain marker, so the
    /// declared arrow already is its surface.
    fn of(types: &mut Types, arrow: &ResolvedContractArrow) -> Option<Self> {
        if arrow.protocol_domain_obligations.is_empty() {
            return None;
        }
        let params: Vec<Ty> = arrow
            .decl
            .params
            .iter()
            .map(|param| types.structural_surface(*param))
            .collect();
        let bounds = arrow
            .decl
            .constraints
            .iter()
            .map(|(var, bound)| (*var, types.structural_surface(*bound)))
            .collect();
        Some(Self {
            arrow: types.arrow(&params, arrow.decl.result),
            bounds,
        })
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
    /// The arrow read for the values it admits, present only when it differs
    /// from `arrow` (when it declares protocol-domain markers).
    pub structural: Option<StructuralSurface>,
    /// A variadic extern's tail: the type every argument past the arrow's
    /// declared parameters must belong to. `None` for an ordinary arrow.
    pub variadic_tail: Option<Ty>,
}

/// A clause's arrow and bounds with every protocol-domain marker read as
/// `any` (`Types::structural_surface`). Refining a call's inputs reads this,
/// so a marker never reaches a callee as the type of a value; obligations,
/// enforceability and diagnostics keep reading the declared arrow.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuralSurface {
    pub arrow: Ty,
    pub bounds: HashMap<TypeVarId, Ty>,
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
                    structural: StructuralSurface::of(types, &arrow),
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
            let Some(row) = clause.narrowed_row(types, &params, arg_tys) else {
                continue;
            };
            let clause_result = types
                .arrow_result(&clause.arrow)
                .expect("a contract clause is an arrow with a result slot");
            let (matched_params, matched_result) =
                match types.match_arrow(&params, &clause_result, &clause.bounds, &row) {
                    ArrowMatch::Known { params, result } => (params, Some(result)),
                    ArrowMatch::Underconstrained { params, result: _ } => (params, None),
                    ArrowMatch::Invalid => continue,
                };
            if !Self::admits_instantiated_clause(types, arg_tys, &matched_params, self.extern_wire.is_some()) {
                continue;
            }
            if let Some(matched) = matched_result {
                result = Some(match result {
                    Some(current) => types.union(current, matched),
                    None => matched,
                });
            }
            matched_arrows.push(clause.structural_params(types, matched_params, &row));
            matched_any = true;
            enforceable_matched |= clause_enforceable;
        }
        // A column no value inhabits is a call that cannot be made: dead code
        // is never refused, and answers nothing.
        if arg_tys.iter().any(|ty| types.is_empty(ty)) {
            matched_any = true;
            enforceable_matched = true;
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
}

impl ContractArrow {
    /// The clause's parameter list, widened to a variadic row: a tail domain
    /// repeats past the declared parameters until the lists are the same
    /// length. A row no longer than the parameters is untouched, so
    /// `match_arrow`'s own arity check still refuses one that is too short.
    fn matched_params(&self, types: &Types, row_len: usize) -> Vec<Ty> {
        self.widened_to_row(types.arrow_params(&self.arrow), row_len)
    }

    fn widened_to_row(&self, params: Vec<Ty>, row_len: usize) -> Vec<Ty> {
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

    /// The parameters a matched call refines its inputs by: the declared
    /// `params` the call matched, re-matched against the structural surface
    /// when the clause declares protocol-domain markers.
    fn structural_params(&self, types: &mut Types, declared: Vec<Ty>, arg_tys: &[Ty]) -> Vec<Ty> {
        let Some(surface) = &self.structural else {
            return declared;
        };
        let params = self.widened_to_row(types.arrow_params(&surface.arrow), arg_tys.len());
        let result = types
            .arrow_result(&surface.arrow)
            .expect("a contract clause is an arrow with a result slot");
        match types.match_arrow(&params, &result, &surface.bounds, arg_tys) {
            ArrowMatch::Known { params, .. } | ArrowMatch::Underconstrained { params, .. } => params,
            ArrowMatch::Invalid => unreachable!(
                "the structural surface reads every protocol-domain marker as any, so it admits whatever the declared clause matched"
            ),
        }
    }

    #[cfg(test)]
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

    /// The row a call is answered on, or `None` when the call is refused for
    /// this clause. This is the one place a witness is narrowed to a clause's
    /// domain.
    ///
    /// Each column narrows to the clause's domain at every instantiation, so
    /// the walk binds the overlap and judges bounds on it; a column disjoint
    /// from the domain refuses the clause. Whether the part of the call
    /// outside the instantiated clause is let through unnoticed is decided
    /// afterwards, by [`FunctionContract::admits_instantiated_clause`].
    fn narrowed_row(&self, types: &mut Types, params: &[Ty], arg_tys: &[Ty]) -> Option<Vec<Ty>> {
        if params.len() != arg_tys.len() {
            return None;
        }
        let domain = types.clause_domain_at_every_instantiation(params, &self.bounds);
        let mut row = Vec::with_capacity(arg_tys.len());
        for (witness, domain) in arg_tys.iter().zip(domain) {
            let narrowed = types.narrow_to_clause_domain(*witness, domain);
            if types.is_empty(&narrowed) {
                return None;
            }
            row.push(narrowed);
        }
        Some(row)
    }
}

impl FunctionContract {
    /// Whether a value outside the instantiated clause could slip past
    /// unnoticed. `params` are the clause's parameters after the walk bound
    /// its variables, so the judgement is on the clause the call actually
    /// meets.
    ///
    /// - An extern is a raw machine call with no clause tests, so a ground
    ///   column other than `any` must fit its parameter whole. `any` is the
    ///   one imprecise witness: the call site does not know the argument's
    ///   type.
    /// - A function tests its clauses at run time, so a value outside the
    ///   parameter meets the callee's arm of last resort. The tests cannot see
    ///   a brand, so the part of the witness the runtime would let in, its
    ///   overlap with the parameter's runtime reading, must lie inside the
    ///   parameter.
    ///
    /// A witness or parameter still carrying variables is evidence in flight
    /// and passes.
    fn admits_instantiated_clause(types: &mut Types, arg_tys: &[Ty], params: &[Ty], is_extern: bool) -> bool {
        let any = types.any();
        arg_tys.iter().zip(params).all(|(witness, param)| {
            let ground = !types.has_vars(witness) && *witness != any && !types.has_vars(param);
            !ground || Self::column_is_admitted(types, *witness, *param, is_extern)
        })
    }

    fn column_is_admitted(types: &mut Types, witness: Ty, param: Ty, is_extern: bool) -> bool {
        if is_extern {
            return types.is_subtype(&witness, &param);
        }
        let runtime_param = types.runtime_reading(&param);
        if runtime_param == param {
            return true;
        }
        let let_in = types.intersect(witness, runtime_param);
        types.is_subtype(&let_in, &param)
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
