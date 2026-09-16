//! The boxed calling convention is checked from exact caller and wrapper contributions.

use std::collections::BTreeSet;
use std::rc::Rc;

use crate::compiler2::artifact::{
    AbiReadyExecutable, AbiValueRepr, BackendBody, BackendConstructionWrapper, BackendReturnFlow, BackendTail,
    ClosureCallEdge,
};
use crate::compiler2::identity::{ExecutableKey, RootId};
use crate::compiler2::scheduler::FatalError;
use crate::compiler2::semantic::SemanticOrd;
use crate::compiler2::shared_order::SharedOrder;
use crate::compiler2::transport::TransportPosition;
use crate::compiler2::types::Types;
use crate::diag::driver::emit_through;
use crate::diag::{Diagnostic, codes};
use crate::source::Span;
use crate::telemetry::Telemetry;

/// What one boxed closure call in a body reads back from the apply seam: the
/// arity it calls with, and the lanes its destination expects.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct BoxedApplyRequirement {
    pub arity: usize,
    pub delivered: Box<[AbiValueRepr]>,
}

impl BoxedApplyRequirement {
    pub(crate) fn for_body(body: &BackendBody, abi: &AbiReadyExecutable) -> Box<[Self]> {
        let BackendBody::Clauses { entries, .. } = body else {
            return Box::default();
        };
        entries
            .iter()
            .filter_map(|entry| {
                let BackendTail::ClosureCall {
                    edge,
                    args,
                    return_flow,
                    ..
                } = &entry.tail
                else {
                    return None;
                };
                // The call form carries the decision. A direct edge calls its
                // target and never meets the seam, and a dead call reaches
                // nothing at all; only a seam call reads something back from
                // the wrapper.
                if !matches!(edge, ClosureCallEdge::Seam) {
                    return None;
                }
                let delivered = match return_flow {
                    // A delivered or continued result lands in a destination
                    // whose lanes are stated outright.
                    Some(BackendReturnFlow::Deliver { source, .. } | BackendReturnFlow::Continue { source }) => {
                        source.layout.reprs.clone()
                    }
                    // A tail call hands the seam's result straight on to this
                    // body's own caller without touching it, so this body's own
                    // return form is what the seam has to produce. `NoReturn`
                    // and a missing flow lower to the same tail term, so they
                    // read the same way.
                    Some(BackendReturnFlow::Tail | BackendReturnFlow::NoReturn) | None => {
                        abi.return_layout.layout.reprs.clone()
                    }
                };
                Some(Self {
                    arity: args.len(),
                    delivered,
                })
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect()
    }
}

type Callers = SharedOrder<ExecutableKey, ()>;
type Publications = SharedOrder<Rc<TransportPosition>, ()>;

type Lanes = Box<[AbiValueRepr]>;

#[derive(Debug, Clone, Default, PartialEq)]
struct ArityContract {
    callers: SharedOrder<Lanes, Callers>,
    publications: SharedOrder<Lanes, Publications>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Mismatch {
    caller: ExecutableKey,
    delivered: Lanes,
    wrapper: Rc<TransportPosition>,
    published: Lanes,
}

impl ArityContract {
    fn mismatch(&self) -> Option<Mismatch> {
        let mut callers = self.callers.entries();
        let mut publications = self.publications.entries();
        let mut caller = callers.next()?;
        let mut publication = publications.next()?;
        if caller.0 == publication.0 {
            if let Some(other) = callers.next() {
                caller = other;
            } else {
                publication = publications.next()?;
            }
        }
        Some(Mismatch {
            caller: caller.1.entries().next().expect("a lane bucket has a caller").0.clone(),
            delivered: caller.0.clone(),
            wrapper: Rc::clone(
                publication
                    .1
                    .entries()
                    .next()
                    .expect("a lane bucket has a publication")
                    .0,
            ),
            published: publication.0.clone(),
        })
    }
}

#[derive(Debug, Clone, Default, PartialEq)]
pub(crate) struct BoxedContracts {
    arities: SharedOrder<usize, Rc<ArityContract>>,
    mismatches: SharedOrder<usize, Mismatch>,
}

impl BoxedContracts {
    pub(crate) fn replace_caller(
        &mut self,
        key: &ExecutableKey,
        previous: &[BoxedApplyRequirement],
        next: &[BoxedApplyRequirement],
        types: &Types,
    ) {
        if previous == next {
            return;
        }
        for requirement in previous {
            if next.binary_search(requirement).is_err() {
                self.change_caller(key, requirement, false, types);
            }
        }
        for requirement in next {
            if previous.binary_search(requirement).is_err() {
                self.change_caller(key, requirement, true, types);
            }
        }
    }

    fn change_caller(
        &mut self,
        key: &ExecutableKey,
        requirement: &BoxedApplyRequirement,
        present: bool,
        types: &Types,
    ) {
        let mut contract = self
            .arities
            .lookup(&requirement.arity, &usize::cmp)
            .map(|value| value.as_ref().clone())
            .unwrap_or_default();
        let mut owners = contract
            .callers
            .lookup(&requirement.delivered, &Lanes::cmp)
            .cloned()
            .unwrap_or_default();
        if present {
            owners.insert(key.clone(), (), &|left, right| left.semantic_cmp(right, types));
        } else {
            assert!(
                owners
                    .remove(key, &|left, right| left.semantic_cmp(right, types))
                    .is_some(),
                "withdraw an existing caller requirement"
            );
        }
        if owners.is_empty() {
            contract.callers.remove(&requirement.delivered, &Lanes::cmp);
        } else {
            contract
                .callers
                .insert(requirement.delivered.clone(), owners, &Lanes::cmp);
        }
        self.publish(requirement.arity, contract);
    }

    pub(crate) fn replace_wrapper(
        &mut self,
        previous: Option<&BackendConstructionWrapper>,
        next: Option<&BackendConstructionWrapper>,
        types: &Types,
    ) {
        match (previous, next) {
            (None, None) => return,
            (Some(previous), Some(next))
                if previous.call_arity == next.call_arity
                    && previous.return_form == next.return_form
                    && previous.identity == next.identity =>
            {
                return;
            }
            _ => {}
        }
        if let Some(previous) = previous {
            self.change_wrapper(previous, false, types);
        }
        if let Some(next) = next {
            self.change_wrapper(next, true, types);
        }
    }

    fn change_wrapper(&mut self, wrapper: &BackendConstructionWrapper, present: bool, types: &Types) {
        let Some(lanes) = wrapper.return_form.return_reprs() else {
            return;
        };
        let mut contract = self
            .arities
            .lookup(&wrapper.call_arity, &usize::cmp)
            .map(|value| value.as_ref().clone())
            .unwrap_or_default();
        let mut owners = contract
            .publications
            .lookup(&lanes, &Lanes::cmp)
            .cloned()
            .unwrap_or_default();
        if present {
            owners.insert(Rc::new(wrapper.identity.clone()), (), &|left, right| {
                left.semantic_cmp(right, types)
            });
        } else {
            assert!(
                owners
                    .remove(&wrapper.identity, &|left, right| left
                        .semantic_cmp(right.as_ref(), types))
                    .is_some(),
                "withdraw an existing wrapper contribution"
            );
        }
        if owners.is_empty() {
            contract.publications.remove(&lanes, &Lanes::cmp);
        } else {
            contract.publications.insert(lanes, owners, &Lanes::cmp);
        }
        self.publish(wrapper.call_arity, contract);
    }

    fn publish(&mut self, arity: usize, contract: ArityContract) {
        if let Some(mismatch) = contract.mismatch() {
            self.mismatches.insert(arity, mismatch, &usize::cmp);
        } else {
            self.mismatches.remove(&arity, &usize::cmp);
        }
        if contract.callers.is_empty() && contract.publications.is_empty() {
            self.arities.remove(&arity, &usize::cmp);
        } else {
            self.arities.insert(arity, Rc::new(contract), &usize::cmp);
        }
    }

    pub(crate) fn validate(&self, tel: &impl Telemetry, root: RootId) -> Result<(), FatalError> {
        let Some(mismatch) = self.mismatches.first() else {
            return Ok(());
        };
        let diagnostic = Diagnostic::error(
            codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
            format!(
                "compiler2 backend lowering for root {}: boxed closure call in {:?} expects delivered lane(s) {:?} but construction wrapper {:?} it can reach publishes {:?}: the two halves of one calling convention were compiled against different contracts",
                root.as_u32(),
                mismatch.caller.activation.function,
                mismatch.delivered,
                mismatch.wrapper,
                mismatch.published,
            ),
            Span::DUMMY,
        );
        emit_through(tel, std::slice::from_ref(&diagnostic));
        Err(FatalError)
    }
}

#[cfg(test)]
pub(super) mod tests {
    use super::*;
    use crate::compiler2::artifact::BackendCallableReturn;
    use crate::compiler2::transport::{ActivationSymbol, CallableId, ExecutableSymbol};
    use crate::compiler2::{ActivationKey, ExecutableNeed, ModuleId, World};
    use crate::telemetry::ConfiguredTelemetry;

    pub(crate) fn caller(world: &mut World, name: &str) -> ExecutableKey {
        let function = world.reference_function(ModuleId::GLOBAL, name, 0);
        ExecutableKey {
            activation: ActivationKey::from_inputs(RootId::for_test(0), function, &[], world.types_mut()),
            need: ExecutableNeed::Value,
        }
    }

    pub(crate) fn wrapper(
        key: &ExecutableKey,
        arity: usize,
        return_form: BackendCallableReturn,
    ) -> BackendConstructionWrapper {
        BackendConstructionWrapper {
            denotation: key.activation.function.denotation(),
            source_origin: std::sync::Arc::new(fz_runtime::function_denotation::FunctionDenotation::named(
                None,
                "test".into(),
                0,
            )),
            identity: TransportPosition::ExecutableReturn {
                executable: ExecutableSymbol {
                    activation: ActivationSymbol {
                        function: key.activation.function,
                        signature: key.activation.signature.clone(),
                        callable_surfaces: key.activation.callable_surfaces.clone(),
                    },
                    need: key.need,
                },
            },
            callable: CallableId::for_test(0),
            captures: Box::default(),
            call_arity: arity,
            return_form,
            members: Box::default(),
            selection: None,
        }
    }

    #[test]
    fn replacement_and_withdrawal_preserve_mismatch_rejection_and_agreement() {
        let mut world = World::new();
        let key = caller(&mut world, "caller");
        let zero = [BoxedApplyRequirement {
            arity: 1,
            delivered: Box::default(),
        }];
        let one = [BoxedApplyRequirement {
            arity: 1,
            delivered: Box::new([AbiValueRepr::ValueRef]),
        }];
        let absent = wrapper(&key, 1, BackendCallableReturn::Absent);
        let returning = wrapper(&key, 1, BackendCallableReturn::ValueRef);
        let divergent = wrapper(&key, 1, BackendCallableReturn::Diverges);
        let tel = ConfiguredTelemetry::new();
        let mut contracts = BoxedContracts::default();
        contracts.replace_caller(&key, &[], &one, world.types());
        contracts.replace_wrapper(None, Some(&absent), world.types());
        assert!(
            contracts.validate(&tel, RootId::for_test(0)).is_err(),
            "one delivered lane cannot accept an absent wrapper"
        );
        let invalid_snapshot = contracts.clone();
        contracts.replace_wrapper(Some(&absent), Some(&returning), world.types());
        assert!(contracts.validate(&tel, RootId::for_test(0)).is_ok());
        assert!(
            invalid_snapshot.validate(&tel, RootId::for_test(0)).is_err(),
            "an old snapshot retains its original contract"
        );
        contracts.replace_caller(&key, &one, &zero, world.types());
        assert!(
            contracts.validate(&tel, RootId::for_test(0)).is_err(),
            "replacing caller demand must recheck the same arity"
        );
        contracts.replace_wrapper(Some(&returning), Some(&divergent), world.types());
        assert!(
            contracts.validate(&tel, RootId::for_test(0)).is_ok(),
            "a divergent wrapper is not a returning party"
        );
        contracts.replace_wrapper(Some(&divergent), Some(&absent), world.types());
        assert!(
            contracts.validate(&tel, RootId::for_test(0)).is_ok(),
            "zero-lane agreement remains valid"
        );
        contracts.replace_caller(&key, &zero, &[], world.types());
        contracts.replace_wrapper(Some(&absent), None, world.types());
        assert!(contracts.arities.is_empty());
        assert!(
            contracts.mismatches.is_empty(),
            "withdrawal removes the obsolete invariant witness"
        );
    }

    #[test]
    fn matching_first_lane_does_not_hide_another_conflicting_caller_or_wrapper() {
        let mut world = World::new();
        let key = caller(&mut world, "caller");
        let other = caller(&mut world, "other");
        let requirements = [
            BoxedApplyRequirement {
                arity: 1,
                delivered: Box::default(),
            },
            BoxedApplyRequirement {
                arity: 1,
                delivered: Box::new([AbiValueRepr::ValueRef]),
            },
        ];
        let absent = wrapper(&key, 1, BackendCallableReturn::Absent);
        let returning = wrapper(&other, 1, BackendCallableReturn::ValueRef);
        let mut contracts = BoxedContracts::default();
        contracts.replace_caller(&key, &[], &requirements, world.types());
        contracts.replace_wrapper(None, Some(&absent), world.types());
        assert_eq!(
            contracts
                .mismatches
                .first()
                .expect("second caller lane differs")
                .delivered
                .as_ref(),
            [AbiValueRepr::ValueRef]
        );
        contracts.replace_caller(&key, &requirements, &requirements[..1], world.types());
        assert!(contracts.mismatches.is_empty());
        contracts.replace_wrapper(None, Some(&returning), world.types());
        assert_eq!(
            contracts
                .mismatches
                .first()
                .expect("second wrapper lane differs")
                .published
                .as_ref(),
            [AbiValueRepr::ValueRef]
        );
        contracts.replace_wrapper(Some(&returning), None, world.types());
        assert!(contracts.mismatches.is_empty());
    }

    #[test]
    fn wrapper_arity_replacement_checks_only_callers_of_its_current_arity() {
        let mut world = World::new();
        let key = caller(&mut world, "caller");
        let one = [BoxedApplyRequirement {
            arity: 1,
            delivered: Box::new([AbiValueRepr::ValueRef]),
        }];
        let binary = wrapper(&key, 2, BackendCallableReturn::Absent);
        let unary = wrapper(&key, 1, BackendCallableReturn::Absent);
        let mut contracts = BoxedContracts::default();
        contracts.replace_caller(&key, &[], &one, world.types());
        contracts.replace_wrapper(None, Some(&binary), world.types());
        assert!(
            contracts.mismatches.is_empty(),
            "the existing invariant relates only matching call arities"
        );
        contracts.replace_wrapper(Some(&binary), Some(&unary), world.types());
        assert!(contracts.mismatches.lookup(&1, &usize::cmp).is_some());
        assert!(
            contracts.arities.lookup(&2, &usize::cmp).is_none(),
            "replacement withdraws the old publication bucket"
        );
        contracts.replace_wrapper(Some(&unary), Some(&binary), world.types());
        assert!(
            contracts.mismatches.is_empty(),
            "moving the wrapper back removes its old disagreement"
        );
    }

    #[test]
    fn equal_contributions_do_no_work_and_changes_retain_unrelated_arity_allocations() {
        let mut world = World::new();
        let key = caller(&mut world, "caller");
        let other = caller(&mut world, "other");
        let one = [BoxedApplyRequirement {
            arity: 1,
            delivered: Box::new([AbiValueRepr::ValueRef]),
        }];
        let two = [BoxedApplyRequirement {
            arity: 2,
            delivered: Box::new([AbiValueRepr::ValueRef]),
        }];
        let changed = [BoxedApplyRequirement {
            arity: 1,
            delivered: Box::default(),
        }];
        let returning = wrapper(&key, 1, BackendCallableReturn::ValueRef);
        let mut contracts = BoxedContracts::default();
        contracts.replace_caller(&key, &[], &one, world.types());
        contracts.replace_caller(&other, &[], &two, world.types());
        contracts.replace_wrapper(None, Some(&returning), world.types());
        let before = contracts.clone();
        contracts.replace_caller(&key, &one, &one, world.types());
        contracts.replace_wrapper(Some(&returning), Some(&returning), world.types());
        for arity in [1, 2] {
            assert!(
                Rc::ptr_eq(
                    before.arities.lookup(&arity, &usize::cmp).unwrap(),
                    contracts.arities.lookup(&arity, &usize::cmp).unwrap()
                ),
                "equal caller and wrapper contributions retain the existing arity allocation"
            );
        }
        contracts.replace_caller(&key, &one, &changed, world.types());
        assert!(!Rc::ptr_eq(
            before.arities.lookup(&1, &usize::cmp).unwrap(),
            contracts.arities.lookup(&1, &usize::cmp).unwrap()
        ));
        assert!(
            Rc::ptr_eq(
                before.arities.lookup(&2, &usize::cmp).unwrap(),
                contracts.arities.lookup(&2, &usize::cmp).unwrap()
            ),
            "a changed contract never rebuilds an unrelated arity's owners"
        );
        assert!(contracts.mismatches.lookup(&1, &usize::cmp).is_some());
        assert!(before.mismatches.is_empty());
    }

    #[test]
    fn withdrawing_one_owner_keeps_other_owners_and_their_mismatch() {
        let mut world = World::new();
        let key = caller(&mut world, "caller");
        let other = caller(&mut world, "other");
        let one = [BoxedApplyRequirement {
            arity: 1,
            delivered: Box::new([AbiValueRepr::ValueRef]),
        }];
        let absent = wrapper(&key, 1, BackendCallableReturn::Absent);
        let other_absent = wrapper(&other, 1, BackendCallableReturn::Absent);
        let mut contracts = BoxedContracts::default();
        contracts.replace_caller(&key, &[], &one, world.types());
        contracts.replace_caller(&other, &[], &one, world.types());
        contracts.replace_wrapper(None, Some(&absent), world.types());
        contracts.replace_wrapper(None, Some(&other_absent), world.types());
        contracts.replace_caller(&key, &one, &[], world.types());
        contracts.replace_wrapper(Some(&absent), None, world.types());
        let mismatch = contracts
            .mismatches
            .first()
            .expect("other contributions still disagree");
        assert_eq!(mismatch.caller, other);
        assert_eq!(mismatch.wrapper.as_ref(), &other_absent.identity);
        contracts.replace_caller(&other, &one, &[], world.types());
        assert!(
            contracts.mismatches.is_empty(),
            "no caller remains to disagree with the wrapper"
        );
    }
}
