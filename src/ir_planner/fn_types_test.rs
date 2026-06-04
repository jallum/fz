use super::{ReturnDemand, ReturnStrategy, SpecKey, forwarded_return_contract_for_target, return_contract_for_target};
use crate::fz_ir::FnId;

#[test]
fn non_context_return_contracts_need_no_context_plan() {
    let target = SpecKey::value(FnId(7), Vec::new());
    let contract = return_contract_for_target(target.clone());
    assert_eq!(contract.target, target);
    assert_eq!(contract.strategy, ReturnStrategy::Value);

    let target = SpecKey {
        fn_id: FnId(7),
        input: Vec::new(),
        demand: ReturnDemand::tuple_fields(2),
    };
    let contract = return_contract_for_target(target.clone());
    assert_eq!(contract.target, target);
    assert_eq!(contract.strategy, ReturnStrategy::TupleFields(2));
}

#[test]
fn forwarded_return_contract_pairs_tail_call_target_and_strategy() {
    let target = SpecKey {
        fn_id: FnId(7),
        input: Vec::new(),
        demand: ReturnDemand::tuple_fields(2),
    };
    let contract = forwarded_return_contract_for_target(target.clone());
    assert_eq!(contract.target, target.clone());
    assert_eq!(contract.strategy, ReturnStrategy::ForwardedDemand(target.demand));
}
