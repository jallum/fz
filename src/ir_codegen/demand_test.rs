use super::*;

#[test]
fn value_demand_delivers_one_value_lane() {
    let demand = ReturnDemand::value();
    let abi = DemandAbi::from_demand(&demand);
    assert!(abi.delivers_value_lane());
}

#[test]
fn tuple_field_demand_has_no_single_value_lane() {
    let demand = ReturnDemand::tuple_fields(2);
    let abi = DemandAbi::from_demand(&demand);
    assert!(!abi.delivers_value_lane());
}

#[test]
fn continuation_outer_return_collapses_tuple_fields_back_to_one_value_lane() {
    let demand = ReturnDemand::tuple_fields(2);
    let abi = DemandAbi::from_demand(&demand);
    assert!(abi.returned_delivers_value_lane(true));
}
