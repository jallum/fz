//! `DeriveInputDemand` read through the fact it publishes.
//!
//! The demand fact is what activation keying asks before it decides whether a
//! slot's arriving type is meaning or freight, so the statements here are
//! about the demand one body publishes, not about the keys any later job
//! derives from it.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::compiler2::dump::DumpStage;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, FunctionId, InputDemand, RootSubmission};
use crate::dispatch_matrix::demand::DispatchDemand;
use crate::telemetry::ConfiguredTelemetry;

/// Drives one program the way every door does and returns the `InputDemand`
/// each function ended up with, by label.
///
/// The fact is observed through its own telemetry (`input_demand/derived`)
/// rather than reached for in the world, so a re-derivation is visible as the
/// later value and the test reads exactly what a consumer of the fact reads.
fn input_demands(name: &str, source: &str) -> BTreeMap<String, InputDemand> {
    let tel = ConfiguredTelemetry::new();
    let derived: Rc<RefCell<Vec<(FunctionId, InputDemand)>>> = Rc::new(RefCell::new(Vec::new()));
    let sink = Rc::clone(&derived);
    tel.attach_raw_event2::<FunctionId, InputDemand, _>(
        &["fz", "compiler2", "input_demand", "derived"],
        move |_, _, _, function, demand| {
            sink.borrow_mut().push((*function, demand.clone()));
        },
    );

    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("{name} should reach a backend program: {error}"));

    let world = compiler.world();
    derived
        .borrow()
        .iter()
        .map(|(function, demand)| {
            (
                crate::compiler2::canon::function_label(world, *function),
                demand.clone(),
            )
        })
        .collect()
}

fn demand_of(demands: &BTreeMap<String, InputDemand>, label: &str) -> InputDemand {
    demands
        .get(label)
        .unwrap_or_else(|| {
            panic!(
                "{label} should have published an input demand, saw {:?}",
                demands.keys()
            )
        })
        .clone()
}

/// A closure call cannot be answered statically, so every value it touches is
/// a question this body asks: which callable arrived decides which body runs,
/// and that body decides what it makes of the arguments handed to it. Both the
/// called slot and the argument slot therefore carry `Whole` demand, raised
/// where the call is, before any forwarding is joined in.
#[test]
fn a_closure_call_asks_a_whole_question_of_the_callable_and_of_what_it_is_handed() {
    let demands = input_demands(
        "closure call demand",
        "def call2(x, f), do: f.(x)\n\
         def main() do\n  dbg(call2(1, fn (a) -> a + 1 end))\nend\n",
    );

    let call2 = demand_of(&demands, "call2/2");
    assert_eq!(
        call2.forwarded_dispatch,
        vec![DispatchDemand::Whole, DispatchDemand::Whole],
        "calling slot 1 and handing it slot 0 is a question about both slots",
    );
}

/// A body that only TRANSPORTS a value asks nothing of it itself; what it
/// depends on is what the callee it hands the value to asks. The published
/// demand is that callee's, inherited through the forwarding fixpoint with no
/// second walk -- which is why a forwarder's callable slot is asked about here
/// and its brand survives to the callee that calls it.
#[test]
fn a_forwarder_inherits_what_its_callee_asks() {
    let demands = input_demands(
        "forwarded closure call demand",
        "def call2(x, f), do: f.(x)\n\
         def fwd(f, x), do: call2(x, f)\n\
         def main() do\n  dbg(fwd(fn (a) -> a + 1 end, 1))\nend\n",
    );

    let fwd = demand_of(&demands, "fwd/2");
    assert_eq!(
        fwd.forwarded_dispatch,
        vec![DispatchDemand::Whole, DispatchDemand::Whole],
        "both inputs reach call2/2, which calls one and hands it the other",
    );
}
