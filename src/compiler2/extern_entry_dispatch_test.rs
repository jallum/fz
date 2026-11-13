//! An extern is a function with one typed clause: a call whose argument is
//! outside a declared parameter's type meets the arm of last resort an
//! ordinary function's mismatch meets, and a call whose arguments are proven
//! asks nothing.

use super::drive_harness::{Drive, EntryDispatchCapture, FunctionCapture, assert_resolved, latest_entry_dispatch};
use super::{CodeSubmission, Compiler2, ExecutableNeed, FunctionId, Job, ModuleId, RootSubmission};
use crate::dispatch_matrix::OutcomeId;
use crate::telemetry::ConfiguredTelemetry;

/// Every spelling a parameter takes in `lib/`, as a declaration in the `C`
/// ABI: scalars, wire-only spellings, handles, a callable, `any`, an
/// unbounded variable and a bounded one.
const PARAMETER_SPELLINGS: &str = r#"
extern "C" defp spell_integer(integer) :: integer
extern "C" defp spell_float(float) :: integer
extern "C" defp spell_boolean(boolean) :: integer
extern "C" defp spell_atom(atom) :: integer
extern "C" defp spell_binary(binary) :: integer
extern "C" defp spell_c_int(c_int) :: integer
extern "C" defp spell_pid(pid) :: integer
extern "C" defp spell_c_pointer(c_pointer) :: integer
extern "C" defp spell_resource(resource(c_pointer)) :: integer
extern "C" defp spell_resource_of(resource(t)) :: integer when t: integer | c_pointer
extern "C" defp spell_callable((c_pointer) -> nil) :: integer
extern "C" defp spell_any(any) :: integer
extern "C" defp spell_free(t) :: integer when t: any
extern "C" defp spell_bounded(t) :: integer when t: integer | c_pointer
extern "C" defp spell_bounded_with_callable(t, (t) -> nil) :: integer when t: integer | c_pointer
def main(), do: 0
"#;

struct Planned {
    functions: FunctionCapture,
    plans: EntryDispatchCapture,
}

fn plan_every_declaration(text: &str) -> Planned {
    let tel = ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    functions.install(&tel);
    let plans = EntryDispatchCapture::new();
    plans.install(&tel);
    let mut compiler = Compiler2::new(tel);
    let owner = compiler.submit_code(CodeSubmission {
        name: Some("fixtures/extern_parameter_spellings.fz".to_string()),
        text: text.to_string(),
    });
    compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_resolved(compiler.drive(), "the declarations are indexed");
    assert!(compiler.demand(Job::ScopeCode(owner)));
    assert_resolved(compiler.drive(), "the declarations are defined");
    for record in functions.all() {
        if record.function_ref.display_name().starts_with("spell_") {
            assert!(compiler.demand(Job::PlanEntryDispatch(record.function_id)));
        }
    }
    assert_resolved(compiler.drive(), "every extern's entry dispatch is planned");
    Planned { functions, plans }
}

impl Planned {
    fn function(&self, name: &str, arity: u64) -> FunctionId {
        self.functions.id(name, arity)
    }

    fn type_tests(&self, name: &str, arity: u64) -> usize {
        latest_entry_dispatch(&self.plans, self.function(name, arity))
            .graph
            .test_count()
    }
}

#[test]
fn every_parameter_spelling_a_library_extern_uses_has_a_runtime_test() {
    let planned = plan_every_declaration(PARAMETER_SPELLINGS);
    for (name, parameters) in [
        ("spell_integer", 1),
        ("spell_float", 1),
        ("spell_boolean", 1),
        ("spell_atom", 1),
        ("spell_binary", 1),
        ("spell_c_int", 1),
        ("spell_pid", 1),
        ("spell_c_pointer", 1),
        ("spell_resource", 1),
        ("spell_resource_of", 1),
        ("spell_callable", 1),
        ("spell_bounded", 1),
    ] {
        assert!(
            planned.type_tests(name, parameters) > 0,
            "{name} asks its argument what it is before the call"
        );
    }
}

#[test]
fn a_bounded_variable_is_tested_as_its_bound_and_a_parameter_that_admits_everything_asks_nothing() {
    let planned = plan_every_declaration(PARAMETER_SPELLINGS);
    assert_eq!(
        planned.type_tests("spell_any", 1),
        0,
        "an `any` parameter has no precondition"
    );
    assert_eq!(
        planned.type_tests("spell_free", 1),
        0,
        "an unbounded variable admits every value, so it has no precondition"
    );
    assert!(
        planned.type_tests("spell_bounded", 1) > 0,
        "a variable bounded by `integer | c_pointer` admits only that union"
    );
    assert!(
        planned.type_tests("spell_bounded_with_callable", 2) > 0,
        "the bound applies beside a callable parameter"
    );
}

#[test]
fn an_extern_with_one_outcome_routes_that_body_once() {
    let planned = plan_every_declaration(PARAMETER_SPELLINGS);
    let plan = latest_entry_dispatch(&planned.plans, planned.function("spell_integer", 1));
    assert_eq!(plan.outcomes.len(), 1, "an extern is one clause");
    let dispatch = super::ExecutableDispatch::new(plan, vec![0]);
    assert_eq!(dispatch.clause_index(OutcomeId(0)), Some(0));
    assert_eq!(dispatch.clause_ids().collect::<Vec<_>>(), vec![0]);
}

/// Fixture 01113 calls `fz_op_add_ii` once with literals and once with a
/// received value.
#[test]
fn a_proven_extern_call_has_no_dispatch_and_an_unproven_one_has_one() {
    let settled = Drive::fixture(1113).dump_stage(super::dump::DumpStage::Backend);
    let program = settled.backend_program();
    let add = settled
        .functions()
        .all()
        .into_iter()
        .find(|record| record.module_id == ModuleId::GLOBAL && record.function_ref.is_named("fz_op_add_ii"))
        .expect("the fixture declares fz_op_add_ii in the global namespace")
        .function_id;
    let rows = program
        .executables()
        .iter()
        .filter(|executable| executable.key.activation.function == add)
        .map(|executable| executable.abi.materialized.entry_dispatch.is_some())
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 2, "one executable per row: proven and received");
    assert_eq!(
        rows.iter().filter(|asks| **asks).count(),
        1,
        "only the row that carries an `any` asks anything: {rows:?}"
    );
}

#[test]
fn only_the_unproven_extern_call_compiles_a_tag_test() {
    let settled = Drive::fixture(1113).dump_stage(super::dump::DumpStage::Native);
    let names = settled
        .native_program()
        .module
        .fns
        .iter()
        .map(|function| function.name.clone())
        .collect::<Vec<_>>();
    let add = names
        .iter()
        .filter(|name| name.starts_with("fz_op_add_ii__"))
        .collect::<Vec<_>>();
    assert_eq!(
        add.len(),
        3,
        "the proven row is the call alone; the received row is a dispatch and the call: {names:?}"
    );
    assert_eq!(
        add.iter().filter(|name| name.ends_with("__call")).count(),
        1,
        "one call function sits behind a dispatch: {add:?}"
    );
}
