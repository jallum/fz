use super::drive_harness::Drive;
use super::dump::DumpStage;
use super::guard_domain::guard_domain_at;
use super::types::{Ty, Types};
use crate::dispatch_matrix::{DispatchNode, Region, SubjectSource};
use crate::finite_set::FiniteSet;
use crate::ground_value::GroundValue;

const FIXTURE: u32 = 1883;

fn int_arg(value: i64) -> [Option<GroundValue>; 2] {
    [None, Some(GroundValue::Int(value))]
}

/// The arities the run-time test of `ty` admits of a callable.
fn admitted_arities(types: &mut Types, ty: Ty) -> FiniteSet<usize> {
    types.runtime_type_predicate(&ty).callables.arities().clone()
}

/// `is_function(f, n)` in a guard is the question `f :: (any, ..., any -> any)`
/// asks: the entry plan carries one type question on `f`, of an arrow of that
/// arity, and the callable is read for its class alone, so the program builds
/// no construction wrapper for the lambdas it passes.
#[test]
fn a_guard_naming_a_function_arity_asks_f_for_an_arrow_of_that_arity() {
    let mut settled = Drive::fixture(FIXTURE).dump_stage(DumpStage::Backend);
    let foldl = settled.functions().id_in_module("Fold", "foldl", 3);
    let plan = settled.world().entry_dispatch(foldl);

    let mut asked_of_f: Vec<Ty> = Vec::new();
    for node in &plan.graph.nodes {
        let DispatchNode::Test { predicate, .. } = node else {
            continue;
        };
        let Region::Type(ty) = &predicate.region else {
            continue;
        };
        let subject = plan.graph.subject(predicate.subject).expect("a test names a subject");
        if matches!(subject.source, SubjectSource::Input { ordinal: 2 }) {
            asked_of_f.push(*ty);
        }
    }

    let types = settled.compiler_mut().world_mut().types_mut();
    let any = types.any();
    let mut arrows_of_arity = |arity: usize| {
        let arrow = types.arrow(&vec![any; arity], any);
        types.runtime_type_test_envelope(arrow)
    };
    let (binary, unary) = (arrows_of_arity(2), arrows_of_arity(1));
    asked_of_f.sort();
    let mut expected = vec![binary, unary];
    expected.sort();
    assert_eq!(
        asked_of_f, expected,
        "`f` is asked once for an arrow of two arguments and once for one of one argument"
    );
    assert!(
        settled.backend_program().construction_wrappers().is_empty(),
        "a callable that only a type test and a call read needs no construction wrapper"
    );
}

/// The table's entry and `Kernel.is_function/2`'s clauses mean the same thing:
/// `Kernel.is_function(f, n)` run on lambdas of arity 0 to 3 holds exactly
/// where the table's type for `n` admits that arity, and a negative or
/// non-integer arity, which has no entry, raises in the clauses.
#[test]
fn the_table_entry_and_the_kernel_clauses_agree() {
    let mut types = Types::new();
    let mut expected: i64 = 0;
    let mut source = String::from("def probe(f, n), do: if(Kernel.is_function(f, n), do: 1, else: 0)\n");
    source.push_str("def raises(f, n) do\n  try do\n    Kernel.is_function(f, n)\n    0\n  rescue\n    ArgumentError -> 1\n  end\nend\n");
    source.push_str("def main() do\n  0");
    for (bit, (a, n)) in (0..4).flat_map(|a| (0..4).map(move |n| (a, n))).enumerate() {
        let entry = guard_domain_at(&mut types, "Elixir.Kernel", "is_function", &int_arg(n as i64))
            .unwrap_or_else(|| panic!("is_function/2 has a domain at {n}"));
        let [(0, ty)] = entry[..] else {
            panic!("the domain asks one type of the first argument: {entry:?}")
        };
        if admitted_arities(&mut types, ty).contains(&a) {
            expected |= 1 << bit;
        }
        let params = vec!["_"; a].join(", ");
        source.push_str(&format!("\n    + probe(fn {params} -> 0 end, {n}) * {}", 1i64 << bit));
    }
    let outside = [
        ("-1", GroundValue::Int(-1), "negative"),
        (":two", GroundValue::Atom("two".to_string()), "non-integer"),
    ];
    for (offset, (shown, literal, ty)) in outside.into_iter().enumerate() {
        assert_eq!(
            guard_domain_at(&mut types, "Elixir.Kernel", "is_function", &[None, Some(literal)]),
            None,
            "a {ty} arity has no domain"
        );
        let bit = 16 + offset;
        expected |= 1 << bit;
        source.push_str(&format!("\n    + raises(fn -> 0 end, {shown}) * {}", 1i64 << bit));
    }
    source.push_str("\nend\n");

    let mut settled = Drive::source("is_function_clauses.fz", &source).settle();
    let root = settled.root();
    let observed = settled
        .compiler_mut()
        .run_root_interp(root)
        .unwrap_or_else(|failure| panic!("the clause probe runs: {failure:?}"));
    assert_eq!(
        observed, expected,
        "the clauses' answers, bit per (lambda arity, n), then the two raises, are the table's"
    );
}

/// Only `Kernel.is_function/2` has an entry, and only at an integer arity of
/// zero or more.
#[test]
fn a_helper_without_an_entry_or_a_literal_outside_it_has_no_domain() {
    let mut types = Types::new();
    let at = |types: &mut Types, module, name, arguments: &[Option<GroundValue>]| {
        guard_domain_at(types, module, name, arguments)
    };
    assert_eq!(at(&mut types, "Elixir.Kernel", "is_function", &int_arg(-1)), None);
    assert_eq!(at(&mut types, "Elixir.Kernel", "is_function", &[None, None]), None);
    assert_eq!(at(&mut types, "Elixir.Kernel", "is_function", &[None]), None);
    assert_eq!(at(&mut types, "Elixir.Kernel", "is_tuple", &int_arg(2)), None);
    assert_eq!(at(&mut types, "Elixir.Other", "is_function", &int_arg(2)), None);
}
