//! A `defstruct` field list is evaluated only when it computes, and then once.

use std::cell::RefCell;
use std::rc::Rc;

use crate::telemetry::ConfiguredTelemetry;

use super::definition_time::is_evaluator_name;
use super::{CodeSubmission, Compiler2, ExecutableNeed, FunctionId, QuotedSourceRoot, RootSubmission, World};

/// Runs `source`'s `main/0` and gives back its value with how many times a
/// definition-time evaluator ran.
fn run_counting_evaluations(source: &str) -> (i64, usize) {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let expansions = Rc::new(RefCell::new(Vec::<FunctionId>::new()));
    let observed = Rc::clone(&expansions);
    tel.attach_raw_event3::<World, FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("definition_time.fz".into()),
        text: source.into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let value = compiler
        .run_root_interp(root)
        .unwrap_or_else(|failure| panic!("{failure:?}: {:?}", diagnostics.events()));
    let evaluations = expansions
        .borrow()
        .iter()
        .filter(|function| is_evaluator_name(compiler.world().function_ref(**function).name()))
        .count();
    (value, evaluations)
}

#[test]
fn a_computed_field_list_is_evaluated_once_however_many_literals_read_it() {
    let (value, evaluations) = run_counting_evaluations(
        "defmodule Helper do\n def n(), do: 7\nend\n\
         defmodule Tally do\n defstruct count: Helper.n()\nend\n\
         def main(), do: %Tally{}.count + %Tally{}.count + %Tally{count: 1}.count\n",
    );
    assert_eq!(
        value, 15,
        "each literal that omits the field starts from the evaluated default"
    );
    assert_eq!(
        evaluations, 1,
        "the field list runs while its module is defined, not where a literal reads it"
    );
}

#[test]
fn a_field_list_written_as_literals_evaluates_nothing() {
    let (value, evaluations) = run_counting_evaluations(
        "defmodule Tally do\n defstruct [:name, count: 7, seen: {1, [2]}]\nend\n\
         def main(), do: %Tally{}.count + %Tally{}.count\n",
    );
    assert_eq!(value, 14);
    assert_eq!(evaluations, 0, "a written field list is the definition as it stands");
}
