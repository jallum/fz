//! What a macro run answers and asks. A macro's `IO.warn` becomes a
//! compile-time warning, reported the same way whether the macro ran or its
//! memoized expansion was reused. A macro that asks the compiler to expand a
//! macro call is answered once and its expansion reused, and a program that
//! is not a macro has no compiler to ask.

use std::cell::RefCell;
use std::rc::Rc;

use fz_runtime::output::{Expansion, OutputSink as _, Warning};

use crate::source::SourceMap;
use crate::telemetry::{Capture, ConfiguredTelemetry};

use super::{ExpansionAnswer, MacroRunOutput, MacroWarning};
use crate::compiler2::quoted_expander::ExpansionContext;
use crate::compiler2::source::QuotedSourceHeap;
use crate::compiler2::{
    CodeSubmission, Compiler2, ExecutableNeed, FunctionId, Job, ModuleId, QuotedSourceRoot, RootSubmission, World,
};

const WARNING_SOURCE: &str = concat!(
    "defmacro careful(x) do\n",
    "  IO.warn(\"first\", __CALLER__)\n",
    "  IO.warn(\"second\")\n",
    "  x\n",
    "end\n",
    "def main(), do: careful(41) + 1\n",
);

/// The messages of every warning diagnostic the capture holds, sorted.
fn warned_messages(diagnostics: &Capture) -> Vec<String> {
    let mut messages: Vec<_> = diagnostics
        .find(&["fz", "diag", "warning"])
        .iter()
        .map(|event| {
            let diagnostic = event
                .diagnostic
                .as_ref()
                .expect("a warning event carries its diagnostic");
            assert_eq!(diagnostic.code.0, "macro/warning");
            diagnostic.message.clone()
        })
        .collect();
    messages.sort();
    messages
}

fn compiler_with_warning_macro() -> (Compiler2<ConfiguredTelemetry>, Capture, Rc<RefCell<Vec<FunctionId>>>) {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let runs = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&runs);
    tel.attach_raw_event3::<World, FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_warning.fz".into()),
        text: WARNING_SOURCE.into(),
    });
    (compiler, diagnostics, runs)
}

#[test]
fn a_macro_that_warns_reports_each_warning_through_the_warning_event() {
    let (mut compiler, diagnostics, _) = compiler_with_warning_macro();
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "compilation continues past a warning"
    );
    assert_eq!(warned_messages(&diagnostics), ["first", "second"]);
}

#[test]
fn a_reused_expansion_reports_the_warnings_of_the_run_that_made_it() {
    let (mut compiler, diagnostics, runs) = compiler_with_warning_macro();
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(42));
    let cold = warned_messages(&diagnostics);
    let careful = compiler.world_mut().reference_function(ModuleId::GLOBAL, "careful", 1);
    let careful_runs = || runs.borrow().iter().filter(|function| **function == careful).count();
    assert_eq!(careful_runs(), 1);

    // A drive starts by forgetting what the last one reported.
    diagnostics.clear();
    compiler.world_mut().clear_reported_warnings();
    let main = compiler.root_function(root);
    compiler.reproduce_job_for_test(Job::ExpandFunctionSource(main), Vec::new());
    compiler.flush_reported_warnings_for_test();
    assert_eq!(careful_runs(), 1, "the second expansion is the memoized one");
    assert_eq!(
        warned_messages(&diagnostics),
        cold,
        "a warm memo reports what a cold run did"
    );
}

#[test]
fn a_macro_run_output_keeps_its_warnings_in_order_and_locates_the_ones_that_name_a_file() {
    let output = MacroRunOutput::default();
    output.warn(&Warning {
        message: b"one",
        file: b"",
        line: 0,
    });
    output.warn(&Warning {
        message: b"two",
        file: b"a.ex",
        line: 3,
    });

    let mut source_map = SourceMap::new();
    let version = source_map.add_code(Some("a.ex"), "zero\none\ntwo\n");
    let call = source_map.line_span(version, 1);
    let warnings = output.into_warnings();
    assert_eq!(warnings.len(), 2);
    let spans: Vec<_> = warnings
        .iter()
        .map(|warning| warning.diagnostic(call, &source_map).primary.span)
        .collect();
    assert_eq!(spans[0], call.unwrap(), "no location points at the call");
    assert_eq!(
        spans[1],
        source_map.line_span(version, 3).unwrap(),
        "a line of the call's file points at it"
    );
}

#[test]
fn a_warning_naming_a_file_the_compiler_has_no_source_for_points_at_the_call_and_names_it() {
    let output = MacroRunOutput::default();
    output.warn(&Warning {
        message: b"elsewhere",
        file: b"other.ex",
        line: 9,
    });
    let mut source_map = SourceMap::new();
    let version = source_map.add_code(Some("a.ex"), "call\n");
    let call = source_map.line_span(version, 1);

    let warning: MacroWarning = output.into_warnings().remove(0);
    let diagnostic = warning.diagnostic(call, &source_map);

    assert_eq!(diagnostic.primary.span, call.unwrap());
    assert_eq!(diagnostic.notes, ["warned at other.ex:9"]);
}

const ASKING_SOURCE: &str = concat!(
    "defmacro inner(x), do: x\n",
    "defmacro outer(x), do: Macro.expand_once(quote(do: inner(unquote(x))), __CALLER__)\n",
    "def main(), do: outer(41) + 1\n",
);

fn asking_compiler() -> (Compiler2<ConfiguredTelemetry>, Rc<RefCell<Vec<FunctionId>>>) {
    let tel = ConfiguredTelemetry::new();
    let runs = Rc::new(RefCell::new(Vec::new()));
    let observed = Rc::clone(&runs);
    tel.attach_raw_event3::<World, FunctionId, QuotedSourceRoot, _>(
        &["fz", "compiler2", "macro", "expanded"],
        move |_, _, _, _, function, _| observed.borrow_mut().push(*function),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_asking.fz".into()),
        text: ASKING_SOURCE.into(),
    });
    (compiler, runs)
}

#[test]
fn a_macro_that_asks_for_a_macro_call_to_expand_runs_each_macro_once_and_a_reused_expansion_runs_none() {
    let (mut compiler, runs) = asking_compiler();
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(42));
    let inner = compiler.world_mut().reference_function(ModuleId::GLOBAL, "inner", 1);
    let outer = compiler.world_mut().reference_function(ModuleId::GLOBAL, "outer", 1);
    let ran = |function| runs.borrow().iter().filter(|ran| **ran == function).count();
    assert_eq!(
        (ran(inner), ran(outer)),
        (1, 1),
        "the question is answered once, not once per replay"
    );

    let main = compiler.root_function(root);
    compiler.reproduce_job_for_test(Job::ExpandFunctionSource(main), Vec::new());
    assert_eq!(
        (ran(inner), ran(outer)),
        (1, 1),
        "a second expansion of the same call reuses both"
    );
}

#[test]
fn a_program_that_is_not_a_macro_has_no_compiler_to_ask_so_expanding_a_macro_call_raises() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("macro_expand_at_run_time.fz".into()),
        text: concat!(
            "def main() do\n",
            "  try do\n",
            "    Macro.expand({:undefined_name, [], [1]}, __ENV__)\n",
            "  rescue\n",
            "    error in RuntimeError -> String.length(error.message)\n",
            "  end\n",
            "end\n",
        )
        .into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok("Macro.expand of a macro call needs the compiler, which only a running macro can ask".len() as i64)
    );
}

#[test]
fn a_run_answers_its_questions_in_the_order_asked_and_stops_at_the_first_it_has_no_answer_for() {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let call = builder.int(1);
    let output = MacroRunOutput::answering(&[ExpansionAnswer::NotAMacro, ExpansionAnswer::Expanded(builder.int(9))]);

    assert_eq!(output.expand(call.raw_word(), 0), Expansion::NotAMacro);
    assert!(
        matches!(output.expand(call.raw_word(), 0), Expansion::Expanded(_)),
        "the second question gets the second answer"
    );
    assert!(output.asked().is_none());

    assert_eq!(output.expand(call.raw_word(), 2), Expansion::Asked);
    let asked = output.asked().expect("the third question had no answer");
    assert_eq!(asked.context, ExpansionContext::Guard);
    assert_eq!(output.expand(call.raw_word(), 1), Expansion::Asked);
    assert_eq!(
        output.asked().expect("still the first").context,
        ExpansionContext::Guard,
        "later questions do not replace the one the compiler answers"
    );
}
