use super::*;
use crate::any_value::{
    AnyValueRef, ClosureDenotationId, Stored, ValueKind, closure_addr_from_tagged, closure_capture_set,
    closure_capture_value, map_addr_from_tagged,
};
use crate::exec_ctx::ExecCtx;
use crate::handler_stack::Innermost;
use crate::handler_stack::handler_stack_test::push_template;
use crate::heap::{Schema, SchemaRegistry};
use crate::process::ClosureRef;
use std::cell::RefCell;
use std::rc::Rc;
use std::slice;

fn with_process<R>(f: impl FnOnce(&mut Process) -> R) -> R {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Box::new(Process::new(schemas));
    // A linked module seeds the reserved atom ids first; this bare process does not.
    for reserved in ["nil", "true", "false"] {
        process.node.intern_atom(reserved);
    }
    f(&mut process)
}

/// Registers the struct of the exception `module` with its `fields` and the
/// mark every exception carries, as a program does before it raises one.
fn declare(process: &Process, module: &str, fields: &[&str]) {
    let module = crate::module_name::ModuleName::from_atom_name(module).expect("a module's atom");
    let fields = ["__exception__"].iter().chain(fields).map(|field| field.to_string());
    process
        .heap
        .register_schema(crate::heap::Schema::named_struct(module, fields));
}

fn declare_undefined_call_exceptions(process: &Process) {
    declare(process, "Elixir.ArgumentError", &["message"]);
    declare(
        process,
        "Elixir.UndefinedFunctionError",
        &["module", "function", "arity", "reason", "message"],
    );
}

fn atom(process: &Process, name: &str) -> AnyValue {
    AnyValue::atom(process.node.intern_atom(name))
}

fn binary(process: &mut Process, text: &str) -> AnyValue {
    process.heap.alloc_bitstring(text.as_bytes(), 8 * text.len() as u64)
}

fn map(process: &mut Process, entries: &[(&str, AnyValue)]) -> AnyValue {
    let slots: Vec<_> = entries
        .iter()
        .map(|(key, value)| (atom(process, key), *value))
        .collect();
    let bits = process.heap.alloc_map_slots(&slots);
    let addr = map_addr_from_tagged(bits).expect("map addr");
    AnyValue::from_ref(AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref")).expect("map value")
}

fn exception(process: &mut Process, name: &str, message: &str) -> AnyValue {
    let name = atom(process, name);
    let flag = atom(process, "true");
    let message = binary(process, message);
    map(
        process,
        &[("__struct__", name), ("__exception__", flag), ("message", message)],
    )
}

fn line(process: &mut Process, kind: RaiseKind, value: AnyValue) -> Option<String> {
    failure_line(process, kind, value)
}

/// `fz_panic` called as compiled code calls it: with the value's word and kind.
fn panic_with(process: &mut Process, value: AnyValue) {
    let Stored { word, kind } = Stored::of(value);
    fz_panic(process, word, kind);
}

fn error_line(process: &mut Process, value: AnyValue) -> String {
    line(process, RaiseKind::Error, value).expect("an error always has a line")
}

#[test]
fn an_exception_prints_its_name_and_message() {
    with_process(|process| {
        let value = exception(process, "Elixir.ArgumentError", "bad");
        assert_eq!(error_line(process, value), "** (ArgumentError) bad");
    });
}

#[test]
fn a_value_that_is_not_an_exception_prints_as_an_erlang_error() {
    with_process(|process| {
        let reason = atom(process, "badarg");
        assert_eq!(error_line(process, reason), "** (ErlangError) Erlang error: :badarg");
        let text = binary(process, "boom");
        assert_eq!(error_line(process, text), "** (ErlangError) Erlang error: \"boom\"");
    });
}

/// A struct is a map too, so a struct flagged `__exception__: true` is judged
/// an exception by the same reading of its keys.
#[test]
fn a_struct_flagged_as_an_exception_is_one() {
    with_process(|process| {
        let schema = process.heap.register_schema(Schema::named_struct(
            crate::module_name::ModuleName::from_segments(vec!["Overdrawn".to_string()]),
            ["__exception__".to_string(), "message".to_string()],
        ));
        let flag = atom(process, "true");
        let message = binary(process, "balance would be -5");
        let object = process.heap.alloc_struct(schema);
        unsafe {
            process.heap.write_field_slot(object, 0, flag);
            process.heap.write_field_slot(object, 8, message);
        }
        let value = AnyValue::from_ref(AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("struct ref"))
            .expect("struct value");
        assert_eq!(exception_name(process, value), Some(atom(process, "Elixir.Overdrawn")));
        assert_eq!(error_line(process, value), "** (Overdrawn) balance would be -5");
    });
}

#[test]
fn a_struct_shaped_map_without_the_exception_flag_is_not_an_exception() {
    with_process(|process| {
        let name = atom(process, "Elixir.ArgumentError");
        let message = binary(process, "bad");
        let value = map(process, &[("__struct__", name), ("message", message)]);
        let line = error_line(process, value);
        assert!(
            line.starts_with("** (ErlangError) Erlang error: %{"),
            "only a map flagged __exception__: true names an exception: {line}"
        );
    });
}

unsafe extern "C" fn recording_sink(context: *mut (), line: *const u8, len: usize) {
    let lines = unsafe { &mut *(context as *mut Vec<String>) };
    let line = unsafe { slice::from_raw_parts(line, len) };
    lines.push(String::from_utf8_lossy(line).into_owned());
}

#[test]
fn a_panic_hands_its_line_to_the_fault_sink_marks_the_process_failed_and_returns() {
    with_process(|process| {
        let mut lines: Vec<String> = Vec::new();
        let mut ctx = ExecCtx {
            scheduler: &mut lines as *mut Vec<String> as *mut (),
            fault: Some(recording_sink),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        let value = exception(process, "Elixir.RuntimeError", "boom");
        assert!(!process.failed, "a fresh process has not failed");

        panic_with(process, value);

        assert!(process.failed, "the panic marks the process failed");
        assert_eq!(
            lines,
            ["** (RuntimeError) boom"],
            "the sink receives exactly one line, without a newline"
        );
    });
}

/// A handler template: the one-capture closure image compiled code copies into
/// a handler record. Compiled code puts the outer continuation, a closure, in
/// capture 0; these tests never resume it, so `nil` stands in for it.
fn handler_template(process: &mut Process) -> ClosureRef {
    let closure = closure_addr_from_tagged(process.heap.alloc_closure_slots(ClosureDenotationId::INTERNAL, 0, 1, 0))
        .expect("a closure");
    unsafe { closure_capture_set(closure, 0, AnyValue::nil_atom()) };
    ClosureRef::new(AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure).expect("a closure ref"))
}

/// Push the record compiled code writes for a handler whose image is `template`.
fn push_compiled(process: &mut Process, template: ClosureRef) -> *mut u8 {
    push_template(
        &mut process.handlers,
        template.as_ref().closure_addr().expect("a closure ref"),
    )
}

fn capture(closure: *mut u8, index: usize) -> AnyValue {
    unsafe { closure_capture_value(closure, index) }
}

#[derive(Default)]
struct Observed {
    lines: Vec<String>,
    raises: Vec<(String, String, usize)>,
}

unsafe extern "C" fn observing_sink(context: *mut (), line: *const u8, len: usize) {
    let observed = unsafe { &mut *(context as *mut Observed) };
    let line = unsafe { slice::from_raw_parts(line, len) };
    observed.lines.push(String::from_utf8_lossy(line).into_owned());
}

unsafe extern "C" fn observing_raise(
    context: *mut (),
    kind: *const u8,
    kind_len: usize,
    name: *const u8,
    name_len: usize,
    depth: usize,
    _stack_bytes: usize,
) {
    let observed = unsafe { &mut *(context as *mut Observed) };
    let text = |ptr, len| String::from_utf8_lossy(unsafe { slice::from_raw_parts(ptr, len) }).into_owned();
    observed
        .raises
        .push((text(kind, kind_len), text(name, name_len), depth));
}

fn with_observed_process<R>(f: impl FnOnce(&mut Process, &mut Observed) -> R) -> R {
    with_process(|process| {
        let mut observed = Observed::default();
        let mut ctx = ExecCtx {
            scheduler: &mut observed as *mut Observed as *mut (),
            fault: Some(observing_sink),
            raise: Some(observing_raise),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        f(process, &mut observed)
    })
}

#[test]
fn a_panic_under_a_compiled_handler_delivers_the_handler_with_kind_value_and_name() {
    with_observed_process(|process, observed| {
        let template = handler_template(process);
        push_compiled(process, template);
        let value = exception(process, "Elixir.RuntimeError", "boom");

        panic_with(process, value);

        assert!(!process.failed, "a caught raise is not a failure");
        assert!(
            process.handlers.depth() == 0,
            "the handler is consumed by the raise it catches"
        );
        assert_eq!(process.raises_delivered, 1);
        assert!(observed.lines.is_empty(), "nothing is printed for a caught raise");
        let handler = process
            .delivered
            .expect("the handler is what the quantum resumes")
            .as_ref()
            .closure_addr()
            .expect("a closure ref");
        assert!(process.runnable.is_none(), "nothing is queued for the scheduler");
        assert_ne!(
            handler,
            template.as_ref().closure_addr().expect("a closure ref"),
            "the template itself is untouched"
        );
        assert_eq!(
            capture(handler, 0),
            AnyValue::nil_atom(),
            "the outer continuation comes first"
        );
        assert_eq!(capture(handler, 1), atom(process, "error"));
        assert_eq!(capture(handler, 2), value);
        assert_eq!(
            capture(handler, 3),
            value,
            "a raise with no reason of its own carries the raised value"
        );
        assert_eq!(capture(handler, 4), atom(process, "Elixir.RuntimeError"));
        assert_eq!(
            observed.raises,
            [("error".to_string(), "Elixir.RuntimeError".to_string(), 1)]
        );
    });
}

#[test]
fn a_panic_under_an_interpreter_handler_leaves_the_raise_for_the_interpreter_to_read() {
    with_observed_process(|process, observed| {
        process.push_interpreter_handler();
        let value = atom(process, "boom");

        panic_with(process, value);

        assert!(!process.failed);
        assert!(process.handlers.depth() == 0);
        assert!(
            process.runnable_closure().is_none(),
            "the interpreter owns its own frames"
        );
        let raised = process.raised.expect("the raise waits in the process");
        assert_eq!(raised.kind.value("kind"), atom(process, "error"));
        assert_eq!(raised.value.value("value"), value);
        assert_eq!(
            raised.name.value("name"),
            AnyValue::nil_atom(),
            "a value that is not an exception has no name"
        );
        assert_eq!(process.raises_delivered, 1);
        assert_eq!(observed.raises, [("error".to_string(), String::new(), 1)]);
    });
}

#[test]
fn a_panic_reaches_the_innermost_handler_and_leaves_the_outer_one_in_place() {
    with_observed_process(|process, observed| {
        let outer = handler_template(process);
        let outer = push_compiled(process, outer);
        process.push_interpreter_handler();
        let value = exception(process, "Elixir.KeyError", "key :a not found");

        panic_with(process, value);

        assert_eq!(process.handlers.depth(), 1);
        assert_eq!(process.handlers.innermost(), Some(Innermost::Compiled(outer)));
        assert!(
            process.raised.is_some(),
            "the interpreter marker, innermost, took the raise"
        );
        assert_eq!(
            observed.raises,
            [("error".to_string(), "Elixir.KeyError".to_string(), 2)]
        );
    });
}

#[test]
fn a_panic_without_a_handler_is_reported_at_depth_zero_and_still_fails_the_process() {
    with_observed_process(|process, observed| {
        let value = exception(process, "Elixir.RuntimeError", "boom");

        panic_with(process, value);

        assert!(process.failed);
        assert_eq!(process.raises_delivered, 0);
        assert_eq!(observed.lines, ["** (RuntimeError) boom"]);
        assert_eq!(
            observed.raises,
            [("error".to_string(), "Elixir.RuntimeError".to_string(), 0)]
        );
    });
}

#[test]
fn a_panic_reports_nothing_when_the_context_does_not_observe_raises() {
    with_process(|process| {
        let mut lines: Vec<String> = Vec::new();
        let mut ctx = ExecCtx {
            scheduler: &mut lines as *mut Vec<String> as *mut (),
            fault: Some(recording_sink),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        process.push_interpreter_handler();
        let value = atom(process, "boom");

        panic_with(process, value);

        assert!(process.raised.is_some());
        assert!(lines.is_empty());
    });
}

/// A two-tuple `{first, second}`, as a value.
fn pair(process: &mut Process, first: AnyValue, second: AnyValue) -> AnyValue {
    let schema = process.heap.register_schema(Schema::tuple_of_arity(2));
    let tuple = process.heap.alloc_struct(schema);
    for (index, field) in [first, second].into_iter().enumerate() {
        unsafe { process.heap.write_field_slot(tuple, (index * 8) as u32, field) };
    }
    AnyValue::heap_ptr(tuple, ValueKind::STRUCT)
}

/// Raise `value` through `raise` with a closure handler installed and return
/// what the handler was delivered as its kind and value.
fn delivered_by(
    process: &mut Process,
    value: AnyValue,
    raise: impl FnOnce(*mut Process, u64, u64),
) -> (AnyValue, AnyValue) {
    let template = handler_template(process);
    push_compiled(process, template);
    let Stored { word, kind } = Stored::of(value);

    raise(process, word, kind);

    let handler = process
        .delivered
        .expect("the handler was delivered")
        .as_ref()
        .closure_addr()
        .expect("a closure ref");
    (capture(handler, 1), capture(handler, 2))
}

#[test]
fn a_throw_delivers_kind_throw_and_an_exit_delivers_kind_exit() {
    with_observed_process(|process, observed| {
        let ball = atom(process, "ball");
        let (kind, value) = delivered_by(process, ball, |process, word, kind| fz_throw(process, word, kind));
        assert_eq!((kind, value), (atom(process, "throw"), ball));

        let reason = atom(process, "gone");
        let (kind, value) = delivered_by(process, reason, |process, word, kind| fz_exit(process, word, kind));
        assert_eq!((kind, value), (atom(process, "exit"), reason));

        assert!(!process.failed, "a caught throw or exit is not a failure");
        assert!(observed.lines.is_empty());
    });
}

#[test]
fn a_thrown_or_exited_number_reaches_its_handler_without_a_box() {
    with_observed_process(|process, _| {
        let boxes = |process: &Process| process.heap.node.alloc_stats().scalar_box.allocs;
        let before = boxes(process);

        let (_, value) = delivered_by(process, AnyValue::int(41), |process, word, kind| {
            fz_throw(process, word, kind)
        });
        assert_eq!(value, AnyValue::int(41));

        let (_, value) = delivered_by(process, AnyValue::float(2.5), |process, word, kind| {
            fz_exit(process, word, kind)
        });
        assert_eq!(value, AnyValue::float(2.5));

        assert_eq!(
            boxes(process),
            before,
            "a number travels from the raise to the handler as a word"
        );
    });
}

#[test]
#[should_panic(expected = "a collection ran between a raise and its handler")]
fn a_collection_between_a_raise_and_its_handler_fails_loudly() {
    with_observed_process(|process, _| {
        process.push_interpreter_handler();
        let value = atom(process, "boom");
        panic_with(process, value);
        assert!(process.raised.is_some());

        drop(process.collect(&mut []));
    });
}

#[test]
fn a_raise_event_carries_the_kind_text_with_no_exception_name_for_a_throw_or_an_exit() {
    with_observed_process(|process, observed| {
        let raises: [extern "C" fn(*mut Process, u64, u64); 3] = [fz_panic, fz_throw, fz_exit];
        for raise in raises {
            let value = atom(process, "v");
            delivered_by(process, value, |process, word, kind| raise(process, word, kind));
        }
        assert_eq!(
            observed.raises,
            [
                ("error".to_string(), String::new(), 1),
                ("throw".to_string(), String::new(), 1),
                ("exit".to_string(), String::new(), 1),
            ]
        );
    });
}

#[test]
fn a_reraise_continues_with_the_kind_it_was_delivered() {
    with_observed_process(|process, observed| {
        for kind in ["error", "throw", "exit"] {
            let value = atom(process, "v");
            let kind_ref = process.heap.box_any_value_ref(atom(process, kind));
            let (delivered_kind, delivered_value) = delivered_by(process, value, |process, word, kind| {
                fz_reraise(process, kind_ref.raw_word(), word, kind, word, kind)
            });
            assert_eq!((delivered_kind, delivered_value), (atom(process, kind), value));
        }
        assert_eq!(
            observed.raises,
            [
                ("error".to_string(), String::new(), 1),
                ("throw".to_string(), String::new(), 1),
                ("exit".to_string(), String::new(), 1),
            ]
        );
        assert!(!process.failed, "a re-raise a handler takes is not a failure");
    });
}

#[test]
fn a_reraise_nothing_handles_fails_the_process_like_the_original_raise() {
    with_observed_process(|process, observed| {
        let ball = pair(process, atom(process, "ball"), AnyValue::int(1));
        let Stored { word, kind } = Stored::of(ball);
        let kind_ref = process.heap.box_any_value_ref(atom(process, "throw"));

        fz_reraise(process, kind_ref.raw_word(), word, kind, word, kind);

        assert!(process.failed);
        assert_eq!(observed.lines, ["** (throw) {:ball, 1}"]);
    });
}

#[test]
#[should_panic(expected = "fz_reraise: the kind")]
fn a_reraise_of_a_kind_the_runtime_never_delivered_is_an_invariant_violation() {
    with_observed_process(|process, _| {
        let value = Stored::of(atom(process, "v"));
        let bogus = atom(process, "bogus");
        reraise(process, bogus, value, value);
    });
}

#[test]
fn an_uncaught_throw_prints_its_value_and_ends_the_process_with_status_1() {
    with_observed_process(|process, observed| {
        let ball = pair(process, atom(process, "ball"), AnyValue::int(1));
        let Stored { word, kind } = Stored::of(ball);

        fz_throw(process, word, kind);

        assert!(process.failed);
        assert_eq!(process.exit_status, 1);
        assert_eq!(observed.lines, ["** (throw) {:ball, 1}"]);
        assert_eq!(observed.raises, [("throw".to_string(), String::new(), 0)]);
    });
}

fn uncaught_exit(process: &mut Process, reason: AnyValue) -> Option<String> {
    let Stored { word, kind } = Stored::of(reason);
    process.failed = false;
    process.exit_status = 0;
    fz_exit(process, word, kind);
    assert!(process.failed, "an exit nothing handles ends the process");
    failure_line(process, RaiseKind::Exit, reason)
}

#[test]
fn an_uncaught_exit_prints_its_reason_and_exits_1_unless_the_reason_is_a_shutdown() {
    with_observed_process(|process, observed| {
        let reason = pair(process, atom(process, "bad"), atom(process, "reason"));
        assert_eq!(
            uncaught_exit(process, reason).as_deref(),
            Some("** (exit) {:bad, :reason}")
        );
        assert_eq!(process.exit_status, 1);
        assert_eq!(observed.lines, ["** (exit) {:bad, :reason}"]);

        let reason = pair(process, atom(process, "other"), AnyValue::int(7));
        assert_eq!(uncaught_exit(process, reason).as_deref(), Some("** (exit) {:other, 7}"));
        assert_eq!(process.exit_status, 1, "only a tuple led by :shutdown is a shutdown");
    });
}

#[test]
fn an_exit_with_a_shutdown_reason_ends_silently_with_the_status_elixirs_cli_gives() {
    let statuses = |process: &mut Process, reasons: Vec<AnyValue>| {
        reasons
            .into_iter()
            .map(|reason| {
                assert_eq!(uncaught_exit(process, reason), None, "a shutdown prints nothing");
                process.exit_status
            })
            .collect::<Vec<_>>()
    };
    with_observed_process(|process, observed| {
        let shutdown = atom(process, "shutdown");
        let reasons = vec![
            atom(process, "normal"),
            shutdown,
            pair(process, shutdown, AnyValue::int(7)),
            pair(process, shutdown, AnyValue::int(0)),
            pair(process, shutdown, atom(process, "not_a_status")),
        ];
        assert_eq!(statuses(process, reasons), [0, 0, 7, 0, 0]);
        assert!(
            observed.lines.is_empty(),
            "no shutdown prints a line: {:?}",
            observed.lines
        );
        assert!(
            !process.ended_in_failure(),
            "the last of them left status 0, which is not a failure"
        );
    });
}

/// Runs `f` on a process whose fault sink records lines; answers the lines
/// and whether the process failed.
fn recording(f: impl FnOnce(&mut Process)) -> (Vec<String>, bool) {
    with_process(|process| {
        let mut lines: Vec<String> = Vec::new();
        let mut ctx = ExecCtx {
            scheduler: &mut lines as *mut Vec<String> as *mut (),
            fault: Some(recording_sink),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        f(process);
        process.ctx = std::ptr::null_mut();
        (lines, process.failed)
    })
}

#[test]
fn a_raise_with_no_handler_prints_the_message_the_exception_carries() {
    let (lines, failed) = recording(|process| {
        declare(process, "Elixir.ArgumentError", &["message"]);
        let name = atom(process, "Elixir.ArgumentError");
        let message = binary(process, "argument error");
        raise_exception(process, name, &[("message", message)], None);
    });
    assert!(failed, "a raise fails the process through the panic route");
    assert_eq!(
        lines,
        ["** (ArgumentError) argument error"],
        "no module can be asked here, so the words the exception carries are printed"
    );
}

#[test]
fn a_raise_with_no_handler_and_no_message_prints_the_exception_as_a_value() {
    let (lines, failed) = recording(|process| {
        declare(process, "Elixir.MatchError", &["term"]);
        let name = atom(process, "Elixir.MatchError");
        raise_exception(process, name, &[("term", AnyValue::Int(7))], None);
    });
    assert!(failed);
    assert_eq!(
        lines,
        ["** (ErlangError) Erlang error: %MatchError{term: 7}"],
        "the words belong to the module, which the runtime does not ask"
    );
}

/// The fields of the exception a raise delivered to an interpreter handler.
fn delivered_exception(process: &mut Process, raise: impl FnOnce(&mut Process)) -> AnyValue {
    process.push_interpreter_handler();
    raise(process);
    let raised = process.raised.expect("the raise waits in the process");
    raised.value.value("exception")
}

#[test]
fn a_raised_exception_is_a_struct_of_its_module_holding_the_fields_it_was_given() {
    with_observed_process(|process, _| {
        declare(process, "Elixir.CaseClauseError", &["term"]);
        let name = atom(process, "Elixir.CaseClauseError");
        let exception = delivered_exception(process, |process| {
            raise_exception(process, name, &[("term", AnyValue::Int(3))], None);
        });
        let module = crate::module_name::ModuleName::from_atom_name("Elixir.CaseClauseError").expect("a module");
        let raised = process.heap.box_any_value_ref(exception);
        assert!(
            process.heap.has_struct_layout_of(raised, &module),
            "the raised value is laid out as the struct its module declares"
        );
        assert_eq!(exception_name(process, exception), Some(name));
        assert_eq!(
            exception_field(process, exception, "term"),
            Some(AnyValue::Int(3)),
            "the subject is the exception's term, as in Elixir"
        );
        assert_eq!(
            exception_field(process, exception, "message"),
            None,
            "the message is computed by the module, not stored"
        );
    });
}

#[test]
#[should_panic(expected = "is raised before its struct is registered")]
fn an_exception_whose_struct_nothing_registered_cannot_be_raised() {
    with_observed_process(|process, _| {
        let name = atom(process, "Elixir.CaseClauseError");
        raise_exception(process, name, &[("term", AnyValue::Int(3))], None);
    });
}

#[test]
#[should_panic(expected = "is raised with no `term`")]
fn an_exception_is_raised_with_every_field_its_module_declares() {
    with_observed_process(|process, _| {
        declare(process, "Elixir.BadBooleanError", &["term", "operator"]);
        let name = atom(process, "Elixir.BadBooleanError");
        let or = atom(process, "or");
        raise_exception(process, name, &[("operator", or), ("left", AnyValue::Int(1))], None);
    });
}

fn undefined_function_raise(
    process: &mut Process,
    receiver: AnyValue,
    function: &str,
    arity: i64,
    module_is_defined: bool,
) -> (AnyValue, String) {
    declare_undefined_call_exceptions(process);
    process.push_interpreter_handler();
    let function = atom(process, function);
    raise_undefined_function(process, receiver, function, arity, module_is_defined);
    let raised = process.raised.take().expect("the raise waits in the process");
    let exception = raised.value.value("exception");
    let message = exception_field(process, exception, "message").expect("message");
    (exception, binary_text(message).expect("a binary message"))
}

#[test]
fn a_call_on_an_atom_that_reaches_no_function_raises_elixirs_undefined_function_error() {
    with_observed_process(|process, _| {
        let name = atom(process, "Elixir.UndefinedFunctionError");
        let square = atom(process, "Elixir.Square");
        let nowhere = atom(process, "nowhere");
        let nil = atom(process, "nil");

        let (exception, message) = undefined_function_raise(process, nowhere, "area", 1, false);
        assert_eq!(exception_name(process, exception), Some(name));
        assert_eq!(
            message, "function :nowhere.area/1 is undefined (module :nowhere is not available)",
            "an atom naming no module says the module is not available"
        );
        assert_eq!(exception_field(process, exception, "module"), Some(nowhere));
        assert_eq!(
            exception_field(process, exception, "function"),
            Some(atom(process, "area"))
        );
        assert_eq!(exception_field(process, exception, "arity"), Some(AnyValue::Int(1)));
        assert_eq!(exception_field(process, exception, "reason"), Some(nil));

        let (_, message) = undefined_function_raise(process, square, "nope", 0, true);
        assert_eq!(
            message, "function Square.nope/0 is undefined or private",
            "a module that lacks the function says so"
        );

        let (_, message) = undefined_function_raise(process, nil, "area", 1, false);
        assert_eq!(
            message, "function nil.area/1 is undefined",
            "nil is reported without a module"
        );
    });
}

#[test]
fn a_call_on_a_value_that_is_no_atom_raises_elixirs_argument_error() {
    with_observed_process(|process, _| {
        let name = atom(process, "Elixir.ArgumentError");

        let (exception, message) = undefined_function_raise(process, AnyValue::Int(1), "area", 1, false);
        assert_eq!(exception_name(process, exception), Some(name));
        assert_eq!(
            message,
            "you attempted to apply a function on 1. Modules (the first argument of apply) must always be an atom"
        );

        let (_, message) = undefined_function_raise(process, AnyValue::Int(1), "nope", 0, false);
        assert_eq!(
            message,
            "you attempted to apply a function named :nope on 1. If you are using Kernel.apply/3, make sure the \
             module is an atom. If you are using the dot syntax, such as module.function(), make sure the \
             left-hand side of the dot is an atom representing a module",
            "a call with no arguments names the function, as it may have been meant as a field read"
        );
    });
}

#[test]
fn the_extern_raise_finds_the_receiver_among_the_modules_that_lack_the_function() {
    with_observed_process(|process, _| {
        process.push_interpreter_handler();
        let square = atom(process, "Elixir.Square");
        let circle = atom(process, "Elixir.Circle");
        let nope = atom(process, "nope");
        let modules = [square, circle].into_iter().fold(AnyValue::EmptyList, |tail, module| {
            let cell = process.heap.alloc_list_cons_any(module, tail);
            AnyValue::from_ref(cell).expect("a list cell")
        });
        let word = |process: &mut Process, value| process.heap.box_any_value_ref(value).raw_word();
        let (receiver, function) = (word(process, square), word(process, nope));
        let modules = process.heap.box_any_value_ref(modules).raw_word();

        declare_undefined_call_exceptions(process);
        fz_raise_undefined_function(process, receiver, function, 0, modules);

        let raised = process.raised.expect("the raise waits in the process");
        let exception = raised.value.value("exception");
        let message = exception_field(process, exception, "message").expect("message");
        assert_eq!(
            binary_text(message).as_deref(),
            Some("function Square.nope/0 is undefined or private")
        );
    });
}

extern "C" fn recording_halt(scheduler: *mut (), status: i32) {
    unsafe { &mut *(scheduler as *mut Vec<i32>) }.push(status);
}

#[test]
fn a_halt_reports_its_status_and_ends_the_process_past_every_handler_without_a_line() {
    with_process(|process| {
        let mut halts: Vec<i32> = Vec::new();
        let mut ctx = ExecCtx {
            scheduler: &mut halts as *mut Vec<i32> as *mut (),
            halt: Some(recording_halt),
            ..ExecCtx::empty()
        };
        process.ctx = &mut ctx;
        let handler = handler_template(process);
        push_compiled(process, handler);

        fz_system_halt(process, 3);

        assert_eq!(halts, [3], "the scheduler is told the program's status once");
        assert!(process.failed, "the process ends as an uncaught raise ends it");
        assert_eq!(process.exit_status, 3);
        assert_eq!(
            process.handlers.depth(),
            1,
            "no handler is searched, so none is consumed"
        );
        assert!(process.raised.is_none() && !process.has_delivered_handler());
    });
}
