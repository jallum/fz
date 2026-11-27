//! Which continuations share a body frame, and what the frame costs the
//! compiled program. Each test but the layout's refusal compiles and runs a
//! real program and observes the native program the planner produced, the code
//! the backend emitted for it, and the process that ran it.

use super::*;
use crate::compiler2::artifact::FrameRole;
use crate::compiler2::drive_harness::NativeProgramCapture;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::exec::runtime::{ExitRecord, ProcessExitCapture};
use crate::telemetry::ConfiguredTelemetry;
use std::cell::RefCell;
use std::path::Path;
use std::rc::Rc;

/// The body frames of one compiled program and the run that followed.
struct FramedRun {
    roots: Vec<u32>,
    members: usize,
    refused: Vec<RefusedFrame>,
    code_bytes: usize,
    /// The display name of each function that has a body of its own.
    executable_bodies: Vec<String>,
    exit: ExitRecord,
}

/// Runs on a thread with the stack the `fz2` binary's main thread has: a body
/// of a thousand terms nests that deep in the front end, more than a test
/// thread's default stack holds.
fn compile_and_run(name: &str, source: &str) -> FramedRun {
    let (name, source) = (name.to_string(), source.to_string());
    std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || compile_and_run_here(&name, &source))
        .expect("spawn the compiling thread")
        .join()
        .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
}

fn compile_and_run_here(name: &str, source: &str) -> FramedRun {
    let tel = ConfiguredTelemetry::new();
    let exits = ProcessExitCapture::new();
    exits.install(&tel);
    let native = NativeProgramCapture::new();
    native.install(&tel);
    let refused = Rc::new(RefCell::new(Vec::new()));
    let refused_sink = Rc::clone(&refused);
    tel.attach_raw_event2::<crate::compiler2::RootId, RefusedFrame, _>(
        &["fz", "compiler2", "native_program", "frame_refused"],
        move |_, _, _, _, frame| refused_sink.borrow_mut().push(*frame),
    );
    let code_bytes = Rc::new(RefCell::new(0usize));
    let code_bytes_sink = Rc::clone(&code_bytes);
    tel.attach_raw_span1_1::<crate::fz_ir::FnId, cranelift_codegen::Context, _, _, _>(
        &["fz", "codegen", "define_function"],
        |_, _, _, _| {},
        move |_, _, _, _, context| {
            if let Some(code) = context.compiled_code() {
                *code_bytes_sink.borrow_mut() += code.code_buffer().len();
            }
        },
        |_, _, _, _| {},
    );
    let mut compiler = Compiler2::new(tel);
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.submit_code(CodeSubmission {
        name: Some(name.to_string()),
        text: source.to_string(),
    });
    compiler
        .run_root_jit(root)
        .unwrap_or_else(|error| panic!("{name} should run end-to-end: {error}"));
    let program = native.last(root).program;
    let executable_bodies = program
        .bodies
        .iter()
        .filter_map(|body| match &body.origin {
            NativeBodyOrigin::Executable(key) => {
                Some(compiler.world().function_ref(key.activation.function).display_name())
            }
            _ => None,
        })
        .collect();
    let frames = || program.bodies.iter().filter_map(|body| body.frame);
    FramedRun {
        roots: frames()
            .filter(|frame| frame.role == FrameRole::Root)
            .map(|frame| frame.slots)
            .collect(),
        members: frames().filter(|frame| frame.role == FrameRole::Member).count(),
        refused: refused.borrow().clone(),
        code_bytes: *code_bytes.borrow(),
        executable_bodies,
        exit: exits.last().expect("runtime process exit telemetry"),
    }
}

/// `main` calls `f` `calls` times, holds every result, and sums them. `f`
/// tail-calls a loop, so it needs a frame and each call builds a continuation.
fn sequential_calls(calls: usize) -> String {
    let names: Vec<String> = (1..=calls).map(|i| format!("a{i}")).collect();
    let mut source = String::from(
        "def f(x), do: bump(x, 1)\n\ndefp bump(x, 0), do: x\ndefp bump(x, k), do: bump(x + 1, k - 1)\n\ndef main() do\n",
    );
    for (i, name) in names.iter().enumerate() {
        source.push_str(&format!("  {name} = f({})\n", i + 1));
    }
    source.push_str(&format!("  {}\nend\n", names.join(" + ")));
    source
}

fn fixture(stem: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("fixtures/{stem}.fz"));
    std::fs::read_to_string(&path).unwrap_or_else(|error| panic!("read {}: {error}", path.display()))
}

/// A body that holds a thousand results across a thousand calls is cut into a
/// continuation per call. Giving each its own frame copies every held result
/// into every later frame: the program grows with the square of the calls (the
/// native code reached 51 MB and the JIT could not place it). One frame keeps
/// the code proportional to the calls.
#[test]
fn compiler2_a_thousand_sequential_calls_run_in_one_frame_and_compile_to_a_small_program() {
    let run = compile_and_run(
        "a_thousand_sequential_calls.fz",
        &fixture("01253_a_thousand_sequential_calls_sum_their_results"),
    );

    assert_eq!(run.exit.halt_value, 501500, "the sum of f(1)..f(1000)");
    assert_eq!(run.roots, [1000], "one frame holds the thousand results");
    assert_eq!(
        run.members, 984,
        "every other continuation of the body runs in that frame"
    );
    assert_eq!(run.exit.frame_copies, 0, "nothing collects, so the frame is never old");
    assert!(
        run.code_bytes < 4_000_000,
        "the program's native code is proportional to its calls: {} bytes",
        run.code_bytes
    );
}

/// A short chain keeps a frame per continuation: each is popped as it resumes,
/// which costs less than a frame wide enough for the whole body.
#[test]
fn compiler2_a_short_body_keeps_a_frame_per_continuation() {
    let run = compile_and_run("four_sequential_calls.fz", &sequential_calls(4));

    assert_eq!(run.exit.halt_value, 14);
    assert_eq!((run.roots.len(), run.members), (0, 0));
}

/// A body holding two hundred closures and then calling each used to store
/// every closure again at every call: the frame's slots grew with the square of
/// the closures (17,206 here) and past the closure header's 13-bit count. A
/// value has one slot however many names the body gives it, so the frame holds
/// two slots per closure (the closure and its capture) and the calls run in it,
/// collecting while it is live.
#[test]
fn compiler2_a_frame_holds_each_live_value_once_however_many_names_the_body_gives_it() {
    let run = compile_and_run(
        "two_hundred_closures.fz",
        &fixture("02033_two_hundred_closures_that_allocate_when_called_share_a_body_frame_that_holds_each_value_once"),
    );

    assert_eq!(run.roots, [370], "the slots are linear in the closures, not quadratic");
    assert_eq!(run.refused, [], "a frame this size fits the header");
}

/// A frame placed one slot wider than the closure header counts is refused
/// with every member that runs in it, and the report names its width; a frame
/// exactly as wide as the header counts stays.
#[test]
fn compiler2_a_frame_wider_than_the_closure_header_counts_is_refused_with_its_members() {
    let limit = u32::from(CLOSURE_FLAGS_CAPTURED_MASK);
    let (too_wide, fits) = (FnId(1), FnId(10));
    let (wide_member, fitting_member) = (FnId(2), FnId(11));
    let site = Site {
        builder: too_wide,
        block: 0,
    };
    let join = |member, builder| Join {
        member,
        site: Site { builder, ..site },
        extra: 0,
        stores: Vec::new(),
        clears: Vec::new(),
        loads: Vec::new(),
    };
    let frame = |root| PlacedFrame {
        root,
        held: HashMap::default(),
    };
    let mut layout = FrameLayout::default();
    layout.root_slots.insert(too_wide, limit + 1);
    layout.root_slots.insert(fits, limit);
    for (fn_id, root) in [
        (too_wide, too_wide),
        (wide_member, too_wide),
        (fits, fits),
        (fitting_member, fits),
    ] {
        layout.frames.insert(fn_id, frame(root));
    }
    layout.joins.push(join(wide_member, too_wide));
    layout.joins.push(join(fitting_member, fits));

    let refused = layout.refuse_oversize();

    assert_eq!(
        refused,
        [RefusedFrame {
            root: too_wide,
            slots: limit + 1
        }]
    );
    let mut kept: Vec<FnId> = layout.frames.keys().copied().collect();
    kept.sort();
    assert_eq!(kept, [fits, fitting_member], "only the frame that fits is kept");
    assert_eq!(
        layout.joins.len(),
        1,
        "the refused chain's member no longer joins a frame"
    );
    assert_eq!(layout.joins[0].member, fitting_member);
    assert_eq!(layout.root_slots.keys().copied().collect::<Vec<_>>(), [fits]);
}

/// `clauses` clauses of one function, each a distinct four-byte literal then a
/// byte and the rest of the binary, and a catch-all.
fn literal_clauses_then_a_byte(clauses: usize) -> String {
    let mut source = String::from("defmodule P do\n");
    for clause in 0..clauses {
        let literal = [b'a' + clause as u8, b'b', b'c', b'd'];
        source.push_str(&format!(
            "  def w(<<\"{}\", x, r::binary>>), do: x + {clause} + byte_size(r)\n",
            String::from_utf8_lossy(&literal)
        ));
    }
    source.push_str("  def w(_), do: 0\nend\n\ndef main(), do: P.w(\"abcdZ!\")\n");
    source
}

/// Sibling binary clauses each ask for their own byte after the literal they
/// share the read of, so each clause adds about a fixed amount of code. Then
/// going from eight to sixteen clauses adds about twice what going from four to
/// eight added, where growth quadratic in the clauses (a shared node copied
/// once per edge into it) would add four times as much. The bound sits between
/// the two, and compares sizes from one target with each other, so it holds
/// whatever that target's instruction widths are.
#[test]
fn compiler2_sibling_binary_clauses_compile_to_code_proportional_to_their_count() {
    let [four, eight, sixteen] = [4, 8, 16].map(|clauses| {
        let run = compile_and_run("literal_clauses_then_a_byte.fz", &literal_clauses_then_a_byte(clauses));
        assert_eq!(
            run.exit.halt_value, 91,
            "the first clause adds 'Z' (90), its index 0 and the one byte that remains"
        );
        run.code_bytes
    });
    let (first_doubling, second_doubling) = (eight - four, sixteen - eight);
    assert!(
        second_doubling <= 3 * first_doubling,
        "eight more clauses add {second_doubling} bytes, four more added {first_doubling}"
    );
}

/// A callee copied into every caller that reaches it has no body of its own:
/// nothing calls the standalone function, so emitting it only adds code.
#[test]
fn compiler2_a_callee_copied_into_its_only_caller_has_no_body_of_its_own() {
    let run = compile_and_run("literal_clauses_then_a_byte.fz", &literal_clauses_then_a_byte(4));

    assert_eq!(run.exit.halt_value, 91);
    assert!(
        run.executable_bodies.iter().any(|name| name == "main"),
        "main is the root: {:?}",
        run.executable_bodies
    );
    assert!(
        !run.executable_bodies.iter().any(|name| name == "w"),
        "w is copied into main, so no function of its own remains: {:?}",
        run.executable_bodies
    );
}
