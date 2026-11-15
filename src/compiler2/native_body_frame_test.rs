//! Which continuations share a body frame, and what the frame costs the
//! compiled program. Each test compiles and runs a real program and observes
//! the native program the planner produced, the code the backend emitted for
//! it, and the process that ran it.

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
    code_bytes: usize,
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
    let frames = || program.bodies.iter().filter_map(|body| body.frame);
    FramedRun {
        roots: frames()
            .filter(|frame| frame.role == FrameRole::Root)
            .map(|frame| frame.slots)
            .collect(),
        members: frames().filter(|frame| frame.role == FrameRole::Member).count(),
        code_bytes: *code_bytes.borrow(),
        exit: exits.last().expect("runtime process exit telemetry"),
    }
}

/// `main` calls `f` `calls` times, holds every result, and sums them.
fn sequential_calls(calls: usize) -> String {
    let names: Vec<String> = (1..=calls).map(|i| format!("a{i}")).collect();
    let mut source = String::from("def f(x), do: x + 1\n\ndef main() do\n");
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
    assert_eq!(
        run.roots,
        [1001],
        "one frame holds the thousand results and the outer continuation"
    );
    assert_eq!(
        run.members, 1983,
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
