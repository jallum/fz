//! Which continuations run in a body frame, and what each one is handed.

use super::super::artifact::{BodyFrame, FrameRole, NativeBodyOrigin, NativeProgram};
use super::super::identity::ExecutableNeed;
use super::super::{CodeSubmission, Compiler2, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;
use std::rc::Rc;

fn native_program(name: &str, text: String) -> Rc<NativeProgram> {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some(format!("{name}.fz")),
        text,
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    compiler.compile_root_jit(root).expect("the program compiles");
    compiler.retained_native_program(root)
}

/// `main` calls `f` N times, binds each result, and sums them last, so every
/// result stays live across all the calls after it.
fn sequential_calls_program(calls: usize) -> String {
    let binds: String = (1..=calls).map(|i| format!("  a{i} = f({i})\n")).collect();
    let sum = (1..=calls).map(|i| format!("a{i}")).collect::<Vec<_>>().join(" + ");
    format!("def f(x), do: x + 1\ndef main() do\n{binds}  IO.inspect({sum})\nend\n")
}

/// The frame facts of every continuation `main` is cut into, directly or
/// through another of its continuations: role, width and parameter count.
fn main_frames(program: &NativeProgram) -> Vec<(FrameRole, u32, usize)> {
    let owner_of = |fn_id| {
        program
            .bodies
            .iter()
            .find(|body| body.fn_id == fn_id)
            .and_then(|body| match body.origin {
                NativeBodyOrigin::Continuation { owner } => Some(owner),
                _ => None,
            })
    };
    let of_main = |mut fn_id| {
        while let Some(owner) = owner_of(fn_id) {
            fn_id = owner;
        }
        fn_id == program.entry
    };
    program
        .bodies
        .iter()
        .filter(|body| matches!(body.origin, NativeBodyOrigin::Continuation { .. }) && of_main(body.fn_id))
        .map(|body| {
            let BodyFrame { role, slots } = body.frame.expect("every continuation of main runs in a frame");
            (role, slots, body.param_reprs.len())
        })
        .collect()
}

fn roots(frames: &[(FrameRole, u32, usize)]) -> usize {
    frames.iter().filter(|(role, ..)| *role == FrameRole::Root).count()
}

#[test]
fn the_continuations_of_a_body_of_sequential_calls_run_in_one_frame() {
    let calls = 6;
    let program = native_program("sequential_calls", sequential_calls_program(calls));
    let frames = main_frames(&program);
    assert!(
        frames.len() >= calls,
        "each call of main resumes in a continuation: {frames:?}"
    );
    assert_eq!(
        roots(&frames),
        1,
        "the first continuation starts the frame, and every later one is built once, by the one \
         before it, so it joins that frame: {frames:?}"
    );
    let width = frames[0].1;
    assert!(
        frames.iter().all(|(_, slots, _)| *slots == width),
        "the frame is as wide for every continuation that runs in it: {frames:?}"
    );
    assert!(
        frames
            .iter()
            .filter(|(role, ..)| *role == FrameRole::Member)
            .all(|(_, _, params)| *params <= 1),
        "a member is handed at most the call's result; its other values are in the frame: {frames:?}"
    );
}

#[test]
fn a_continuation_built_by_both_branches_of_an_if_starts_its_own_frame() {
    let text = "def f(x), do: x + 1
def main() do
  a = f(1)
  b = if a > 1 do
    f(2)
  else
    f(3)
  end
  c = f(b)
  IO.inspect(a + b + c)
end
";
    let program = native_program("branch_join", text.to_string());
    let frames = main_frames(&program);
    assert_eq!(
        roots(&frames),
        2,
        "the continuation after the `if` is built by a call in each branch, so it is no one \
         member's next step: it starts a second frame, which the calls after it join: {frames:?}"
    );
}
