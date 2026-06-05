//! fz-vdt ctx.9 — coexistence proof.
//!
//! The epic's signal: two `IrInterpRuntime`s, each with its own telemetry sink,
//! live at once on one thread, and each sink sees only its own `dbg` output.
//! This was impossible to write honestly before the arc — `dbg` routed through
//! the thread-global `CURRENT_TEL`/`CURRENT_PROCESS`, so a second runtime would
//! clobber the first's ambient state. Now every BIF carries its process and the
//! telemetry sink lives on the per-task `ExecCtx`, so the two runtimes share no
//! ambient state at all.

use crate::exec::runtime::DbgCapture;
use crate::fz_ir::Module;
use crate::ir_interp::IrInterpRuntime;
use crate::ir_lower::lower_program;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::Telemetry;
use crate::telemetry::bus::ConfiguredTelemetry;

fn lower_src(src: &str) -> Module {
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    lower_program(
        &mut crate::types::new(),
        &prog,
        &crate::telemetry::ConfiguredTelemetry::new(),
    )
    .expect("lower")
}

/// A telemetry sink that captures `dbg` lines, returned alongside the capture
/// handle so the test can read what each runtime emitted.
fn capture() -> (ConfiguredTelemetry, DbgCapture) {
    let tel = ConfiguredTelemetry::new();
    let cap = DbgCapture::new();
    tel.attach(&[], cap.handler());
    (tel, cap)
}

fn drive_main(runtime: &mut IrInterpRuntime, module: &Module, tel: &dyn Telemetry) {
    let main_id = module.fn_by_name("main").expect("main/0").id;
    let mut t = crate::types::new();
    runtime.enqueue_entry(module, 1, main_id, vec![]).expect("enqueue");
    runtime.drive_until_idle(&mut t, tel, None).expect("drive");
}

#[test]
fn two_interpreters_coexist_with_isolated_telemetry() {
    let mod_a = lower_src("fn main() do dbg(:from_a) end");
    let mod_b = lower_src("fn main() do dbg(:from_b) end");

    let (tel_a, cap_a) = capture();
    let (tel_b, cap_b) = capture();

    // Both runtimes are constructed and held live simultaneously — two
    // independent task registries, heaps, and ExecCtxs on one thread.
    let mut rt_a = IrInterpRuntime::fresh_with_root(&mod_a);
    let mut rt_b = IrInterpRuntime::fresh_with_root(&mod_b);

    // Interleave on one thread: A runs, then B runs, with both runtime objects
    // alive across both drives. Each routes its dbg through its own ExecCtx.tel.
    drive_main(&mut rt_a, &mod_a, &tel_a);
    drive_main(&mut rt_b, &mod_b, &tel_b);

    // Each sink saw only its own output. Under the old ambient CURRENT_TEL this
    // isolation could not hold — the global sink was whatever was last installed.
    assert_eq!(cap_a.lines(), vec![":from_a".to_string()]);
    assert_eq!(cap_b.lines(), vec![":from_b".to_string()]);
}

#[test]
fn interleaved_rounds_keep_each_runtimes_state_isolated() {
    // Two runtimes whose `main` emits a marker and whose heaps accumulate
    // distinct data. Driven in alternating rounds (A, B, A, B) to exercise
    // resumption with no cross-talk.
    let mod_a = lower_src("fn main() do dbg(:a_round) end");
    let mod_b = lower_src("fn main() do dbg(:b_round) end");

    let (tel_a, cap_a) = capture();
    let (tel_b, cap_b) = capture();

    let mut rt_a = IrInterpRuntime::fresh_with_root(&mod_a);
    let mut rt_b = IrInterpRuntime::fresh_with_root(&mod_b);

    // Round 1: A, then B.
    drive_main(&mut rt_a, &mod_a, &tel_a);
    drive_main(&mut rt_b, &mod_b, &tel_b);
    // Round 2: re-drive each (pid 1 persists in each runtime), still interleaved.
    drive_main(&mut rt_a, &mod_a, &tel_a);
    drive_main(&mut rt_b, &mod_b, &tel_b);

    assert_eq!(cap_a.lines(), vec![":a_round".to_string(), ":a_round".to_string()]);
    assert_eq!(cap_b.lines(), vec![":b_round".to_string(), ":b_round".to_string()]);
}
