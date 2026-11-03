use super::*;

extern "C" fn sample_send(_sender: *mut Process, _scheduler: *mut (), _pid: u32, _msg: u64) {}

#[test]
fn empty_ctx_has_null_handles_and_no_callbacks() {
    let ctx = ExecCtx::empty();
    assert!(ctx.scheduler.is_null());
    assert!(ctx.output_context.is_null());
    assert!(ctx.send.is_none());
    assert!(ctx.spawn.is_none());
    assert!(ctx.fault.is_none());
}

#[test]
fn populated_ctx_reads_its_fields_back() {
    let mut scheduler = 0u64;
    let tel = 7u64;
    let ctx = ExecCtx {
        scheduler: (&mut scheduler) as *mut u64 as *mut (),
        output_context: (&tel) as *const u64 as *const (),
        send: Some(sample_send),
        ..ExecCtx::empty()
    };
    assert_eq!(ctx.scheduler, (&mut scheduler) as *mut u64 as *mut ());
    assert_eq!(ctx.output_context, (&tel) as *const u64 as *const ());
    assert!(ctx.send.is_some());
}

#[test]
fn a_context_without_argv_reads_as_the_empty_command_line() {
    let ctx = ExecCtx::empty();
    assert!(ctx.argv().is_empty());
}

#[test]
fn a_context_reads_back_the_program_arguments_its_driver_owns() {
    let argv = Argv::new(vec![b"a".to_vec(), Vec::new(), vec![0xff, 0xfe]]);
    let ctx = ExecCtx {
        argv: &argv,
        ..ExecCtx::empty()
    };
    assert_eq!(ctx.argv(), [b"a".to_vec(), Vec::new(), vec![0xff, 0xfe]]);
}
