use super::*;

extern "C" fn sample_send(_sender: *mut Process, _scheduler: *mut (), _pid: u32, _msg: u64) {}

#[test]
fn empty_ctx_has_null_handles_and_no_callbacks() {
    let ctx = ExecCtx::empty();
    assert!(ctx.scheduler.is_null());
    assert!(ctx.tel.is_null());
    assert!(ctx.module.is_null());
    assert!(ctx.send.is_none());
    assert!(ctx.spawn.is_none());
}

#[test]
fn populated_ctx_reads_its_fields_back() {
    let mut scheduler = 0u64;
    let tel = 7u64;
    let module = 9u64;
    let ctx = ExecCtx {
        scheduler: (&mut scheduler) as *mut u64 as *mut (),
        tel: (&tel) as *const u64 as *const (),
        module: (&module) as *const u64 as *const (),
        send: Some(sample_send),
        ..ExecCtx::empty()
    };
    assert_eq!(ctx.scheduler, (&mut scheduler) as *mut u64 as *mut ());
    assert_eq!(ctx.tel, (&tel) as *const u64 as *const ());
    assert_eq!(ctx.module, (&module) as *const u64 as *const ());
    assert!(ctx.send.is_some());
}
