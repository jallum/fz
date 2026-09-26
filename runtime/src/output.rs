use std::io::Write as _;
use std::slice::from_raw_parts;

use crate::scheduler_hooks::OutputHook;

pub trait OutputSink {
    fn emit(&self, bytes: &[u8]);
}

pub struct NullOutput;

impl OutputSink for NullOutput {
    fn emit(&self, _bytes: &[u8]) {}
}

pub struct StdoutOutput;

impl OutputSink for StdoutOutput {
    fn emit(&self, bytes: &[u8]) {
        let mut stdout = std::io::stdout().lock();
        let _ = stdout.write_all(bytes);
        let _ = stdout.write_all(b"\n");
    }
}

pub static STDOUT_OUTPUT: StdoutOutput = StdoutOutput;

pub struct OutputContext<'a>(&'a dyn OutputSink);

impl<'a> OutputContext<'a> {
    pub fn new(sink: &'a dyn OutputSink) -> Self {
        Self(sink)
    }

    pub fn as_ptr(&self) -> *const () {
        self as *const Self as *const ()
    }
}

unsafe extern "C" fn output_hook(context: *const (), bytes: *const u8, len: usize) {
    if context.is_null() {
        return;
    }
    let context = unsafe { &*(context as *const OutputContext<'_>) };
    context.0.emit(unsafe { from_raw_parts(bytes, len) });
}

unsafe extern "C" fn stdout_output_hook(_context: *const (), bytes: *const u8, len: usize) {
    STDOUT_OUTPUT.emit(unsafe { from_raw_parts(bytes, len) });
}

pub const OUTPUT_HOOK: OutputHook = output_hook;
pub const STDOUT_OUTPUT_HOOK: OutputHook = stdout_output_hook;

#[cfg(test)]
#[path = "output_test.rs"]
mod output_test;
