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
mod tests {
    use super::*;
    use std::cell::{Cell, RefCell};

    struct BorrowCapture {
        pointer: Cell<*const u8>,
        len: Cell<usize>,
    }

    impl OutputSink for BorrowCapture {
        fn emit(&self, bytes: &[u8]) {
            self.pointer.set(bytes.as_ptr());
            self.len.set(bytes.len());
        }
    }

    #[test]
    fn output_hook_passes_the_original_event_scoped_bytes() {
        let sink = BorrowCapture {
            pointer: Cell::new(std::ptr::null()),
            len: Cell::new(0),
        };
        let context = OutputContext::new(&sink);
        let bytes = b"raw output";

        unsafe { OUTPUT_HOOK(context.as_ptr(), bytes.as_ptr(), bytes.len()) };

        assert_eq!(sink.pointer.get(), bytes.as_ptr());
        assert_eq!(sink.len.get(), bytes.len());
    }

    struct RetainingCapture(RefCell<Vec<Vec<u8>>>);

    impl OutputSink for RetainingCapture {
        fn emit(&self, bytes: &[u8]) {
            self.0.borrow_mut().push(bytes.to_vec());
        }
    }

    #[test]
    fn retaining_sink_owns_its_copy_after_the_callback() {
        let sink = RetainingCapture(RefCell::new(Vec::new()));
        let context = OutputContext::new(&sink);
        {
            let bytes = Vec::from(&b"retained"[..]);
            unsafe { OUTPUT_HOOK(context.as_ptr(), bytes.as_ptr(), bytes.len()) };
        }

        assert_eq!(sink.0.borrow().as_slice(), &[b"retained".to_vec()]);
    }

    #[test]
    fn missing_output_context_does_not_invoke_a_sink() {
        unsafe { OUTPUT_HOOK(std::ptr::null(), b"ignored".as_ptr(), 7) };
    }

    #[test]
    fn null_output_does_not_retain_event_bytes() {
        let context = OutputContext::new(&NullOutput);
        unsafe { OUTPUT_HOOK(context.as_ptr(), b"ignored".as_ptr(), 7) };
    }
}
