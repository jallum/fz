use std::io::Write as _;
use std::slice::from_raw_parts;

use crate::scheduler_hooks::{ExpandHook, OutputHook, WarnHook};

/// What `IO.warn` reports: a message, and where it points when it has a
/// location. An empty `file` is no location.
pub struct Warning<'a> {
    pub message: &'a [u8],
    pub file: &'a [u8],
    pub line: u32,
}

impl Warning<'_> {
    /// The stderr form: `warning: <message>`, then `  <file>:<line>` when the
    /// warning is located.
    pub fn render(&self) -> Vec<u8> {
        let mut rendered = b"warning: ".to_vec();
        rendered.extend_from_slice(self.message);
        rendered.push(b'\n');
        if !self.file.is_empty() {
            rendered.extend_from_slice(b"  ");
            rendered.extend_from_slice(self.file);
            rendered.extend_from_slice(format!(":{}\n", self.line).as_bytes());
        }
        rendered
    }
}

/// What the compiler answers a macro body that asked it to expand a macro
/// call one step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Expansion {
    /// The call is no macro call, so it stays as written.
    NotAMacro,
    /// The call expands to this quoted code.
    Expanded(u64),
    /// The compiler has not answered yet: it will, and the macro body then
    /// runs again with the answer in hand.
    Asked,
    /// No compiler is running.
    NoCompiler,
}

impl Expansion {
    pub const NOT_A_MACRO_CODE: u64 = 0;
    pub const EXPANDED_CODE: u64 = 1;
    pub const ASKED_CODE: u64 = 2;
    pub const NO_COMPILER_CODE: u64 = 3;
}

pub trait OutputSink {
    fn emit(&self, bytes: &[u8]);

    /// Receive one `IO.warn`. Unless a sink says otherwise, a warning is
    /// written to stderr in one piece.
    fn warn(&self, warning: &Warning<'_>) {
        let _ = std::io::stderr().lock().write_all(&warning.render());
    }

    /// Answers a macro body's request to expand the macro call `ast` one step,
    /// standing in `context` (0 an expression, 1 a pattern, 2 a guard). Unless
    /// a sink says otherwise there is no compiler to ask.
    fn expand(&self, _ast: u64, _context: i64) -> Expansion {
        Expansion::NoCompiler
    }

    /// Hand everything emitted so far to its destination. Every end of a run
    /// calls this, so a final partial line is not lost.
    fn flush(&self) {}
}

pub struct NullOutput;

impl OutputSink for NullOutput {
    fn emit(&self, _bytes: &[u8]) {}

    fn warn(&self, _warning: &Warning<'_>) {}
}

pub struct StdoutOutput;

impl OutputSink for StdoutOutput {
    fn emit(&self, bytes: &[u8]) {
        let mut stdout = std::io::stdout().lock();
        let _ = stdout.write_all(bytes);
    }

    fn flush(&self) {
        let _ = std::io::stdout().flush();
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

unsafe extern "C" fn warn_hook(
    context: *const (),
    message: *const u8,
    message_len: usize,
    file: *const u8,
    file_len: usize,
    line: u32,
) {
    if context.is_null() {
        return;
    }
    let context = unsafe { &*(context as *const OutputContext<'_>) };
    context
        .0
        .warn(&unsafe { warning_from_raw(message, message_len, file, file_len, line) });
}

unsafe extern "C" fn stdout_warn_hook(
    _context: *const (),
    message: *const u8,
    message_len: usize,
    file: *const u8,
    file_len: usize,
    line: u32,
) {
    STDOUT_OUTPUT.warn(&unsafe { warning_from_raw(message, message_len, file, file_len, line) });
}

unsafe extern "C" fn expand_hook(context: *const (), ast: u64, expansion_context: i64, answered_ast: *mut u64) -> u64 {
    if context.is_null() {
        return Expansion::NO_COMPILER_CODE;
    }
    let context = unsafe { &*(context as *const OutputContext<'_>) };
    match context.0.expand(ast, expansion_context) {
        Expansion::NotAMacro => Expansion::NOT_A_MACRO_CODE,
        Expansion::Expanded(expanded) => {
            unsafe { *answered_ast = expanded };
            Expansion::EXPANDED_CODE
        }
        Expansion::Asked => Expansion::ASKED_CODE,
        Expansion::NoCompiler => Expansion::NO_COMPILER_CODE,
    }
}

unsafe fn warning_from_raw<'a>(
    message: *const u8,
    message_len: usize,
    file: *const u8,
    file_len: usize,
    line: u32,
) -> Warning<'a> {
    Warning {
        message: unsafe { from_raw_parts(message, message_len) },
        file: unsafe { from_raw_parts(file, file_len) },
        line,
    }
}

pub const OUTPUT_HOOK: OutputHook = output_hook;
pub const STDOUT_OUTPUT_HOOK: OutputHook = stdout_output_hook;
pub const WARN_HOOK: WarnHook = warn_hook;
pub const STDOUT_WARN_HOOK: WarnHook = stdout_warn_hook;
pub const EXPAND_HOOK: ExpandHook = expand_hook;

#[cfg(test)]
#[path = "output_test.rs"]
mod output_test;
