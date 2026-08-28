mod aot_link;
mod ast;
pub mod compiler2;
mod diag;
mod dispatch_matrix;
mod exec;
mod extern_contract;
mod finite_set;
mod function_surface;
mod fz_ir;
pub mod ground_value;
mod ir_codegen;
mod ir_dce;
mod ir_interp;
mod modules;
mod parser;
mod runtime_type_predicate;
mod source;
mod telemetry;
mod type_expr;
pub mod types;

use libc::{c_int, close, write};

pub use function_surface::FunctionSurface;
/// Causal replay over a public telemetry log (fz-kdt.34.6). Re-exported at the
/// crate root because it reads the public ARTIFACT, not the compiler: the
/// integration tests and a future `fz2 trace-diff` consume a log file.
pub use telemetry::causal;
pub use telemetry::sink::NullTelemetry;

const FZ_EXEC_READY_FD_ENV: &str = "FZ_EXEC_READY_FD";

pub(crate) fn notify_fixture_execution_start() {
    let Ok(raw_fd) = std::env::var(FZ_EXEC_READY_FD_ENV) else {
        return;
    };
    let Ok(fd) = raw_fd.parse::<c_int>() else {
        return;
    };
    let byte = [1_u8];
    unsafe {
        let _ = write(fd, byte.as_ptr().cast(), byte.len());
        let _ = close(fd);
    }
}
