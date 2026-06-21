mod aot_link;
mod ast;
pub mod compiler2;
mod diag;
mod dispatch_matrix;
mod exec;
mod extern_contract;
mod function_surface;
mod fz_ir;
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
