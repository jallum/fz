//! The boundary between compiling a program and running it.
//!
//! Both engines announce it immediately before the root process starts: the
//! JIT before the runtime spawns the entry, the backend interpreter before it
//! enqueues one. `fz2 test` reaches the same seam once per test, inside the
//! child process that runs it.
//!
//! The boundary is a telemetry event, emitted whether or not anything is
//! listening. The descriptor named by `FZ_EXEC_READY_FD` is one consumer of
//! it: a harness passes the write end of a pipe there and learns, from the
//! single byte written here, that everything still ahead of the process is the
//! program itself.

use libc::{c_int, close, write};

use crate::telemetry::{Telemetry, TelemetryExt as _};

const FZ_EXEC_READY_FD_ENV: &str = "FZ_EXEC_READY_FD";

/// Announces that compilation and code generation are behind the caller and
/// the program starts now.
pub(crate) fn signal_execution_ready<T: Telemetry + ?Sized>(tel: &T) {
    tel.raw_event0(&["fz", "runtime", "execution_ready"]);
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
