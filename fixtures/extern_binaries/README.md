---
purpose: "extern binary/cstring marshal classes round-trip through libc open/write/close"
paths: [jit, interp, aot]
---

# extern_binaries

[[fz-vw1]] — End-to-end exercise of the `cstring` and `binary` extern
marshal classes from [[fz-0cv]] and the runtime helpers from [[fz-9ss]],
across all three execution paths.

The fixture opens `/dev/null` for write (cstring path), writes five
bytes to the fd (binary path), and closes the fd. Two thin libc shims
in `runtime/src/libc_io.rs` do the actual `open`/`write`/`close` work
and convert libc's raw return values into tagged `FzValue::Int`s so
the fz side reads them like every other extern result.

A successful round-trip prints `1`.
