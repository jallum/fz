---
purpose: "fz-swt.13 — File module wraps an fd in a resource; the dtor closes the fd at heap drop (interp/JIT/AOT parity)."
paths: [interp, jit, aot]
---

# file_resource_lifecycle

fz-swt.13 — first real customer of the resource mechanism: a `File`
module that wraps a Unix file descriptor in an `opaque resource(integer)`
and registers `close(2)` as its destructor.

## Scope (descope from epic sketch)

The epic sketch showed `extern "C" fn fd_open(path :: cstring, mode :: cstring)`
and a `File.open(path, mode)` entry point. That signature requires the
`ExternTy::CString` marshal class (**fz-0cv**), which itself depends on
the +1-NUL invariant tracked by **fz-wu9**. Neither ticket is in this
epic's DAG. Rather than scope-creep the cstring FFI in here, this ticket
authorizes a minimum surface that exercises the dtor mechanism end-to-end:

  * `File.wrap_fd(integer) :: t` — adopt an already-open fd as a resource.
  * `File.fd_of(t) :: integer` — in-module accessor (proves opaque-visibility
    on the read side; not used by the fixture itself but kept for shape
    parity with the epic sketch).

The fd is produced by a runtime test helper (`fz_test_open_tmpfile`) that
`mkstemp`s a tmpfile and immediately unlinks the path, so no filesystem
cleanup is required even if the dtor leaks. `File.open(path, mode)` is the
v1 surface and will land once fz-wu9 + fz-0cv ship.

## What the fixture proves

  1. `File.wrap_fd/1` allocates a `Resource` whose dtor closure
     (`&File.dtor/1`) wraps the C extern `fz_test_close_fd`. The dtor-
     resolution path used by interp / JIT / AOT (see
     `resolve_dtor_from_closure` in `src/ir_interp.rs`) finds the
     `Prim::Extern` inside the in-module wrapper exactly as it does for
     top-level wrappers — proving the resource subsystem doesn't care
     where the wrapper lives.
  2. The fd is observably alive between `wrap_fd` and `main` returning:
     `fz_test_close_fd` first asserts the fd is open via `fcntl(fd, F_GETFD)`
     before closing it. If the fd had been double-closed or never opened,
     the dtor would print `dtor:failed` and the fixture would diverge.
  3. After the dtor runs `close(2)`, it re-checks the fd with `fcntl`
     and asserts the result is `-1` with `EBADF`. Only then does it
     print `dtor:closed`. The single line of dtor output therefore
     witnesses both the lifecycle (dtor fired exactly once) and the
     semantics (fd is genuinely closed, not just released).
  4. Output ordering is identical across all three legs:

         opened
         before
         dtor:closed

     The first two lines come from `main`. The `dtor:closed` line comes
     from the MSO sweep at process heap drop, which fires after `main`
     returns — matching the ordering contract pinned by
     `fixtures/resource_aot_dtor` and `fixtures/resource_lifecycle`.

## Verification mechanics

`fz_test_close_fd(payload: u64)` (in `runtime/src/resource.rs`):

  * Unboxes `payload` as `FzValue::Int` to recover the raw fd.
  * Calls `fcntl(fd, F_GETFD)` and stores the result — `-1` here means
    the dtor was handed a stale fd.
  * Calls `close(fd)` and stores the return.
  * Calls `fcntl(fd, F_GETFD)` again — the post-close call must return
    `-1` with `errno == EBADF`, otherwise the kernel disagrees with us
    about whether the fd is closed.
  * Prints `dtor:closed` iff all three checks pass; otherwise prints a
    diagnostic that includes which check failed so a regression surfaces
    in the golden diff rather than silently passing.

The `fz_test_open_tmpfile()` helper opens a temp file (via `mkstemp`)
and immediately `unlink`s the path so the test never leaves files on
disk regardless of how the dtor behaves.
