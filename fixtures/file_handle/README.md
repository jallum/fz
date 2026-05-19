---
purpose: "FileHandle = fd + dtor, exercising cstring/binary/integer marshal classes against real libc with an observable resource lifecycle"
paths: [jit, interp, aot]
---

# file_handle

[[fz-x5m]] — End-to-end demonstration of the extern marshal classes
plumbed through `make_resource` from fz-swt.

```
libc::creat (path :: cstring, mode :: integer)  :: integer
libc::write (integer, binary, integer)          :: integer
libc::unlink(cstring)                           :: integer
```

The destructor is `fz_test_close_fd` (defined in `runtime/src/resource.rs`
for fz-swt's own resource fixture). It fcntl-verifies the fd is open,
calls libc::close, fcntl-verifies the fd is now closed by the kernel,
and prints exactly `dtor:closed` on success or `dtor:failed(<reason>)`
on any check failure. The `:dtor_closed` line at the end of expected.txt
is what proves the destructor actually ran.

## Why not `&libc::close/1` here?

The architectural answer is that `&libc::close/1` *is* the correct
shape — the runtime's `resolve_dtor_from_closure` extracts the wrapper
closure's canonical `Prim::Extern` and invokes that C symbol directly.
Anything else in the wrapper body (e.g. a `print` for the test golden)
is never executed; the runtime cannot run CPS-shaped fz IR from a raw
`fn(u64)` callback.

So with `&libc::close/1` the dtor really does call libc's `close` — we
just can't *observe* it from inside the fixture. `fz_test_close_fd` is
the observable variant: same lifecycle, same Prim::Extern-extraction
path, but a dtor that prints the proof.
