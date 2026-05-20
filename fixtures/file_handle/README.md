---
purpose: "FileHandle = fd + dtor, exercising cstring/binary/integer marshal classes against real libc with an observable resource lifecycle"
paths: [jit, interp, aot]
---

# file_handle

[[fz-x5m]] / [[fz-4mk]] — End-to-end demonstration of the extern marshal
classes plumbed through `make_resource`.

```
libc::creat (path :: cstring, mode :: integer)  :: integer
libc::write (integer, binary, integer)          :: integer
libc::close (integer)                           :: integer
libc::unlink(cstring)                           :: integer
```

The fixture wraps the fd in a `FileHandle` resource whose dtor calls
`libc::close` and then prints `:dtor_closed`. The dtor body runs as
real fz code at task-exit drain (fz-4mk) — the closure isn't picked
apart for an extracted C symbol; the wrapper's `print` actually fires.
The `:dtor_closed` line at the end of expected.txt is what proves the
destructor ran.
