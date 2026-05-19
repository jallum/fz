---
purpose: "FileHandle = fd + libc::close dtor, exercising cstring/binary/integer marshal classes against real libc"
paths: [jit, interp, aot]
---

# file_handle

[[fz-x5m]] — End-to-end demonstration of the extern marshal classes
plumbed through `make_resource` from fz-swt. No runtime-side shims:
the fixture declares libc functions directly and wraps the returned
file descriptor as an `opaque resource(integer)` with `&libc::close/1`
as the destructor.

```
libc::creat(path :: cstring, mode :: integer) :: integer
libc::write(integer, binary, integer)         :: integer
libc::close(integer)                          :: integer
libc::unlink(cstring)                         :: integer
```

When the wrapped handle drops at end-of-scope, the runtime's MSO sweep
invokes the dtor closure synthesized by `&libc::close/1`, which calls
libc's real `close` on the wrapped fd.
