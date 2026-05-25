---
purpose: "FileHandle = fd + dtor, exercising cstring/binary/integer marshal classes against real libc with an observable resource lifecycle"
paths: [jit, interp, aot]
budget.codegen.functions: 4
budget.codegen.instructions: 49
budget.specs.count: 4
budget.typer.worklist_pops: 7
budget.typer.walk_calls: 7
budget.typer.type_fn_calls: 4
budget.typer.matcher_specs: 0
budget.typer.vars: 48
budget.typer.blocks: 8
budget.typer.stmts: 24
budget.typer.dispatches: 2
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
