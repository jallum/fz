---
purpose: "fz-swt.13 / fz-4mk — File module wraps an fd in a resource; the dtor closes the fd at task-exit drain (interp/JIT/AOT parity)."
paths: [interp, jit, aot, repl]
budget.codegen.functions: 3
budget.codegen.instructions: 35
budget.specs.count: 3
budget.typer.worklist_pops: 4
budget.typer.walk_calls: 4
budget.typer.type_fn_calls: 3
budget.typer.matcher_specs: 0
budget.typer.vars: 37
budget.typer.blocks: 7
budget.typer.stmts: 17
budget.typer.dispatches: 2
---

# file_resource_lifecycle

fz-swt.13 / fz-4mk — first real customer of the resource mechanism: a
`File` module that wraps a Unix file descriptor in an
`opaque resource(integer)` and registers `&File.dtor/1` as its
destructor. The dtor calls `libc::close` directly and prints
`:dtor_closed` for observability.

## Scope

The epic sketch showed `extern "C" fn fd_open(path :: cstring, mode :: cstring)`
and a `File.open(path, mode)` entry point. This fixture stays focused on
the *resource lifecycle*: fz code creates a temporary fd through libc,
wraps that raw integer fd, unlinks the path, and proves the dtor fires.

Surface:

  * `File.wrap_fd(integer) :: t` — adopt an already-open fd as a resource.
  * `File.fd_of(t) :: integer` — in-module accessor.
  * `File.dtor(fd)` — fz fn body that calls `libc::close(fd)` and prints
    `:dtor_closed`. Used via `&File.dtor/1` as the dtor closure.

## What the fixture proves

  1. `File.wrap_fd/1` allocates a `Resource` whose dtor closure is
     `&File.dtor/1` — an in-module fn ref. The closure body runs as
     real fz code at task-exit drain (fz-4mk), proving that resource
     dtors are no longer restricted to thin wrappers around a single C
     extern; the wrapper can do real work and have side effects.
  2. The fd is observably alive between `wrap_fd` and `main` returning.
     The path is unlinked by fz code before exit so the kernel reclaims
     the file after the resource dtor closes the fd.
  3. Output ordering is identical across all three legs:

         opened
         before
         :dtor_closed

     The first two lines come from `main`. The `:dtor_closed` line
     comes from the scheduler's pending-dtor drain at task exit, after
     `main` returns — matching the ordering contract pinned by
     `fixtures/resource_aot_dtor` and `fixtures/resource_lifecycle`.

## Verification mechanics

The dtor body is just:

```fz
fn dtor(fd) do
  libc::close(fd)
  print(:dtor_closed)
end
```

`libc::creat`, `libc::unlink`, and `libc::close` are ordinary externs.
The `print(:dtor_closed)` is the witness that the dtor body fully
executed — under the old extracted-Prim::Extern path it would have
been silently dead code.
