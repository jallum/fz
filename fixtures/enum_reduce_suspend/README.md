---
purpose: "Enum.reduce/3 suspend returns a real resumable closure at the runtime-value boundary"
paths: [jit, interp, aot, repl]
---

# enum_reduce_suspend

Pins the materialization boundary for `Enumerable.reduce_list/3` suspend:

```fz
Enum.reduce(xs, {:suspend, 0}, fn (x, acc) -> {:cont, acc + x})
```

The suspend clause returns `{:suspended, acc, fn () -> ... end}`. That closure
is a source value, not an internal native continuation edge, so it must remain a
real heap closure even as native call continuations become direct or lazy.

Target for native JIT/AOT:

- the three-element input list allocates three cons cells;
- the known zero-state reducer path boxes no scalar operands before reaching
  the suspend boundary;
- the returned suspend function allocates one closure;
- `closure_allocs = 1`;
- `closure_bytes = 48`.
