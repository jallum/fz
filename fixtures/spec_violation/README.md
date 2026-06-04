---
purpose: "a wrong @spec is rejected with a spec/violation diagnostic on every path"
paths: [interp, jit, aot, repl]
expect: diagnostic
diagnostic.code: spec/violation
---

# spec_violation

`M.add1` declares `@spec add1(float) :: float` but its body adds `1` to an int
argument. The shared spec-validation pass rejects this at compile time with a
`spec/violation` diagnostic. The same pass runs in every driver, so the verdict
is invariant across the four paths; the fixture pins the diagnostic through the
`[fz, diag, error]` telemetry event.
