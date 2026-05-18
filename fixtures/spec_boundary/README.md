---
purpose: "fz-jg5.12 (RED.9) — @spec is a reduction boundary; fact has 1 body, not 0"
paths: [jit, interp]
---

# spec_boundary

fz-jg5.12 (RED.9) — declaring `@spec fact(integer) :: integer` tells
the reducer to honor `fact` as a contract. Without the spec, the
reducer would fold `fact(5)` to the literal `120` and emit no body;
with the spec, `fact` survives as a single emitted body and `main`
calls it.

Compare against `multi_clause`, which `fact`s without an `@spec` and
demonstrates the reducer collapsing the call.

## Notes

         runs identically on interp, jit, aot
