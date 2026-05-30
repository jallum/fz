---
purpose: "runtime fz_binary_concat joins byte-aligned binaries across inline and ProcBin storage"
paths: [jit, interp, aot, repl]
oracle: oracle.exs
---

Exercises the runtime BIF that will back the `<>` operator desugar. The small
case stays inline; the long case crosses the shared-binary threshold and
therefore returns through the ProcBin path.
