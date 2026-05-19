---
purpose: "TailCallClosure with captured singleton closure-lit preserves narrow arg ABI through recursive HOF"
paths: [jit, interp, aot, repl]
---

# tailcall_closure_captures

Recursive higher-order call through a captured closure-lit must pass the
list element to the lambda body in the lambda's narrow representation.
