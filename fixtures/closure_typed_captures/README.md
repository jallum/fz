---
purpose: "fz-ul4.29.5 — closure dispatched via call_indirect through stub_fp"
paths: [jit, interp, aot, repl]
budget.codegen.functions: 5
budget.codegen.instructions: 155
budget.specs.count: 5
budget.typer.worklist_pops: 9
budget.typer.walk_calls: 9
budget.typer.type_fn_calls: 5
budget.typer.matcher_specs: 0
budget.typer.vars: 26
budget.typer.blocks: 6
budget.typer.stmts: 10
budget.typer.dispatches: 3
---

# closure_typed_captures

fz-ul4.29.5 — closure dispatched via call_indirect through stub_fp

## Notes

fz-ul4.27.22.11 — apply1's `f(z)` resolves via closure_lit to lambda_3's
narrow body spec; the cl+16 indirect dispatch is replaced by a direct
return_call.
fz-ul4.27.22.5 — typed closure capture seam: ishl/bor pairs dropped at the
MakeClosure producer (add_to_s6) and sshr_imm dropped at the body's typed
capture loads (lambda_3_s8 captures v3/v4 are RawInt, no untag needed).
fz-ul4.27.22.12 — closure_lit-driven per-callsite specialization splits
lambda_3 into a narrow `[10, 20, 12]` spec and a wide `[10, 20, any]`
fallback. The narrow spec used at runtime gets full RawInt ABI; the wide
is unused by main's flow but emitted for the any-key fallback.
fz-cps.1.12: closure stubs deleted. The lambda body is invoked
directly via Tail-CC `return_call_indirect` through cl+16 — no stub
fn exists to assert about. Tracked by §8.3 acceptance test.

A closure capturing two ints + invoked. Under .29.5, the closure heap
object stores stub_fp at payload offset 16; MakeClosure computes its
address via func_addr; CallClosure loads stub_fp and call_indirect-s
through it. The fz_closure_invoke / fz_closure_arg runtime helpers no
longer exist.

fz-ul4.29.8 — the lambda's body is leaf (Return only, no parking),
so post-.29.8 it becomes natively-callable. The stub for
`lambda_3` (the inner closure target, 2 captures) no longer
allocates a frame; it loads captures from the closure heap object
and directly calls the native body (no `fz_alloc_frame` for the stub).
