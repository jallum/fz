---
purpose: "fz-recv epic acceptance — selective receive across two pinned refs with out-of-order replies + after timeout"
paths: [interp, jit, aot]
repl-skip: "fz-dt3.7 — eval::Interp cannot park selective receives or resume from sender-side matcher hits"
budget.codegen.functions: 14
budget.codegen.instructions: 459
budget.specs.count: 11
budget.typer.worklist_pops: 24
budget.typer.walk_calls: 24
budget.typer.type_fn_calls: 11
budget.typer.matcher_specs: 0
budget.typer.vars: 83
budget.typer.blocks: 13
budget.typer.stmts: 30
budget.typer.dispatches: 4
---

# receive_selective_refs

Acceptance fixture for selective receive (see `guides/processes.html`).
Pins sender-side matcher miss + hit and receiver-side initial-scan hit
in a single trace.

## What it exercises

| Path | Where in the trace |
|---|---|
| Sender-side matcher **miss** | ref_a reply arrives while main is parked on ref_b. Server invokes main's matcher; pattern's `^ref_b` does not match ref_a; message stays in mailbox. |
| Sender-side matcher **hit** | ref_b reply arrives. Server invokes main's matcher; `^ref_b` matches; v is bound; clause body resolved; main wakes pre-resolved via `ResumeMatched`. |
| Receiver-side scan **hit** | Main's second `receive` (on ref_a) walks the mailbox at entry, finds the ref_a reply already there, matches without parking. |
| Pinned variables | `^ref_a`, `^ref_b`. |
| `make_ref` | Both refs. |
| `after` clause | 500 ms timeout on the first receive (does not fire in a healthy run; presence exercises the parse + park-record + timer paths). |

## Expected output

```
3
```

The server echoes integer keys back as the reply payload, so `val_a == 1`
and `val_b == 2`.

## Three-path parity

The fixture is run through interpreter, JIT, and AOT; all three must
produce identical printed output. The README budget frontmatter keeps
compiler output shape from growing unexpectedly without committing the full
generated dumps.
