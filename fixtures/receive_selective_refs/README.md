---
purpose: "fz-recv epic acceptance — selective receive across two pinned refs with out-of-order replies + after timeout"
paths: [interp, jit, aot]
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
{:k_a, :k_b}
```

(The server echoes the key back as the reply payload, so `val_a == :k_a`
and `val_b == :k_b`.)

## Three-path parity

The fixture is run through interpreter, JIT, and AOT; all three must
produce identical printed output. The CLIF golden (`expected.clif`) is the
JIT/AOT lowering target; specs (`expected.specs`) is the front-end output.
Both will be blessed when the implementation lands.
