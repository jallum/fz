# multi_relay — paper walk under the proposed reducer

Ticket: `fz-jg5.1`-adjacent (one of the per-fixture paper walks under
the RED.0 spike umbrella). Goal: drive every callsite reachable from
program roots (main + spawned fns) through the seven reducer rules
**by hand**.

If a step requires a judgment call we haven't named, surface it in
§ Findings.

## The reducer rules, in one place

(See `red-0-ast-eval-paper-walk.md` for the canonical table.)
`dispatch`, `substitute`, `fold-prim`, `recurse`, `stop-opaque`,
`stop-non-decrease`, `stop-budget`.

Plus the boundary rules from `bodies-are-boundaries.md`:

- `receive()` is **always** a boundary; output is the mailbox type
  (`any` if untyped).
- `extern / FFI` is a boundary; output is declared (`any` if not).
- `spawn` of a value-flow closure with static captures **reduces**
  the lambda body in isolation; with opaque captures it emits a body.

## The source

```
fn worker(), do: send(1, receive() * 2)

fn main() do
  spawn(worker)
  spawn(worker)
  send(2, 10)
  send(3, 11)
  print(receive())
  print(receive())
end
```

Expected output:

```
20
22
```

## Process graph

```
       main (pid=1)
        |   |
   spawn|   |spawn
        v   v
    worker  worker
    (pid=2) (pid=3)

  main: send(2, 10) ---> worker(2).receive() -> 20
  main: send(3, 11) ---> worker(3).receive() -> 22
  worker(2): send(1, 20) ---> main.receive() -> 20
  worker(3): send(1, 22) ---> main.receive() -> 22
```

Two spawn sites, both spawning the **same** fn (`worker`). Two
mailboxes feed the two workers; each worker sends one message back to
main; main does two `receive()`s.

## Program roots

The reducer drives from:
- `main` (always a root)
- `worker` (root because it's a `spawn` target)

Each root reduces independently.

## Root 1: `main`

```
fn main() do
  spawn(worker)       # 1
  spawn(worker)       # 2
  send(2, 10)         # 3
  send(3, 11)         # 4
  print(receive())    # 5
  print(receive())    # 6
end
```

| Step | Rule | Detail |
|---|---|---|
| 1 | `spawn` (no captures) | `worker` is a top-level fn — `closure_lit` with empty captures. Captures are statically empty, so the lambda body **reduces in isolation** (see root 2). At main's level, this is an opaque extern call `spawn(<fn_ref worker>)` returning a pid Descr; leave in place. |
| 2 | same as 1 | second `spawn(worker)` — same treatment. |
| 3 | extern call | `send(2, 10)` — both args are literal Descrs. `send` is an extern; the call body cannot be folded by the reducer. Leave in place as `send(int_lit(2), int_lit(10))`. |
| 4 | extern call | `send(3, 11)` — same as 3, leave in place. |
| 5 | `receive()` boundary | `receive()` is a boundary; produces an opaque Descr `any` (mailbox untyped). The result flows into `print(...)` — another extern; leave in place. |
| 6 | `receive()` boundary | same as 5. |

**Reduced main:** identical to source. No call dissolved; no body
emitted by main beyond `worker`'s own body (driven by root 2).

## Root 2: `worker`

```
fn worker(), do: send(1, receive() * 2)
```

Single clause, no args. The reducer dispatches to it (zero-arg
dispatch is trivial), then walks the body:

| Step | Rule | Detail |
|---|---|---|
| 2.1 | `dispatch` | zero-arg fn, one clause; `MatchedClause(0, {})`. |
| 2.2 | `receive()` boundary | `receive()` yields an opaque Descr `any`. |
| 2.3 | `fold-prim`? | `receive() * 2` — left input is opaque, right is `int_lit(2)`. `fold-prim` requires **all** inputs literal. **Does not fire.** Leave as `Prim::mul(any, 2)`. |
| 2.4 | extern call | `send(1, <mul result>)`. Args not all literal; leave in place. |

**Reduced worker body:** essentially the source. One boundary body
emitted for `worker`.

## Effect on the closure_lit at the spawn site

`spawn(worker)` desugars to `spawn(closure_lit(worker_fn, []))`. The
captures list is empty (literal), so the closure heap object dissolves
— spawn receives a static `fn_ref`. **No heap closure for worker.**

## main, after reduction

Identical to source (no callsite reduced away). One residual call to
`worker`'s emitted body — actually two, both via spawn.

## Bodies emitted

| Fn | Bodies | Why |
|---|---|---|
| `main` | 1 | always |
| `worker` | 1 | receive() is a boundary; mul has opaque input |

Total user bodies: **1** (worker). Matches the expected "one body per
boundary equivalence class."

## Findings

**The walk is mechanical end-to-end.** Every step is one of the named
rules. No judgment calls surfaced.

**The reducer does not attribute messages across processes.** It treats
each spawned fn as its own reduction root with its own `receive()`
boundary. The fact that main happens to send `10` and `11` is
**invisible** to the worker reducer — worker's `receive()` is opaque
regardless of what main sends, because there's no global mailbox-type
inference. (Typed mailboxes are explicitly deferred.) This is the
right call for v1.

**Both spawn sites share one worker body.** Same fn ref, same
(empty) captures — memo key collapses to the single (worker_fn, [])
entry. No body duplication.

**`receive()` × `* 2` does not constant-fold even though one operand
is literal.** `fold-prim` is all-or-nothing on operand literality. This
matches the design (set-theoretic Descrs aren't propagated into prim
folding for partial-literal cases in v1).

**Spawn with empty captures dissolves the closure heap object.** This
is the `static captures` case from the design note — and it applies
even when the "captures list" is empty (a top-level fn ref). worker
becomes a static thunk.
