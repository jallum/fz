# three_process_chain — paper walk under the proposed reducer

Drive every callsite reachable from program roots through the seven
reducer rules.

## The reducer rules

See `red-0-ast-eval-paper-walk.md`. Plus boundary rules: `receive()`
always stops; extern always stops; spawn-with-static-captures reduces
the lambda body in isolation.

## The source

```
fn first_relay() do
  send(3, receive() + 1)
end

fn second_relay() do
  send(1, receive() + 1)
end

fn main() do
  spawn(first_relay)
  spawn(second_relay)
  send(2, 40)
  print(receive())
end
```

Expected output: `42`.

## Process graph

```
   main (pid=1)
     |
     | spawn first_relay -> pid=2
     | spawn second_relay -> pid=3
     | send(2, 40)
     v
   first_relay (pid=2)
     mbox <- 40
     send(3, 40 + 1 = 41)
     v
   second_relay (pid=3)
     mbox <- 41
     send(1, 41 + 1 = 42)
     v
   main mbox <- 42
   print(receive()) -> 42
```

The runtime chain is **invisible** to the reducer. Each fn reduces in
isolation against opaque mailbox contents.

## Program roots

`main`, `first_relay`, `second_relay`.

## Root 1: `main`

| Step | Rule | Detail |
|---|---|---|
| 1 | spawn (empty captures) | `spawn(first_relay)` — closure dissolves (top-level fn ref, no captures). Spawn is an extern returning pid; leave call in place. |
| 2 | spawn (empty captures) | `spawn(second_relay)` — same. |
| 3 | extern | `send(2, 40)` — both literal; extern call left in place. |
| 4 | receive boundary | `receive()` opaque; result feeds `print` extern. Leave both in place. |

**Reduced main:** same as source. No user calls dissolved.

## Root 2: `first_relay`

```
fn first_relay() do
  send(3, receive() + 1)
end
```

| Step | Rule | Detail |
|---|---|---|
| 2.1 | dispatch | one clause, zero args; trivial. |
| 2.2 | receive boundary | `receive()` opaque (`any`). |
| 2.3 | fold-prim? | `receive() + 1` — left opaque, right `int_lit(1)`. Mixed; fold-prim does not fire. |
| 2.4 | extern | `send(3, <add>)` — leave. |

**Reduced body:** source-identical. One body emitted.

## Root 3: `second_relay`

Structurally identical to `first_relay` (only the destination pid
literal differs: `1` instead of `3`). Same outcome — one body emitted.

## Bodies emitted

| Fn | Bodies |
|---|---|
| `main` | 1 |
| `first_relay` | 1 |
| `second_relay` | 1 |

Three boundary bodies (one per source-level fn). None get dissolved
because each has a `receive()` boundary.

## Findings

**No cross-process inference.** The reducer cannot see that
first_relay's receive will produce `int_lit(40)` because main sent
`40` to pid=2. The mailbox type is `any`. This is fine — typed
mailboxes (deferred) would fix this if we wanted the chain to
constant-fold all the way to `print(42)`.

**Two distinct spawned fns ⇒ two distinct memo keys.**
`first_relay` and `second_relay` share **no structure** at the
reducer level — they're separate top-level fns. The reducer does
not deduplicate them (and shouldn't; that's the source-level author's
choice).

**Same shape as multi_relay.** Both fixtures end up with N+1 user
bodies (one per spawned fn + main). The reducer doesn't unify
identical bodies; that's a later optimization or a source-level
refactor.

**Hard mechanical walk** — no judgment calls.
