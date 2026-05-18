# spawn_with_captures — paper walk

Ticket: `fz-jg5.1` (SPIKE — verify reducer on spawn-with-opaque-capture).

This walkthrough exercises the **spawn-with-opaque-capture** branch:
the spawned lambda captures `tag`, which is a parameter of an enclosing
user function. Whether the capture is "opaque" depends on whether the
**call to that enclosing function** is reduced statically.

## The source

```
fn parent(tag) do
  spawn(fn () -> send(1, tag))
  receive()
end

fn main() do
  print(parent(99))
end
```

## Pre-reducer call graph from main

```
main
└── parent(99)
      ├── spawn(λ_send)             (extern)
      │     └── λ_send : captures=[tag] body=send(1, tag)
      │           └── send(1, tag)  (extern)
      └── receive()                  (extern — boundary)
```

`spawn`, `send`, `receive` are extern primitives. `print` is an
extern. Only `parent/1` is a user function.

## Call 1 — `parent(99)`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.1 | dispatch | `parent/1` has one clause with head `tag` (no guard) → bind `tag := 99` (literal int Descr) | 1 |
| 1.2 | substitute | body becomes: `spawn(fn () -> send(1, 99)); receive()` — the literal `99` substitutes into the lambda's free variable `tag` | 1 |

After substitution, the lambda's captures collapse from `[tag]` (one
opaque-at-definition-site capture) to `[]` after capture-substitution
with the literal `99`. **This is the key reduction step for this
fixture**: the capture is opaque from the lambda's *own* perspective,
but the **calling context** supplies a literal, and the reducer
substitutes through.

### Sub-call 1.a — `spawn(fn () -> send(1, 99))`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.a.1 | (closure_lit reduce, RED.5) | captures = `[]` after substitution. λ body = `send(1, 99)`. Lift to static thunk. | 2 |
| 1.a.2 | (extern passthrough) | `spawn(THUNK_send_1_99)` — extern, leave the call. | 2 |

The lambda body's `send(1, 99)` is the residual inside the thunk —
itself a boundary (extern call), so it stays as the thunk's emitted
body.

### Sub-call 1.b — `receive()`

| Step | Rule | Detail | Counter |
|---|---|---|---|
| 1.b.1 | stop-opaque | mailbox is untyped; output Descr `any`; cannot fold | 2 |

`receive()` stays. The receive-cont in `parent` is "return the
received value to the caller of `parent`."

### Back to call 1 — reduced body of `parent(99)`

```
spawn(THUNK_send_1_99)
return receive()
```

This residual replaces the literal `parent(99)` callsite in main.

## Call 2 — `print(parent(99))` after substitution

After call 1's reduction, main becomes:

```
fn main() do
  spawn(THUNK_send_1_99)
  print(receive())
end
```

The `receive()` inside what was `parent` has lifted (via inline-as-
reduction) into main. `print(receive())` remains: `receive` is the
boundary, `print` is the receive-cont consumer.

## main, after reduction

```
fn main() do
  spawn(THUNK_send_1_99)
  print(receive())
end
```

Plus one residual top-level function:

```
fn THUNK_send_1_99() do
  send(1, 99)
end
```

User functions emitted: **zero** bodies for `parent` (fully
substituted away), one synthetic top-level thunk for the spawn target.

## Findings

**Boundary count: 1 user-visible.**

1. **`receive()` in main (lifted from `parent`)** — *boundary type:*
   untyped receive. *Annotation that would narrow:* typed mailbox
   (`fz-ul4.19`). With `@mailbox int`, the receive cont's output is
   `int`, and the path to `print` is typed.

**Capture substitution is the load-bearing step.** The lambda is
defined with one capture (`tag`). Whether that capture is "static" or
"opaque" is determined **at the call site of the enclosing function**.
Here `parent(99)` has a literal argument, so the substitute rule
turns the capture into a literal **before** closure_lit reduction
runs. Result: zero-capture thunk, no heap closure object.

**If `parent` were called with an opaque tag** — e.g.
`fn main() do print(parent(receive())) end` — the substitute rule
would not produce a literal. The lambda's `tag` capture would stay
opaque. closure_lit reduction would **not** lift to a static thunk;
instead a body for the lambda would be emitted, parameterised over
`tag`, and a heap closure object would be allocated at the spawn
site to carry the runtime `tag` into the spawned task. This is the
"opaque captures keep the closure on the heap" branch of the design
note.

**Reducer + spawn compose cleanly via two passes at the spawn site.**
First, substitute the caller's literal args into the lambda's free
variables (the standard substitute rule, applied to closure bodies
too). Second, if the lambda's residual capture set is empty, lift to
a static thunk; else emit a boundary body for the lambda. The first
pass is the seven-rule reducer applied to closure bodies; the second
is RED.5's special-cased lifting.

**Judgment call — receive-cont capture interaction with the reducer.**
The receive-cont in main (after `parent` is inlined) captures
nothing — it's just `λ msg -> print(msg)`. If `parent` had been
written as `fn parent(tag) do x = receive(); send(1, tag + x); 0 end`,
the receive-cont would capture `tag`. The reducer's substitute rule
would still fire on `parent(99)` and substitute `tag := 99` into the
cont's body before emitting it. **The cont's body is just another
expression and obeys the same substitute rule.** No new mechanism is
required.

**Spike outcome: GO.** Substitution composes through closure
captures and cont captures alike. No new rules surfaced.
