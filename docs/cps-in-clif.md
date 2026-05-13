# CPS-in-clif — Design Doc

Status: **design**, pre-implementation. Single source of truth for the CPS-in-clif epic.
Tickets (`fz-cps.*`) reference sections of this document by anchor.

## §1. Premise

fz-IR is already canonical CPS: `Term::Call` carries an explicit `Cont { fn_id, captured }`.
The runtime ABI, however, is not — continuations live in heap frame slot 0, every fz fn
threads a `frame_ptr` parameter, and a trampoline (`CompiledModule::run_quantum`)
dispatches frames by schema id.

The proposal collapses to one sentence:

> **Promote `cont` from a frame slot to a function parameter, and use `return_call*`
> for every fz→fz transfer.**

Everything else in this document follows mechanically.

## §2. Model

### §2.1. Function shapes

Three kinds of callable, each with a fixed signature shape. All use Cranelift
`CallConv::Tail`.

| Kind | Signature | Invocation |
|---|---|---|
| **Regular fn** (top-level, no captures) | `(args..., k: i64)` | Direct: `return_call %fn(args..., k)` |
| **Closure** (any fn-as-value) | `(args..., self: i64, k: i64)` | Indirect: `v_code = load f+16; return_call_indirect sig, v_code(args..., f, k)` |
| **Continuation** (a cont closure) | `(result: i64, self: i64)` | Indirect: `v_code = load k+16; return_call_indirect sig_cont, v_code(result, k)` |

`self` is the closure pointer itself. The callee loads its captures from
`self + 24, +32, ...` (past the 16-byte `HeapHeader` and 8-byte `code_ptr`).

A continuation has no separate `k` parameter — its "next k" lives in its captures,
because the cont was constructed at a known site by code that knew what came next.

### §2.2. Closure object layout

Unchanged from the current runtime (`runtime/src/heap.rs:297-316`):

```
offset 0  : HeapHeader { kind, flags, size_bytes, schema_id, _reserved }   (16B)
offset 16 : code_ptr                                                        (8B)
offset 24 : captures[0]                                                     (8B each)
offset 32 : captures[1]
...
```

A **continuation is a closure** — same layout, same allocator, same GC path. We
do not introduce a new heap type.

### §2.3. Discipline

The model is summarized by four invariants:

1. **Every fz→fz transfer is a tail call** (`return_call` for known callees,
   `return_call_indirect` for closures and conts).
2. **`cont` is always a parameter, never a memory slot** in the calling
   convention. Memory storage of a cont occurs only at the parking site
   (§4) and via cross-process copy (§5).
3. **A continuation invokes nothing but its captured next-step** — every cont
   body ends in a `return_call*`.
4. **The current `cont` parameter is the *only* GC root that anchors live
   data on the call chain** (§7).

### §2.4. Halt continuation

A static singleton closure `@halt_stub`:

```
%halt_stub:
  block0(_r: i64, _self: i64):
    call %fz_task_exit()
    trap unreachable
```

Module init allocates one `@halt_stub` per module (zero captures). `Runtime::spawn`
hands every new task a reference to this singleton as its initial `k`.

## §3. Escape rule (proof obligation)

A continuation closure `K` allocated at site `S` is **stack-allocatable** iff every
CFG path from `S` to `K`'s invocation contains no occurrence of an escape-inducing
operation; otherwise **heap-allocated**.

**Escape-inducing operations** — exactly this closed set:

- `Term::Receive` — parks the current continuation into the process's parked-cont slot.
- `spawn(closure)` — deep-copies the closure into a new task's heap.
- `send(_, msg)` — copies the message through the scheduler's mailbox.
- Store into heap-resident data (`Prim::StoreField` and friends).

### §3.1. Per-Term obligation

| Term | Allocates a cont? | Escape contribution |
|---|---|---|
| `Term::Goto target` | No | Flow into `target`. |
| `Term::If { then, else }` | No | Meet of both arms. |
| `Term::Call { fn, args, cont }` | Yes | Escapes iff the callee's `escapes_cont` bit is `true`. |
| `Term::TailCall { fn, args }` | No | Forwards current `k`. |
| `Term::CallClosure { f, args, cont }` | Yes | Conservatively `true` unless target is statically known. |
| `Term::TailCallClosure { f, args }` | No | Forwards current `k`. |
| `Term::Return v` | No | Indirect-invokes caller-provided `k`. |
| `Term::Halt v` | No | No alloc. |
| `Term::Receive { cont, captured }` | Yes | **ESCAPE** — canonical promotion site. |

| Prim | Escape contribution |
|---|---|
| `spawn` | Closure escapes (cross-task deep copy). |
| `send` | Message escapes (mailbox copy). |
| `StoreField` and other heap-write prims | Stored value escapes. |
| arithmetic, compare, alloc-float/int, print | None. |

**Per-function summary bit.** `escapes_cont: bool` computed as a fixed-point: `true`
iff the body contains any escape-inducing op on a path that does not pre-emptively
invoke the cont.

**Exhaustiveness.** The two tables enumerate every `Term` and every escape-relevant
`Prim`. Closures created in non-Term positions (`MakeClosure`) escape iff they are
passed into an escape op, which is covered by the same rule.

### §3.2. v1 conservative shortcut

Until the modular `escapes_cont` analysis lands, **any function whose body contains
any of `Receive` / `spawn` / `send` / store-to-heap heap-allocates *all* its conts**.
All other functions ... also heap-allocate their conts (see §3.3). The rule is
documentation of the correctness argument; the *placement* in v1 is uniform.

### §3.3. Why all conts are heap-allocated in v1

Cranelift 0.131's `stack_slot` is invalidated by `return_call*` — the caller's stack
frame (slots included) is popped before the callee runs, so a stack-slot address
passed as an argument dangles in the callee. The "stack-allocate non-escaping conts"
optimization therefore requires a custom bump region in a callee-saved register —
hand-rolled ABI work, not a Cranelift primitive. It is **deferred** to a future
optimization ticket (§9.opt1).

v1 heap-allocates every cont in the process-local arena (§6). Allocation cost is
one bump-pointer add; reclamation cost is amortized into the next GC. The escape
rule of §3 is preserved as the correctness argument and as the basis for the
future stack tier.

## §4. Receive

`Receive` is the canonical promotion site. It does not need a parking-frame
schema; it stores the current cont parameter into the process's parked-cont slot.

```
fn caller(... , k):
  ;; build receive cont (heap-alloc; caller's body contains Receive → §3.2)
  v_k1 = call %fz_alloc_closure(iconst.i32 N)
  store @after_receive, v_k1+16
  store ...captures..., v_k1+24, +32, ...
  return_call %fz_receive_park(v_k1)
```

`fz_receive_park(cont) -> noreturn`:
1. Stores `cont` into `Process::parked_cont`.
2. Sets `Process::state = Blocked`.
3. Returns control to the scheduler.

On message arrival, the scheduler:
1. Pulls a message from `Process::mailbox`.
2. Tail-calls `cont.code(msg, cont)` via a thunk in the runtime.

There is no parking frame schema. There is no slot-0 cont. The parked task's
entire continuation is one closure pointer.

## §5. Spawn

`Runtime::spawn(closure)` is a direct entry-call with the halt continuation:

1. Pull a fresh arena block from the pool (§6).
2. Initialize `Process { heap: block, mailbox: empty, parked_cont: null, state: Ready }`.
3. Deep-copy `closure` into the new process's heap (cross-heap pointers are
   forbidden by construction; copy enforces it).
4. Enqueue the task to run `closure.code(closure, @halt_stub)`.

The scheduler executes the task by calling that entry point on its own (system-V)
stack. There is no trampoline loop; there is no `next_frame`.

## §6. Per-process arena

### §6.1. Layout

One bump-pointer region per `Process`. No separate fz stack; all live fz data
(cont closures, value boxes, future structs) lives in this arena.

```rust
struct Heap {
    block_start: *mut u8,
    bump_top:    *mut u8,
    block_end:   *mut u8,
    size_class:  u8,        // index into §6.3 SIZE_TABLE
    low_live_streak: u8,    // §6.5 shrink hysteresis
}
```

### §6.2. Allocation

```rust
fn alloc(size: usize) -> *mut u8 {
    let p = bump_top;
    let n = bump_top.add(size);
    if n > block_end { note_alloc_pressure(); }   // flag; GC at next park
    bump_top = n;
    p
}
```

GC is **not** synchronous on allocation. The pressure flag is set; the next
scheduler-park (§4) checks the flag and runs GC for that process.

### §6.3. Size table

A static array of preset block sizes, Fibonacci-shape at the low end transitioning
to geometric (~20%):

```
SIZE_TABLE = [
    1024,   1536,   2560,   4096,   6656,   10752,
    17408,  28160,  45568,  73728,  119296, 192768,
    // tail: next = round(prev * 1.2)
]
```

Initial size on spawn: `SIZE_TABLE[0]` (1 KiB).

### §6.4. GC (Cheney)

At park-time, if pressure flag set:

```
gc(process):
    live_words = trace_from(process.parked_cont)
    new_size   = SIZE_TABLE[pick_size_class(live_words + slack)]
    new_block  = pool.alloc(new_size)
    cheney_copy(process.parked_cont, into=new_block)   // forwarding ptrs in old block
    pool.free(process.heap.block_start)
    process.heap = Heap::new(new_block, new_size)
```

**Roots:** `process.parked_cont` only. No stack scan. No register scan. Tail-call
discipline means the caller's frame is gone before any GC could observe it.

**Forwarding:** during copy, the from-space `HeapHeader` is overwritten with a
forwarding pointer to the to-space copy. Standard Cheney.

### §6.5. Shrink hysteresis

If two consecutive GCs each yield `live < 25% of current size`, pick a smaller
`size_class` next time. Counter `low_live_streak: u8` on `Heap`.

### §6.6. Pool

Blocks come from a process-global, size-classed pool. Spawn pulls; GC returns.
Avoids `malloc`/`free` churn under heavy spawn pressure.

### §6.7. Why no generational GC, no write barrier

- Cross-process pointers are forbidden by construction (spawn/send deep-copy at
  the boundary).
- Within a process, fz is functional: heap objects are not mutated after
  construction. There is no path that writes an old→young pointer.

Generational tiers and remembered sets are unnecessary. The single-generation
copying collector of §6.4 is sufficient.

## §7. Roots and GC safety

The GC fires only at park-time. At that moment:

- The current fn (if any) has tail-called into the runtime; its frame is gone.
- All previously-live SSA values are gone (Cranelift's Tail CC popped them).
- The only fz-side reference into the process arena is `process.parked_cont`.

Therefore the root set at every GC trigger point is exactly one pointer.

`return_call*` is **not** a Cranelift safepoint, confirmed by the test
`hot_loop_alloc_triggers_safepoint_gc` in `src/ir_codegen.rs:4915-4944` (allocation
calls + tail calls coexist in the current codebase; the GC fires on the alloc, not
the tail-call).

Cranelift's stack-map APIs are **not used and not required**. fz roots are
structurally discoverable from `parked_cont`.

## §8. Acceptance fixtures

Four fixtures, each chosen to exercise one property no other fixture does. Target
clif listings below are the **acceptance criteria** for `fz-cps.1` through `fz-cps.5`.

### §8.1. `tail_recursion.fz` — constant heap on tail-recursive forwarding

Source:
```fz
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)
fn main(), do: print(count(100000, 0))
```

Property: the recursive case of `%count` allocates nothing and forwards its
received `k` unchanged. 100 000 iterations run with `sp` constant and the process
heap at a single allocation (the main-built receive-cont).

Target clif:
```clif
function %count(i64, i64, i64) tail {              ; (n, acc, k)
block0(v_n: i64, v_acc: i64, v_k: i64):
    brif v_n, block_rec, block_done

block_rec:
    v_n1   = iadd_imm v_n, -1
    v_acc1 = iadd_imm v_acc, 1
    return_call %count(v_n1, v_acc1, v_k)          ; ZERO alloc; k forwarded

block_done:
    v_kcode = load.i64 v_k+16
    return_call_indirect sig_cont, v_kcode(v_acc, v_k)
}

function %main(i64) tail {                          ; (k_halt)
block0(v_k: i64):
    v_k1   = call %fz_alloc_closure(iconst.i32 1)
    v_code = func_addr.i64 %main_k1
    store v_code, v_k1+16
    store v_k,    v_k1+24
    v_100k = iconst.i64 100000
    v_0    = iconst.i64 0
    return_call %count(v_100k, v_0, v_k1)
}

function %main_k1(i64, i64) tail {                  ; (result, self)
block0(v_r: i64, v_self: i64):
    v_kh = load.i64 v_self+24
    return_call %print(v_r, v_kh)
}
```

Acceptance:
- `%count` contains zero `fz_alloc_*` calls.
- `block_rec` ends in `return_call %count`.
- `%main` calls `fz_alloc_closure` exactly once.
- Running 100 000 iterations completes, RSS stays flat, GC fires ≤ 1 time.

### §8.2. `higher_order.fz` — unified closure/fn ABI

Source (focus on `compose`):
```fz
fn double(x), do: x * 2
fn neg(x), do: 0 - x
fn compose(f, g, x), do: f(g(x))
fn main(), do: print(compose(double, neg, 5))
```

Property: `compose` builds a cont (`kg`) that captures `f` and the outer `k`,
then invokes `g` and `f` via the closure-indirect path. `double` and `neg` are
top-level fns wrapped once at module init into static zero-capture closures.

Target clif (compose only):
```clif
function %compose(i64, i64, i64, i64) tail {        ; (f, g, x, k)
block0(v_f: i64, v_g: i64, v_x: i64, v_k: i64):
    v_kg   = call %fz_alloc_closure(iconst.i32 2)
    v_code = func_addr.i64 %compose_after_g
    store v_code, v_kg+16
    store v_f,    v_kg+24
    store v_k,    v_kg+32
    v_gcode = load.i64 v_g+16
    return_call_indirect sig_closure1, v_gcode(v_x, v_g, v_kg)
}

function %compose_after_g(i64, i64) tail {          ; (r_g, self)
block0(v_rg: i64, v_self: i64):
    v_f = load.i64 v_self+24
    v_k = load.i64 v_self+32
    v_fcode = load.i64 v_f+16
    return_call_indirect sig_closure1, v_fcode(v_rg, v_f, v_k)
}
```

Acceptance:
- Both indirect calls lower to `return_call_indirect`.
- No `fz_closure_invoke` runtime helper referenced.
- Module-init region produces `double`/`neg` static closures exactly once.

### §8.3. `closure_typed_captures.fz` — escape via return

Source:
```fz
fn add_to(x, y), do: fn (z) -> x + y + z
fn apply1(f, x), do: f(x)
fn main(), do: print(apply1(add_to(10, 20), 12))
```

Property: the lambda escapes `add_to` (returned via `k`). `add_to` heap-allocates
the lambda; `%lambda_z`'s body does no allocation.

Target clif (highlights):
```clif
function %add_to(i64, i64, i64) tail {              ; (x, y, k)
block0(v_x: i64, v_y: i64, v_k: i64):
    v_lam  = call %fz_alloc_closure(iconst.i32 2)
    v_code = func_addr.i64 %lambda_z
    store.i64 v_code, v_lam+16
    store.i64 v_x,    v_lam+24
    store.i64 v_y,    v_lam+32
    v_kcode = load.i64 v_k+16
    return_call_indirect sig_cont, v_kcode(v_lam, v_k)
}

function %lambda_z(i64, i64, i64) tail {            ; (z, self, k)
block0(v_z: i64, v_self: i64, v_k: i64):
    v_x = load.i64 v_self+24
    v_y = load.i64 v_self+32
    v_t = iadd v_x, v_y
    v_r = iadd v_t, v_z
    v_kcode = load.i64 v_k+16
    return_call_indirect sig_cont, v_kcode(v_r, v_k)
}

function %apply1(i64, i64, i64) tail {              ; (f, x, k)
block0(v_f: i64, v_x: i64, v_k: i64):
    v_fcode = load.i64 v_f+16
    return_call_indirect sig_closure1, v_fcode(v_x, v_f, v_k)
}
```

Acceptance:
- `%add_to` calls `fz_alloc_closure` exactly once.
- `%lambda_z` calls no `fz_alloc_*`.
- `%apply1` is two ops: load, indirect tail-call.

### §8.4. `concurrency_ping_pong.fz` — Receive promotion

Source:
```fz
fn child(), do: send(1, 42)
fn main() do
  spawn(child)
  print(receive())
end
```

Property: `main`'s body contains `spawn` and `Receive`; the receive cont is
heap-allocated and stored into `Process::parked_cont` via `fz_receive_park`. No
parking-frame schema.

Target clif:
```clif
function %main(i64) tail {                          ; (k_halt)
block0(v_k: i64):
    v_child_clos = global_value.i64 @child_static_closure
    call %fz_spawn(v_child_clos)
    v_k1   = call %fz_alloc_closure(iconst.i32 1)
    v_code = func_addr.i64 %main_after_receive
    store.i64 v_code, v_k1+16
    store.i64 v_k,    v_k1+24
    return_call %fz_receive_park(v_k1)
}

function %main_after_receive(i64, i64) tail {       ; (msg, self)
block0(v_msg: i64, v_self: i64):
    v_kh = load.i64 v_self+24
    return_call %print(v_msg, v_kh)
}

function %child(i64) tail {                         ; (k_halt_child)
block0(v_k: i64):
    v_1  = iconst.i64 1
    v_42 = iconst.i64 42
    call %fz_send(v_1, v_42)
    v_kc = load.i64 v_k+16
    return_call_indirect sig_cont, v_kc(v_42, v_k)
}
```

Acceptance:
- `%main` ends in `return_call %fz_receive_park`.
- No `Process::frame_sizes` / schema-table references in the produced module.
- End-to-end: parent prints `42`.

## §9. DAG

### §9.1. Codegen / ABI

- **`fz-cps.1`** — Cont-param ABI (§2). Every fz fn takes `cont` as last param;
  every fz→fz transfer is `return_call*`; cont closures heap-allocated via existing
  `fz_alloc_closure`. Acceptance: §8.1 `block_rec` shape.
- **`fz-cps.2`** — Halt continuation (§2.4). One static singleton per module;
  initial `k` for every spawned task.
- **`fz-cps.3`** — `Runtime::spawn` rewrite (§5). Direct entry-call with halt cont;
  no frame seeding; no `next_frame`.
- **`fz-cps.4`** — `Receive` rewrite (§4). Cont read from parameter; stored via
  `fz_receive_park`. Acceptance: §8.4.
- **`fz-cps.5`** — Delete uniform branch + trampoline + `frame_ptr` + slot-0 +
  schema table + `fz-ul4.27.14.1`/`.14.2` machinery + closure `stub_fp` + parking
  schema + `cont_blocked` analysis. Removal-only; gated by the existing test suite
  plus all §8 acceptance fixtures.
- **`fz-cps.6`** — Three-path parity audit. AOT shim aligned; interpreter audit
  (already shape-correct per `src/ir_interp.rs:236`).

### §9.2. GC / runtime

Can run in parallel with §9.1 — they meet at the `fz_alloc_closure` contract,
unchanged.

- **`fz-cps.GC.1`** — Per-process `Heap` struct + bump allocator + park-time GC
  trigger (§6.1, §6.2).
- **`fz-cps.GC.2`** — Cheney copy with live-trace from `parked_cont` (§6.4, §7).
- **`fz-cps.GC.3`** — Size table + `pick_size_class` (§6.3).
- **`fz-cps.GC.4`** — Size-classed block pool (§6.6).
- **`fz-cps.GC.5`** — Shrink hysteresis (§6.5).
- **`fz-cps.GC.6`** — Spawn-options skeleton (API only; knobs deferred).

### §9.opt1 — Deferred optimization

Custom callee-saved bump region for stack-allocatable conts per §3.3. Conditional
on benchmarks demonstrating cost.

## §10. Open questions to settle before §9 begins

None blocking. The four questions raised during design are resolved:

1. Cont representation — §2.2: closure-shaped, single `i64`.
2. Receive integration — §4: `fz_receive_park`, no schema.
3. Multi-cont/errors — out of scope for v1; ABI is additive.
4. Cranelift `Tail` CC + `return_call*` — confirmed working alongside allocation
   safepoints in the existing codebase (§7).

`pick_size_class` exact tail past `SIZE_TABLE[11]` (§6.3) is a tunable, not a
design question.

## §11. Non-goals for this epic

- Generational GC (§6.7).
- Preemptive scheduling / reduction counting.
- Multiple continuations (ok/err / typed effects).
- Off-heap shared binaries.
- Stack-allocated conts (§9.opt1).

These are reserved for later, do not affect §9 ticket bodies, and do not require
ABI changes to add.
