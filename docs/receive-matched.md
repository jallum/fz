# Receive — codegen'd matchers, sender-side resolution

Status: **design**, pre-implementation. Sibling to `docs/cps-in-clif.md §4`,
which it supersedes. Tickets (`fz-recv.*`) reference sections of this document
by anchor.

## §1. Premise

BEAM does selective receive with a save-pointer: receiver wakes on every
arrival and re-walks the mailbox from where the last scan stopped. It can't do
better because the matcher is interpreted and the runtime doesn't know what the
receiver was waiting for.

fz codegens the matcher. That changes what's possible.

The proposal collapses to one sentence:

> **The matcher is a pure leaf function. The receiver runs it on initial scan;
> the sender runs it on arrival. Whoever first finds a match resolves the
> continuation and its arguments; the receiver wakes pre-resolved.**

Everything else follows.

## §2. Model

### §2.1. Three pieces of compiled code per `receive`

| Piece | What it is | Who runs it | Where |
|---|---|---|---|
| **Matcher** | Pure leaf fn over (msg, pinned, out). Returns `(clause_idx+1)` or `0`. | Receiver (initial scan) and sender (arrival probe). | Compiled once. |
| **Clause body** | Normal fz function. Receives bound vars as args. | Receiver, on resume. | One per clause + one for `after`. |
| **Park record** | `{ matcher_fn, pinned[], after_deadline, after_cont }` on `Process`. | — | Lives in Process while parked. |

A clause body is **just a function**. Bindings produced by the pattern are its
parameters. The destructuring machinery from `fz-fyq` already covers this
shape — clause bodies reuse it.

### §2.2. Matcher ABI

```
extern "C" fn match(msg: FzValue, pinned: *const FzValue,
                    out: *mut FzValue) -> u32
```

- Returns `0` for no match; returns `clause_idx + 1` on match.
- On match, writes the bound args to `out[0..N]` where `N` is the bound-arg
  count for that clause.
- `pinned` is a const slice of FzValues captured at the moment the matcher
  was registered — pinned variables (`^x`) and any other immutable values
  the pattern compares against.
- **Pure**: no FFI back into runtime, no allocator, no schema lookups beyond
  reads, no per-process state mutation. Bytes go in, bytes go out.

The matcher is `CallConv::SystemV` — it is called from both fz-compiled code
(receiver-side scan) and from runtime Rust (sender-side probe). The latter is
load-bearing for the §3 fast path.

### §2.3. Pure-patterns / pure-guards invariant

**A pattern or guard is legal iff it lowers to operations from the read-only,
non-allocating codegen subset.**

That subset:

- Tag tests (`band_imm v, 7; icmp_imm eq ...`).
- `HeapHeader.kind` and `schema_id` reads (`load.i16 v+0`, `load.i32 v+4`).
- Field reads at known offsets into Struct/List/Map (`load.i64 v+16+i*8`).
- Hash lookup against a frozen Map (read-only).
- Integer arithmetic and comparison on already-untagged ints.
- Atom-id equality.
- Closure-pointer equality (for pinned closure values).

What's excluded:

- Any `fz_alloc_*` call.
- Any user-defined function call.
- Any cross-process pointer chase.
- String concatenation, sub-binary construction, list cons, tuple build.

**Patterns and guards share this rule.** A guard expression is exactly an
expression whose lowering passes the pure-codegen check. The typer enforces
the check at both syntactic positions in one pass.

The corollary: **matcher purity is a theorem, not a discipline.** If the
pattern compiles, the matcher cannot allocate.

### §2.4. Pattern enumeration

Every pattern shape we mean to support, and the operations its matcher
emits:

| Pattern | Lowering | Pure? |
|---|---|---|
| Scalar literal (`42`, `:atom`, `nil`) | bits compare | ✓ |
| Wildcard `_` | no-op | ✓ |
| Variable bind `x` | read slot, write to out | ✓ |
| Pinned var `^x` | read pinned, bits compare | ✓ |
| Tuple `{a, b, ...}` | tag test, schema/arity test, element reads | ✓ |
| List `[h \| t]` | tag test, kind test, car/cdr reads | ✓ |
| List `[a, b, c]` | three cons reads, terminal `[]` test | ✓ |
| Map `%{k => v, ...}` | hash lookups, returns existing FzValue at each key | ✓ |
| Whole-binary equality `<<a, b, c>> = msg` | byte-compare | ✓ |
| Bitstring extract scalar `<<n::8, ...>>` | byte/shift/mask into immediate int | ✓ |
| Bitstring tail bind `<<n::8, rest::binary>>` | bind `(msg_ptr, offset)` as two slots | ✓ |
| Sub-tuple / sub-list rest patterns | bind `(parent_ptr, index)` as two slots | ✓ |

The tail-binding row is the one that needs explaining. Binaries in fz are
heap objects (`HeapKind::Bitstring` / `HeapKind::ProcBin`). A sub-binary
ordinarily requires allocating a fresh bitstring/procbin stub. The matcher
**doesn't do that**. It binds the rest position as two pieces of data the
body can use directly:

- The parent binary FzValue (already in the message, no copy).
- The bit-offset where `rest` begins, as a tagged int.

The body, if it just reads bytes from `rest` or pattern-matches it further,
does so via `(parent, offset)` indexing — no allocation. If the body needs
to hand `rest` to something that wants a generic binary FzValue, it
materializes a sub-binary on the receiver thread, in the receiver's arena,
at that point. The matcher reports facts; the body builds things.

This means **the user's source-level binding `rest` may be lowered as two
hidden parameters of the clause body** (`rest_parent`, `rest_offset`). Body
code that uses `rest` shape-matches on those. This is a codegen detail; the
surface syntax is unchanged.

### §2.5. Park record

When the receiver enters a `receive`, scans the mailbox, and finds no match,
it parks:

```rust
struct ParkRecord {
    matcher_fn: extern "C" fn(FzValue, *const FzValue, *mut FzValue) -> u32,
    pinned: SmallVec<FzValue, 4>,
    bound_arity: u16,                  // max N across clauses; sizes out[]
    after_deadline: Option<Instant>,   // None = `after :infinity` or absent
    after_cont: *mut u8,               // closure ptr; null if no `after`
}
```

`Process::parked_cont: *mut u8` is replaced by `Process::parked: Option<ParkRecord>`.
The existing `state = Blocked` flag continues to mean "owns no run-queue entry."

### §2.6. Ready-queue entry shape

The scheduler today resumes a parked task by calling
`cont.code(msg, cont)` via an inline thunk. Under this design the
scheduler may already know the clause body and bound args before the task
runs:

```rust
enum ReadyEntry {
    Fresh(Process),                                         // never run
    Resume { cont: *mut u8 },                               // legacy, one-arg cont
    ResumeMatched { cont: *mut u8, args: SmallVec<FzValue, 8> },
}
```

`ResumeMatched` is the new path. The cont is a clause body; the args are
the bound vars in declaration order.

## §3. Protocol

### §3.1. Receiver hits `receive`

```
1. Build ParkRecord (matcher_fn, pinned snapshot, after, bound_arity).
2. Walk mailbox from head to tail:
     for each msg at index i:
         out = stack-buffer[bound_arity]
         k = matcher_fn(msg, pinned.as_ptr(), out.as_mut_ptr())
         if k > 0:
             splice msg out of mailbox at index i
             tail-call clause_body[k-1](out[0], out[1], ..., k_outer)
   end
3. No match → register parked = Some(ParkRecord),
              schedule after_deadline (if any) on the timer wheel,
              set state = Blocked,
              fz_yield to scheduler.
```

The initial scan happens on the receiver's thread, in the receiver's arena.
This is the "scan-hit" path.

### §3.2. Sender does `send(pid, m)`

```
1. Deep-copy m from sender heap to receiver heap (today's path).
2. Append to receiver.mailbox.
3. If receiver.parked is Some:
     out = stack-buffer[bound_arity]
     k = matcher_fn(m, pinned.as_ptr(), out.as_mut_ptr())
     if k > 0:
         splice m out of mailbox (tail position)
         cancel after-timer
         args = SmallVec::from(out[0..clauses[k-1].arity])
         cont = clause_body_ptr[k-1]
         clear receiver.parked
         enqueue ResumeMatched { cont, args }
         receiver.state = Ready
     else:
         (no-op — message stays in mailbox, receiver stays Blocked)
4. Else (not parked):
     today's path (just enqueue; flip Blocked→Ready only if was Blocked
     for non-receive reasons, which v1 has none of).
```

This is the "sender-side fast path." When it hits, the receiver wakes with
its work already done: cont resolved, args bound, just run.

### §3.3. After timer fires

```
1. If receiver.parked is Some and after_cont matches:
     clear receiver.parked
     enqueue ResumeMatched { cont: after_cont, args: [] }
     receiver.state = Ready
2. Else (already woke for another reason): no-op.
```

`after 0` skips parking entirely: §3.1 step 2 runs, no match → directly
tail-call the after_cont without registering a park. `after :infinity` (or
absent `after`) means no timer is scheduled in step 3 above.

### §3.4. Concurrency invariants

**v1 is single-worker** (`src/runtime.rs:43-54` — one OS thread drives the
run queue). The "sender thread" and "receiver thread" are the same OS
thread; the model below is written in cross-thread language so it
extrapolates to the future multi-worker world (per `src/runtime.rs:27-33`),
but no `Mutex` is needed in v1. Critical sections collapse to "the
single-threaded scheduler invokes things in a definite order."

- **Sender invokes matcher.** Matcher is pure (§2.3), reads bytes
  already copied into receiver's heap, writes only to a local out-buffer.
  No allocator interaction. No GC race: receiver is `Blocked`, so its
  arena is not being mutated; GC fires only at park-time.
- **Lock scope (forward-looking).** Under multi-worker, a short mutex on
  `Process::parked` and the mailbox tail would guard the sender-side
  critical section. v1 has nothing to lock — the worker either holds the
  receiver Process or doesn't, and `dispatch_send` runs inline.
- **FIFO across matches.** Initial scan is in head-to-tail order. After
  registration, single-message arrivals are inherently ordered. The
  semantics match BEAM's "first matching message in mailbox order."
- **Self-send.** Sender == receiver means we are not parked (we're
  running). Step 3 of §3.2 short-circuits: just enqueue. No special case
  needed at the matcher level.
- **Spurious wakes.** Not possible: the scheduler never moves a `parked`
  task to Ready except via §3.2 or §3.3.

## §4. What's removed

The single-cont parked-state of `docs/cps-in-clif.md §4` is replaced:

- `Process::parked_cont: *mut u8` → `Process::parked: Option<ParkRecord>`.
- `fz_receive_park(cont)` → `fz_receive_park_matched(matcher_fn, pinned_ptr,
  pinned_count, bound_arity, after_ms, after_cont)`.
- The scheduler's "load cont+16; call_indirect (msg, cont)" thunk is replaced
  by the §2.6 `ResumeMatched` dispatch, which is itself a one-instruction
  load + tail-call with N args.

Other deletions:

- The notion of a save-pointer never lands. Registration-time replaces it.
- `fz_receive_attempt` (the pre-CPS legacy fallback) goes.
- `receive` as a parseable identifier in `runtime.fz` and the parser goes.
  It becomes a dedicated syntactic form, not a function.
- The "first message wins" semantics goes; replaced by clause-order match.

## §5. Three-path parity

| Backend | What it does |
|---|---|
| **Interpreter** | Walks the pattern AST directly inside `Term::Receive`. Mailbox iteration, pinned-var capture, after-timer dispatch all live in `ir_interp.rs`. No matcher codegen — the pattern AST *is* the matcher. |
| **JIT** | Compiles the matcher as a SystemV leaf function. `Term::Receive` lowers to `fz_alloc_park_record + fz_receive_park_matched`. Clause bodies and after_body are normal compiled fns reached via `ResumeMatched`. |
| **AOT** | Same Cranelift module as JIT; differs only in linking. The `ResumeMatched` shim is in `runtime/src/aot_shim.rs` alongside the existing entry shims. |

All three see the same surface, the same IR, the same fixture goldens. There
is no "selective receive feature flag" — it's the only receive shape.

## §6. Surface syntax (Elixir-shaped)

```fz
receive do
  pat1 [when g1] -> body1
  pat2 [when g2] -> body2
after
  ms -> after_body
end
```

- `after` is optional. Absent = wait forever.
- `after 0` is the peek form.
- `after :infinity` is allowed; same as absent.
- `make_ref()` and `self()` are builtins; pin variables work on any FzValue.

## §7. ABI / IR

A `Term::Receive` becomes:

```rust
struct ReceiveClause {
    pattern: PatternTree,         // compiled to matcher arm
    guard:   Option<ExprTree>,    // compiled inline with arm; pure-only
    body:    FnId,                // a normal fz fn, params = bound vars
    arity:   u16,                 // body's bound-var count
}

Term::Receive {
    clauses:   Vec<ReceiveClause>,
    after:     Option<(FnId /*timeout_expr*/, FnId /*after_body*/)>,
    pinned:    Vec<Var>,          // pinned-var snapshot to capture at park
    captures:  Vec<Var>,          // outer-scope vars passed to each clause body
}
```

Clause bodies and after_body all take `captures...` as trailing parameters
(after bound pattern vars), matching how today's continuations carry their
captures. The matcher itself takes no captures — just `(msg, pinned, out)`.

The escape rules of `cps-in-clif.md §3` extend cleanly: `Receive` remains
the escape point. The new bit is that the *clause body* is what gets
enqueued (not a wrapper), and the matcher is a sibling leaf fn that does
not participate in the cont chain.

## §8. Acceptance fixture

`fixtures/receive_selective_refs/input.fz` — two pinned-ref selective
receives whose replies arrive in the wrong order. Exercises:

- Sender-side matcher miss (ref_a reply arrives while receiver waits on ref_b).
- Sender-side matcher hit (ref_b reply arrives; sender resolves, receiver
  wakes pre-resolved).
- Receiver-side scan hit (second receive finds ref_a reply already in mailbox).
- Pinned variables.
- `make_ref`.
- `after` clause (defensive, doesn't fire).

See `docs/receive-matched-stress-test.html` for a step-by-step trace of
this program through the matcher, parked state, and CLIF lowering.

## §9. DAG (sketch — bodies to be filled per `bw` conventions)

### §9.1. Front-end
- **`fz-recv.parse`** — parser support for `receive do ... after ... end`.
- **`fz-recv.ast`** — dedicated `Expr::Receive`; drop the Call-shaped path.
- **`fz-recv.guards`** — pure-codegen-subset typer pass; reject impure guards/patterns at typing.
- **`fz-recv.pin`** — pin-var (`^x`) lowering through the matcher's `pinned` slice.
- **`fz-recv.ref`** — `make_ref()` builtin + Pid/Ref opaque types.

### §9.2. Codegen
- **`fz-recv.matcher`** — codegen for the pure leaf matcher.
- **`fz-recv.clauses`** — clause bodies as normal fns; captures passed via trailing params.
- **`fz-recv.park`** — `fz_receive_park_matched` FFI + `ParkRecord` allocation.

### §9.3. Runtime
- **`fz-recv.parkstate`** — `Process::parked: Option<ParkRecord>`; replace `parked_cont`.
- **`fz-recv.send`** — `dispatch_send` invokes registered matcher on the
  arrival; emits `ResumeMatched` on hit.
- **`fz-recv.timer`** — sorted-list timer wheel; deadline dispatch.
- **`fz-recv.scan`** — receiver-side initial scan helper.

### §9.4. Interpreter
- **`fz-recv.interp`** — `Term::Receive` walker in `ir_interp.rs` covering
  scan, sender-probe (via a shared scheduler hook), and timer.

### §9.5. Removal
- **`fz-recv.delete`** — drop `fz_receive_attempt`; drop `receive` from
  `runtime.fz`; drop `parked_cont` field.

### §9.6. Acceptance
- **`fz-recv.fixture`** — `receive_selective_refs/{input.fz,expected.{clif,specs,txt}}`
  golden lands; interp + JIT + AOT runs produce identical printed output.

## §9.7. Investigation facts that ground the DAG

Resolved before tickets are filed. Each item is a code reference, not an
opinion.

- **Single-worker scheduler.** `src/runtime.rs:43-54` — v1 is one OS
  thread; no cross-thread locking needed in `dispatch_send`.
- **Schema registry is module-global.** `src/ir_codegen.rs:106-109, 188`
  + `runtime/src/heap.rs:1198` — `make_process` clones an `Rc` to a
  single `SchemaRegistry`; deep-copy passes `schema_id` through
  unchanged. The matcher can embed a `schema_id` literal and it stays
  stable across sender and receiver.
- **Pattern compiler exists and is the basis.** `src/ir_lower.rs:2724`
  (`lower_pattern_bind`) with `match_tuple` (2774), `match_list` (2800),
  `match_map` (2831), `match_bitstring` (2850). ~120 lines total. The
  matcher's compiled arms mirror this skeleton, emitting to a leaf
  SystemV fn rather than inline.
- **Typer central pass.** `src/ir_typer.rs:1917` (`type_prim`) is the
  single dispatch point. The pure-codegen check is a sibling pass that
  walks the same worklist (`process_worklist` at line 775) and rejects
  expressions whose prims fall outside the allow-set.
- **No timer infrastructure exists.** Greenfield. v1 is a sorted
  `Vec<(deadline_ns, PidId, TimerId)>` scanned on each scheduler tick —
  fine under single-worker.
- **Opaque types + Pid precedent.** `src/types.rs:432`
  (`Descr::opaque_of`) + `src/runtime.fz:1` (`@type pid :: opaque
  integer`). `Ref` follows the same pattern. `PidId` counter lives on
  Runtime (`src/runtime.rs:199-201`); `RefId` is the same shape.

## §10. Non-goals

- Out-of-band signals (link/monitor messages).
- Per-clause `match_spec`-style bytecode (we have native code; no benefit).
- Zero-copy send (`fz-ul4.19.5`). The matcher's purity assumes the message
  is in the receiver's arena. Zero-copy changes the trust boundary; it is
  a later epic that builds on this one, not part of it.
- Multiple alternative continuations per clause (ok/err split). Each clause
  has one body.
