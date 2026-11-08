# Runtime Telemetry

## Model

Runtime telemetry is how the running scheduler reports what a task did, and how
tests observe a run without reaching into a `Process`. It is the runtime side of
the same idea as compile-time [`telemetry`](telemetry.md): the system writes down
facts it already holds, and a sink that is listening reads them.

Every runtime event is a variant of `RuntimeEvent` (`runtime/src/telemetry.rs`),
and the scheduling core reports each one through `Scheduler::observe`, a
required method with no default: a scheduler that ignores events says so in
code. `end_quantum` observes the collection and the exit, `next_runnable`
observes a sleep, and the send paths and run teardown observe their own events.

- The JIT `Runtime` and the interpreter's scheduler adapter implement `observe`
  with `emit_runtime_event` (`exec/runtime.rs`), the one function that raises
  the typed raw event for each variant on the telemetry bus.
  `Runtime::new(compiled, workers, tel)` preserves the concrete telemetry type,
  so `NullTelemetry` remains monomorphizable.
- `JsonlBackend` handles each raw event by rendering it with
  `fz_runtime::telemetry::write_line`, the one writer of a runtime event's
  line: the envelope every telemetry line shares, then the event's metadata.
- `AotScheduler::observe` appends each event, rendered with the same
  `write_line`, to the file `FZ_LOG_TELEMETRY` names; see
  [Built binaries](#built-binaries).

Seven events matter:

- `fz.runtime.execution_ready` — the boundary between compiling a program and
  running it, emitted by `run_root_jit` and `run_root_interp`.
- `fz.runtime.process_exited` — one per task exit, carrying the existing pid and
  live `Process` authority.
- `fz.runtime.scheduler_slept` — one each time the scheduling core sleeps for a
  pending receive-after timer because nothing is runnable.
- `fz.runtime.send.probe` — one per cross-process send, carrying what the
  sender's probe decided and what it cost.
- `fz.runtime.raise` — one per raise, caught or not, before the runtime decides
  where it goes.
- `fz.runtime.gc` — one per heap collection a scheduler boundary performs,
  carrying the collection's stats.
- `fz.runtime.run_ended` — one per run, after every process has been torn down,
  carrying the block pool's census.

## `fz.runtime.execution_ready`

`signal_execution_ready` (`execution_ready.rs`) raises it through `emit_runtime_event`, called
by `run_root_jit` just before the runtime spawns the entry and by
`run_root_interp` just before `run_backend_main` enqueues it — so the event
lands once per `fz2 run`, once per `fz2 interp`, and once per `run-test-root`
child `fz2 test` starts, with parsing, the fixpoint drive, the backend product
and Cranelift all behind it. A built binary observes it from `fz_aot_run_main` before its run-queue loop.
The event has no payload; its content is its position in the stream. The same
call writes one byte to the descriptor named by
`FZ_EXEC_READY_FD` when the environment names one — the fixture matrix's
execution deadline is a consumer of this boundary, not a second definition of it
(see [fixtures](fixtures.md)). A built binary does not write that byte; the
build leg's deadline starts when the binary is spawned.

## `fz.runtime.process_exited`

`sched_core::end_quantum` observes `RuntimeEvent::ProcessExited` for a halted
process once its destructors have run, on every scheduler. `emit_runtime_event`
raises it with the process's pid and the live `Process`; the event carries no
derived process fields:

```text
raw event:    fz.runtime.process_exited
signature:    (&PidId, &Process)
```

`ExitRecord` is the test-side projection: `{ pid, halt_value: i64, live_count:
usize, bytes_used: usize, list_retention_attempts: u64,
list_retention_hits: u64, raises_delivered: u64, reduction_yields: u64,
failed: bool, dtors_dispatched: u64 }`. `failed` is
`Process::ended_in_failure`: whether the process ended through an uncaught raise
with a non-zero exit status (see [exceptions](exceptions.md)); an exit with a
shutdown reason of status 0 ends a process without failing it. A failed
process's `halt_value` is not a return value. `raises_delivered` counts the
raises a handler took in this process, and `reduction_yields` the times its
reduction budget ran out and it yielded to the scheduler. `ProcessExitCapture`
builds it during dispatch by reading the live process. `write_line` reads the
same fields when it renders the event, nested under
`"process":{"opaque_type":"fz_runtime::process::Process",...}` with `failed` as
a JSON boolean. The emitter does not traverse the process for telemetry.

List-retention fallbacks are derived, not emitted separately:
`fallback_count = list_retention_attempts - list_retention_hits`. The runtime
FFI helper increments `attempts` for every `fz_list_reuse_or_cons_parts` call,
and increments `hits` when the heap returns the original source cell, either
unchanged or after guarded rewrite. That keeps the runtime telemetry seam at one
boundary event instead of a per-attempt side channel.

`dtors_dispatched` is `Process::dtors_dispatched`: the resource destructors the
scheduling core ran for the process over its whole life, whether a collection
freed the resource at a yield or park or the exit swept it (see
[scheduler](scheduler-zero-arg-closures.md#the-step-after-a-quantum)).
`write_line` renders it on `process_exited` as a number beside
`list_retention_hits`. There is no separate destructor event; a destructor
dispatched mid-life is visible on the exit record of the process that ran it,
and the `fz.runtime.gc` event of the collection that freed it precedes it.
`tests/fixture_matrix.rs`
(`a_resource_freed_by_a_collection_runs_its_destructor_once_on_every_path`)
pins it on the `run`, `interp` and `build` paths: 1 for fixture 00906 and 3 for 00907.

The raw `&Process` is valid only during dispatch. A handler that needs data
after the callback must project and copy that data itself. `write_line` renders
fields synchronously.

## `fz.runtime.scheduler_slept`

`next_runnable` (`runtime/src/sched_core.rs`) observes
`RuntimeEvent::SchedulerSlept(wait)` just before it sleeps; `wait` is the
`Duration` until the next timer deadline. `write_line` renders it as `wait_ns`.
The event fires only when the run queue is empty and a timer pends, so a program
whose timers are all cancelled by arriving messages never emits it.
`exec/runtime_test.rs` observes the event on the `run` and `interp` paths, and
`a_built_binary_sleeps_the_scheduler_once_for_a_receive_that_times_out` pins
exactly one on `build` for fixture 00687 (the count, never the wait).

## `fz.runtime.run_ended`

`RunEnded::sample` (`runtime/src/telemetry.rs`) reads the census and
`emit_runtime_event` raises it. The JIT `Runtime` observes it from its `Drop`, after clearing the task registry (exited and parked
tasks stay in the registry until then, so their heaps and any gifts still
queued on them are dropped first). The interpreter observes it in
`run_backend_main` after dropping its `IrInterpRuntime`.

```text
raw event:    fz.runtime.run_ended
signature:    (&RunEnded)
```

`RunEnded` is `{ pool_outstanding_before_run, pool_outstanding_after_run,
pool_cached_blocks }`, all block counts of the thread's block pool. Outstanding
is the count `pool_alloc` has handed out minus the count `pool_free` has taken
back (`heap::pool_outstanding_blocks`), sampled when the run began and again
once every process has been torn down; `pool_cached_blocks` is the blocks
resting in the pool's free lists. Exact blocks (a gift below or above the
table) belong to the system allocator and appear in neither count. The compiler's own heaps live on the same
thread for the whole run, so the absolute outstanding count is never zero. The
run's guarantee is `pool_outstanding_after_run == pool_outstanding_before_run`:
it returned every block it took. `write_line` renders
all three as numbers. A built binary samples the outstanding count in `fz_aot_setup` before it
creates main's process and observes the event from `fz_aot_run_main` after the
scheduler has dropped. `tests/fixture_matrix.rs`
(`a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown`) asserts the
equality for fixture 00903 on the `run`, `interp` and `build` paths.

## `fz.runtime.send.probe`

A send to another process runs `sched::probe_sender` on the sender: the
receiver's parked matcher, if any, is tested against the message with the
sender as the allocating process, and whatever the receiver will keep (the
bound values on a hit, the whole message on a miss) is copied into a gift on the
sender's heap and queued on the receiver's `in_queue`. The JIT
`send_via`, the interpreter's `send_ref` and the AOT send hook each observe
`RuntimeEvent::SendProbe` with the `SendProbe` the probe returned; the first two
raise it through `emit_runtime_event` and the AOT scheduler writes it to its log:

```text
raw event:    fz.runtime.send.probe
signature:    (&SendProbe)
```

`SendProbe` is `{ outcome: Hit | Miss, receiver: PidId, reductions: i64,
gift_bytes: usize, gift_blocks: usize }`. `reductions` is the change in the
sender's remaining budget across the matcher call; `gift_bytes` and
`gift_blocks` are the segment's fill and block count. `gift_bytes` equals the
bytes `measure_deep_copy` returned before the copy, and `gift_blocks` is `1`
for every gift that allocates; both are `0` when a hit binds nothing and no
window opens. `write_line` renders the
outcome as `"hit"` or `"miss"` and the rest as numbers. A self-send is a mailbox
push and emits nothing, as does a send to an exited or unknown receiver. `tests/fixture_matrix.rs`
(`a_send_probes_on_the_sender_and_gifts_its_result_through_the_receivers_in_queue`)
pins the event sequence of fixtures 00901 and 00902 on the `run`, `interp` and
`build` paths, and `a_receiver_left_parked_with_queued_gifts_drops_them_at_teardown`
pins each of fixture 00903's three gifts (`gift_bytes` 16032, 64 and 16, one
block each).
`many_senders_into_one_guarded_receive_gift_one_message_each_and_leave_the_misses_queued`
pins fixture 00910's hundred probes on `run`, `interp` and `build` (fifty misses of 80
bytes, the one hit of 48, then forty-nine misses; 7968 bytes in all), and
`a_large_list_passed_back_and_forth_crosses_as_one_gift_per_message_on_every_path`
pins fixture 00911's nine hits (the empty announcement, then eight balls of
320016 bytes: 20000 cells plus the bound number as a boxed scalar). Both
fixtures have the same probes on all three paths.

## `fz.runtime.gc`

`sched_core::end_quantum` (`runtime/src/sched_core.rs`) collects the process's
heap when `Heap::should_gc` holds and observes the `Collection` it performed as
`RuntimeEvent::Gc`, right after collecting and before any destructor runs. How the quantum ended is read off the process
(`Process::quantum_end`, a `Disposition`):

```text
raw event:    fz.runtime.gc
signature:    (&Collection)
```

`Collection` is `{ pid, boundary: CollectionBoundary, stats: GcStats }`; a halting
process is not collected, so the boundary of a collection is `Yield` or `Park`.
`write_line` renders `pid` and the `boundary` as `"yield"` or `"park"`, then these `GcStats` fields as numbers:

- `copied_bytes`: bytes the pass copied;
- `live_bytes`: bytes in use once the pass finished (the bytes copied);
- `from_space_capacity_bytes`: capacity of every block the pass collected (the
  tip, a gift's saved tip and every parked block);
- `blocks_released`: from-space blocks the pass released;
- `blocks_after`: blocks the heap holds once the pass finished (the new tip and every
  to-space block it parked).

`GcStats` carries more (object counts, root and per-container edge
counts); `Heap::collect` and `Process::collect` return all of it to their
callers and the heap's unit tests read it there. Every scheduler's
`end_quantum` observes it, so a built binary logs it too.
`tests/fixture_matrix.rs`
(`a_matched_reply_fixture_collects_on_every_path_though_only_the_jit_yields_mid_run`)
pins fixture 00901: 8 collections on `run` (seven child yields, one parent
park) copying 2005344 bytes in all, and 1 on `interp` (the parent's park)
copying 592, since the interpreter charges no reductions and
never yields mid-run. Neither parent collects after its graft: the gifts raised
its baseline to its fill.
The same file pins fixture 00910 (`interp`: the parent's park at 48 bytes;
`run`: its park at 288 bytes) and fixture 00911 (`interp`:
the parent's park at 0 bytes; `run`: six parent yields copying 12992, 38592,
76992, 153792, 307392 and 320128 bytes while it builds the list). The
run-ended equality is pinned for both fixtures on `run`, `interp` and `build`.
`sched_core_test.rs` pins the `Collection` that `end_quantum` observes, that a
halting process is not collected, and the exit it observes and the destructors it dispatches.

## Built binaries

A built binary links `fz_runtime` and no host crate, so it has no telemetry bus.
When the environment variable `FZ_LOG_TELEMETRY` names a path, `fz_aot_setup`
opens it with create and append, so a log that `fz2 --log-telemetry <path>
build` wrote keeps its compile events first and the run's events follow. Each
event is rendered by `write_line` with span ids 0 and `time_ns` counted from
`fz_aot_setup`, and written with one `write` of one whole line on the unbuffered
file. With the variable unset no file is opened and `observe` returns on one
branch. A path that cannot be opened is a loud failure: a message naming the
path and the error on stderr and a non-zero exit before the program runs.

The binary reports `execution_ready`, `send.probe`, `gc`, `scheduler_slept`,
`process_exited` and `run_ended`. The absolute pool counts in `run_ended` are
smaller than on `run`, since no compiler heaps share the thread; the guarantee
is the same equality. In the fixture matrix the build leg of
`run_path_logged_to` runs `fz2 --log-telemetry <log> build`, then the binary
with the fixture's arguments and `FZ_LOG_TELEMETRY=<log>`.
`a_built_binary_reports_the_same_probes_collections_and_destructors_as_run`
asserts that for fixtures 00901, 00906, 00907, 00910 and 00911 the build's probe
sequence, collections and per-process `dtors_dispatched` equal `run`'s.

## `fz.runtime.raise`

The raise route (`fz_panic`, `fz_raise_kind`, `fz_raise`) reports every raise before deciding
where it goes, through the
`ExecCtx.raise` hook; the JIT runtime and the interpreter's scheduler adapter
emit `RuntimeEvent::Raise` with a `Raise { kind, exception,
handler_depth }` (`runtime/src/telemetry.rs`): the kind's name (`error`, `throw`
or `exit`), the exception's module name (empty when the raised value is not an
exception, as it never is for a throw or an exit), and how many handlers could
take it. Depth zero is an uncaught raise. `write_line` renders the three as
`kind`, `exception` and `handler_depth`. The AOT scheduler keeps the default
no-op hook. See [exceptions](exceptions.md).

## Program Output

Printed bytes are semantic program output, not telemetry. `write_output`
passes the bytes `fz_io_write` was given, unchanged and with no newline added,
through the running process's `ExecCtx.output` hook to an event-scoped `OutputSink`. The CLI sink writes those
bytes to stdout immediately. A retaining test sink copies them during the
callback. `NullOutput` does nothing. No sink constructs an event or stages a
second copy for a later telemetry call.

Interpreter, JIT, and AOT install the same raw callback boundary. An interpreter
destructor-drain failure is propagated directly; it is not converted into a
telemetry-only warning.

## Program Arguments

`System.argv/0` reads the command line from the running process's `ExecCtx`:
`argv` points at an `Argv`, a list of raw byte strings the driver owns, and
null reads as `[]`. `fz_system_argv` conses a binary per argument, back to
front, and every execution door calls that one helper by symbol.

- JIT: `Compiler2::set_program_args` holds the arguments; `run_root_jit` passes
  them to `Runtime::with_argv`, which copies the pointer onto the context
  `run_until_idle` builds.
- Interpreter: `run_root_interp` passes them to `run_backend_main`, which hands
  them to `drive_backend_until_idle`. Macro execution
  (`run_backend_entry_on_process`) passes `NO_ARGV`, so a macro reads `[]`.
- AOT: the emitted C `main(argc, argv)` passes both to `fz_aot_setup`, which
  copies `argv[1..]` into the `AotScheduler` and points its context at the copy.
  The program name is not an argument, as in Elixir.

`fz2 run|interp <src.fz> args...` gives the program every token after the
source path, verbatim and as bytes (`args_os`). fz2's own options are read only
before the path.

## Observing In Tests

There is one run path — the production scheduler — and tests watch its exit event
instead of poking task internals:

- `ProcessExitCapture` reconstructs a typed `ExitRecord` (result + heap stats +
  cumulative list-retention counters) from each `process_exited` event's
  live process during dispatch, queryable by `last()` or `by_pid(pid)`.
- `DbgCapture` is a retaining `OutputSink` that copies each callback-scoped line,
  read back with `lines()`.

`observe(compiled, entry)` (codegen tests) attaches the exit handler and installs
the output sink, spawns `entry`, drains `run_until_idle`, and returns the root
task's `ExitRecord` plus the dbg lines. The
result/output/heap helpers build on it: `run_main` reads `observe(...).exit.halt_value`,
`capture_main` reads `observe(...).output`, and `run_capturing` returns
`(exit.halt_value, exit.live_count)`.

`CompiledModule::run(tel, fn_id)` is a sibling convenience: a thin `spawn` +
`run_until_idle` that uses the caller-owned telemetry bus, attaches a
`ProcessExitCapture`, and returns the root pid's `halt_value` from its
`process_exited` record. Both seams read the result from the event, not from
`task.halt_value`.

Tests follow the same ownership rule as compile-time telemetry: the test root
creates the bus, then helpers thread it downward. A helper that allocates its
own runtime bus splits the observation stream and stops the test from seeing the
actual run it asked for.
