# Interpreter Frame

The interpreter (`src/ir_interp`) runs a `BackendProgram` one control entry at a
time. Everything a running executable holds is a `Frame`: a table with one slot
per value id, `Vec<Option<BackendBoundValue>>`. A frame moves from step to step
instead of being rebuilt, and a call hands it to the continuation that resumes
after the call.

## Sizing

Value ids are allocated by the lowerer's `fresh_value`, counting up from zero
per function body. `Lowerer` records that count on the `LoweredBody`
(`with_value_count`); `prune_lowered_body` carries it over when a body is
trimmed for one executable, and `BackendExecutable::value_count` copies it. Ids
are not dense: trimming removes the ids of unreachable clauses and entries, so
a frame has gaps, but every id the body names is below the count.
`step_backend_executable` builds `Frame::sized(executable.value_count)`.

`Frame::insert` panics, naming the id and the frame length, when an id is out of
range. There is no growth path, so a count that is too small fails at the first
write rather than corrupting a run. Hand-built test executables carry
`BackendExecutable::TEST_VALUE_COUNT`, and their tests build frames of that size.

## Entering an entry

`enter_entry` prepares the frame for a target entry in place: it binds the
entry's delivered parameters and, for a `DeliveredResume` origin, binds the value
the call returned. Entries reached by a branch, a `Deliver` destination, a
receive match or a receive `after` continue in the current frame. A return
pops the continuation and enters its entry with the returned value.

## Calls and retention

A non-tail call parks the caller's frame in a `BackendContinuation` behind the
callee. `retain_continuation_captures` first reduces the frame to what the
target entry reads: it takes the entry's `captures` and `physical_captures` out
of the frame, clears every other slot, and puts the captures back. A capture
the frame does not hold is an error naming the value.

A `try` parks a handler frame the same way, but its body keeps running in the
current frame, so the handler frame is built from a copy of it trimmed to the
handler entry's captures. A raise pops continuations down to the handler frame
and enters the handler entry in that frame with the raise's kind, value and
exception name as its parameters.

The trim is load-bearing for collection. `BackendParkRecord::heap_refs_mut` roots
every value in a parked process's frame and in each of its continuation frames,
so a dead slot left in a frame keeps its heap value alive across a park. The
trimmed frame roots exactly the target entries' captures.

## Lanes

`Lanes` is `SmallVec<[AnyValue; 4]>`. The words of a call's arguments, an
encoded value and a macro entry's inputs are built in a `Lanes`, so a call of up
to four words allocates nothing for them. `BoundValue::Transport` stores
its lanes as a `Vec`, so a transport value converts with `into_vec`.
