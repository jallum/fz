# TaggedValueRef Ticket DAG

## Overview

The migration should be organized as preparation plus a hard-cut campaign.

Preparation proves the new heap access model without changing production
interpreter/JIT/AOT behavior.

The hard cut removes the old raw+kind value ABI and works compiler failures by
module. There should be no long-lived compatibility bridge.

## Proposed Spine

```text
fz-tvr        epic: TaggedValueRef value representation
fz-tvr.1      research + design docs
fz-tvr.2      remove vector heap/type/runtime surface
fz-tvr.3      add TaggedValueRef pack/unpack/projection primitives
fz-tvr.4      add heap-only read/write APIs returning TaggedValueRef
fz-tvr.5      hard-cut campaign parent
fz-tvr.5.1    hard-cut acceptance gate
```

## Actual Issue Graph

`bw` assigned this graph:

```text
fz-0k7        epic: TaggedValueRef value representation
fz-0k7.1      land TaggedValueRef research and design docs
fz-0k7.2      remove vector heap/type/runtime surface
fz-0k7.3      add TaggedValueRef primitives with heap-only tests
fz-0k7.4      add heap read/write APIs returning TaggedValueRef
fz-0k7.6      add heap write APIs accepting TaggedValueRef
fz-0k7.5      hard-cut campaign to TaggedValueRef
fz-0k7.5.1    acceptance gate for TaggedValueRef hard cut
fz-0k7.5.2    break old raw+kind ABI/types intentionally
fz-0k7.5.3    port runtime heap storage and GC to TaggedValueRef
fz-0k7.5.4    port runtime BIF surface to TaggedValueRef
fz-0k7.5.5    port interpreter and REPL value flow to TaggedValueRef
fz-0k7.5.6    port JIT/AOT signatures and lowering to TaggedValueRef
fz-0k7.5.7    port matcher receive mailbox and scheduler value flow
fz-0k7.5.8    final docs tests and rg gates for TaggedValueRef cutover
fz-0k7.5.9    rename FzValue into storage-local ValueSlot
fz-0k7.5.10   replace typed-parts BIF returns with one-word values
fz-0k7.5.11   replace MailboxSlot with traceable value-root storage
fz-0k7.5.12   replace InterpValue with REPL-only Value view
fz-0k7.5.13   replace StrictValue with typed lanes plus TaggedValueRef
fz-0k7.5.14   replace MatcherValue and matcher scratch ABI
```

The gate is `fz-0k7.5.1` because it was deliberately created as the first child
under the hard-cut campaign. Every known hard-cut child blocks that gate, and
future worklist tickets must do the same.

`fz-0k7.4` proved the heap read side only. `fz-0k7.6` is titled
`tvr.4.1` and is deliberately wired before `fz-0k7.5`: it adds the missing
write side (list construction, map put/construction, struct field writes, and
closure capture writes) so the hard cut does not start until both heap reads
and heap writes have a tested `TaggedValueRef` API.

The first `fz-0k7.5.2` compile break renamed only the old carrier declaration
points. That exposed these module-sized clusters before runtime could even
finish type checking:

- `fz-0k7.5.9`: `FzValue` is the runtime storage substrate and must either die
  or become a deliberately storage-local slot/root type.
- `fz-0k7.5.10`: `FzValueParts` owns raw+kind out-param BIF returns and must be
  replaced by one-word value returns/projections.
- `fz-0k7.5.11`: `MailboxSlot` owns persistent mailbox/scheduler storage and
  must become shared traceable root storage.
- `fz-0k7.5.12`: `InterpValue` is the interpreter-only value view and must not
  become a runtime representation.
- `fz-0k7.5.13`: `StrictValue` is the JIT raw+kind SSA carrier and must split
  into scalar fast lanes plus generic one-word tagged values.
- `fz-0k7.5.14`: `MatcherValue` and matcher scratch buffers duplicate the same
  raw+kind ABI in receive codegen.

## Gate-First Rule

Create the hard-cut acceptance gate before implementation children:

```text
fz-tvr.5.1 acceptance gate: TaggedValueRef hard cut complete
```

As the compiler-error worklist reveals module-sized missions, add child tickets
and make each one block the gate.

This prevents the gate from opening before all discovered work is completed.

## Hard-Cut Tactics

The hard cut should start by making the old world stop compiling:

- remove or rename old raw+kind heap-read/write/build BIFs.
- remove or rename old raw+kind heap storage builders.
- remove or rename `FzValue` unless it is narrowed and renamed into an
  intentionally storage-local root/slot type.
- remove or rename `FzValueParts`.
- remove or rename `MailboxSlot`.
- remove or rename `InterpValue`.
- remove or rename `StrictValue`.
- remove or rename `MatcherValue`.

Then fix forward.

Each compiler-error cluster becomes a ticket if it is not already covered:

- runtime primitives
- heap layouts/readers/writers
- GC forwarding/rooting
- persistent root containers
- runtime BIFs
- interpreter/repl
- JIT signatures
- JIT lowering
- matcher/selective receive
- mailbox/scheduler/runtime
- docs/tests/fixtures

## Final Gate Acceptance

The acceptance gate should require:

- all tests pass.
- docs match implementation.
- interpreter and JIT/AOT use the same TaggedValueRef BIF surface.
- JIT/AOT/runtime BIF signatures pass and return one-word tagged values where
  possible; no raw+kind out-param structs are kept for value returns.
- vector feature is gone.
- no production use of old raw+kind heap-read/write/build APIs.
- no production raw+kind mailbox, process, map-builder, or scheduler storage.
- no production `FzValue` unless renamed into a deliberately narrow
  storage-local root/slot type.
- no production definitions/usages of:
  - `FzValueParts`
  - `MailboxSlot`
  - `InterpValue`
  - `StrictValue`
  - `MatcherValue`
- no `fz_*_typed_parts` heap-read/write BIF surface.
- no new compatibility/bridge module.
- map construction/put semantics are explicit and centralized.
- every persistent root can be traced without GC side tables.
