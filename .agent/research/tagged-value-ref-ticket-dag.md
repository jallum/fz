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
fz-0k7.5      hard-cut campaign to TaggedValueRef
fz-0k7.5.1    acceptance gate for TaggedValueRef hard cut
fz-0k7.5.2    break old raw+kind ABI/types intentionally
fz-0k7.5.3    port runtime heap storage and GC to TaggedValueRef
fz-0k7.5.4    port runtime BIF surface to TaggedValueRef
fz-0k7.5.5    port interpreter and REPL value flow to TaggedValueRef
fz-0k7.5.6    port JIT/AOT signatures and lowering to TaggedValueRef
fz-0k7.5.7    port matcher receive mailbox and scheduler value flow
fz-0k7.5.8    final docs tests and rg gates for TaggedValueRef cutover
```

The gate is `fz-0k7.5.1` because it was deliberately created as the first child
under the hard-cut campaign. Every known hard-cut child blocks that gate, and
future worklist tickets must do the same.

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

- remove or rename old raw+kind heap-read BIFs.
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
- vector feature is gone.
- no production use of old raw+kind heap-read APIs.
- no production definitions/usages of:
  - `FzValueParts`
  - `MailboxSlot`
  - `InterpValue`
  - `StrictValue`
  - `MatcherValue`
- no `fz_*_typed_parts` heap-read BIF surface.
- no new compatibility/bridge module.
