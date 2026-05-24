# GC layout telemetry audit

Ticket: fz-0k7.11.2

## ELI5 model

The GC moves boxes. If a live list cell contains the integer `123`, the whole
cell moves, so `123` moves with it. The GC does not pretend `123` is a pointer.

That is the important split:

- **copy bytes**: every reachable object is copied or marked as a whole object.
- **follow edges**: only layout-local metadata decides which payload words are
  heap children.

So a scalar word can look exactly like an address and still not be followed.
The tag/kind stored by the container is the authority.

## Walker ownership

Each heap shape owns the metadata needed to trace its internals:

- List: the cons link word carries the head kind. Heap head values are followed;
  scalar head values are copied as payload bytes only. The tail word is a list
  spine edge when it is non-empty.
- Struct/tuple: the schema says which payload offsets are `ValueSlot`s. Each
  slot carries its kind byte. Heap kinds are followed; scalar kinds are copied
  as payload bytes only.
- Map: the packed tag byte beside each entry names the key kind and value kind.
  Heap keys/values are followed; scalar keys/values are copied as payload bytes
  only.
- Closure: each capture slot carries raw payload plus kind byte. Heap captures
  are followed; scalar captures are copied as payload bytes only.
- Resource: the destructor closure slot carries raw payload plus kind byte. A
  heap closure is followed; a scalar/null destructor slot is copied only.
- Bitstring and ProcBin: no payload heap children.
- Fragments: oversized objects are marked in place instead of copied into
  to-space, then traced with the same shape-specific walker.

## Telemetry acceptance

`GcStats` is emitted by the GC boundary as the return value of `gc`,
`gc_with_extra_root_slots`, `gc_process_roots`, and
`gc_value_slots_with_process_roots`; the heap also keeps `last_gc_stats`.

The stats distinguish:

- objects/bytes copied into to-space
- fragment survivors/bytes
- from-space and to-space capacity chosen for the collection
- root heap edges vs scalar root slots
- list, struct, map, closure, and resource heap edges vs scalar slots

Tests assert this directly. In particular, one test stores the address of an
unrooted cons cell as an `INT` payload inside a rooted cons cell. The rooted
cell is copied, the integer payload is preserved, and telemetry reports one
scalar list-head slot and zero list-head heap edges. The decoy object is not
copied.

That proves the policy we need before the one-word `ValueRef` ABI rewrite:
containers copy their own bytes, and only object-local metadata creates child
edges.
