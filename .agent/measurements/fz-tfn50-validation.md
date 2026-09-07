# Shared product wait observations

Ticket: `fz-tfn.50`. Baseline: `e616d82d13cc4e916bfae8e5a48e5219ac680d8a`.
The independent `.46` candidate remains recoverably parked in stash
`710cba048553f39fbfcb4eb49171b92cdb7809f7`; it is not part of this change.

## Removed work and ownership

The drive no longer clones each complete wait vector and its positioned input
boxes solely for `last_wait`. It moves the original sorted vector into one
immutable `ProductWaitBatch`, shared by the live frame and latest diagnostic.
The product heap contains original-batch indices or newly admitted owned keys.
Fact pumping borrows the original prefix, removing its drain/collect/reverse
buffer. Product pulls borrow selected keys rather than copying them per pull.
Budget errors borrow the exact full observation, even after its frame drains.

A batch-borrowed child that itself waits copies its owner once into an
independent batch, replacing the former per-pull copy. Owned dynamic children
move. Completed owners move after releasing the prior diagnostic; checked
unique ownership replaces a fallback clone. No batch owns a parent handle.
Cancellation moves boundary handles and releases routing through the existing
frame teardown; no value store, dependency authority or lifetime registry is
added.

Storage accounting is explicit: each Waiting outcome handled by the drive adds
one shared batch allocation, including an empty batch. A nonempty product
suffix allocates its exactly sized index/admission heap. Empty and fact-only
batches allocate no such heap. Exact-size range construction avoids growing an
initially undersized buffer. Tests prove original backing, bounded ownership
and release—not a reduction in all allocator calls or measured wall-clock time.

## TDD and review

`/tmp/fz-tfn50-wait-backing-red.log` records two genuine failures on the baseline:
the diagnostic vector and a healthy selected positioned input have different
backing from the originals. Exact diagnostic text passes before the backing
assertion fails. Three incumbent frame controls pass in the same run.

`/tmp/fz-tfn50-product-drive-final-controls.log` passes all **48** controls.
They include original vector/input backing, full empty/mixed/latest nested
diagnostics after frame drain, descending fact order, exact suffix offsets and
capacities, checked completed-owner transfer, weak cancellation lifetimes,
actual producer selection and failed selection followed by same-driver retry.
The existing dynamic admission and cancellation behavior remains required.
No temporary allocation counter, batch registry or probe remains.

An independent reviewer uninvolved in this ticket's implementation accepted
the final eight-path diff, subject to remaining gates and work proof:
`7b07beffbcf414e3539a7c45819d9fdb1c892aa9fc3dd3b569db878a2797ea8c`.
The review caught and resolved the index-heap growth risk and verified completed
owner uniqueness across normal completion and cancellation.

## Independent immutable artifact and work proof

Binary: `/tmp/fz-tfn50-final.ZVlAcZ/fz2`.
SHA256: `02ef4472dcd698f99f57fea3c2e988efb3911cc64887cf74d1babd6ab4e829b5`.
Proof: `/tmp/fz-tfn50-accepted-proof.0IjODW`.
Log: `/tmp/fz-tfn50-independent-proof.log`.
Unchanged verifier: `/tmp/fz-tfn46-proof-tool.jZn1af/verify.cjs`, SHA256
`f965b874f858ccc45191e35ce419dacb01a823bebb764367cc80755d5401a060`.
Baseline proof: `/tmp/fz-tfn48-accepted-proof.kYZFpt`.

Root independently ran all three fixtures through interpreter and native
execution. All six outputs match their goldens with empty stderr. Backend and
CLIF artifacts are byte-identical to `.48`. Every job, request, evaluation and
settlement family matches; no comparator or work budget changed.

| Fixture | Jobs | Body walks | Native functions | Native code bytes |
| --- | ---: | ---: | ---: | ---: |
| range map | 1393 | 243 | 144 | 31004 |
| predicate search | 2394 | 589 | 472 | 101744 |
| take/drop/split | 4233 | 1280 | 1036 | 302304 |

A separate root comparison of every numeric `ProductValidation` field and
event count is exact on both doors: ordering comparisons are 2055/7283/21517,
witness visits 102/278/369, and witness updates 558/1503/2151. These are CLI
measurements, distinct from the library's retained-request and bare-drive pins.

## Verification

- Compiler library: **1953 passed, 0 failed, 6 existing ignored**,
  `/tmp/fz-tfn50-library.log`.
- Serial fixture matrix: **537 passed**, `/tmp/fz-tfn50-fixture-matrix.log`.
- CLI/cross-process: **30 passed**; AOT: **1 passed**,
  `/tmp/fz-tfn50-cli-aot.log`.
- Strict workspace/all-target Clippy passes, `/tmp/fz-tfn50-clippy.log`.
- Runtime library: **210 passed**, `/tmp/fz-tfn50-runtime.log`.
- Workspace documentation passes with one existing ignored compiler doctest,
  `/tmp/fz-tfn50-docs.log`.
- Final formatting and diff checks pass. The frozen source and binary hashes
  remain unchanged after all gates.

The prior pushed head's CI (`34019976927`, exact `e616d82d`) was independently
rechecked green before landing this ticket. Its source gate does not stand in
for CI on the new commit.
