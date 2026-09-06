# Native helper emission cutover

The predecessor is `537280e35` (fz-tfn.18). Both versions use the same
deterministic fixture selection in
`compiler2::drive_test::measure_native_cps_sharing_corpus`:

```sh
cargo test --lib compiler2::drive_test::measure_native_cps_sharing_corpus -- --ignored --exact --nocapture
```

511 source candidates produce 475 native programs; 473 support paired native
codegen. Both versions have the same exclusions, 5,771 semantic executable
entries, 118 closure constructions, and 5,705 final physical executable roots.
The existing census records each fixture's inventories and compiled text bytes,
using the existing pre-sharing capture and codegen events. No production
observation hook was added.

| Inventory | Predecessor | Reference-driven emitter | Removed |
| --- | ---: | ---: | ---: |
| Functions/bodies before sharing | 15,816 | 15,763 | 53 |
| Functions/bodies after sharing | 15,527 | 15,474 | 53 |
| Compiled bytes before sharing | 3,338,000 | 3,331,640 | 6,360 |
| Compiled bytes after sharing | 3,281,840 | 3,275,480 | 6,360 |
| Unreachable functions before sharing | 53 | 0 | 53 |
| Unreachable functions after sharing | 53 | 0 | 53 |

38 fixtures change. Every moving fixture loses exactly 120 compiled bytes per
removed body, both before and after sharing; all other fixture body and byte
counts are unchanged. This cutover does not enable additional physical sharing.
An independent repeat reproduces all 950 per-fixture inventory/byte rows and
every deterministic aggregate counter exactly; both zero-reachability assertions
pass before and after physical sharing.
The historical fz-kdt.163 audit's 59 missing ownership-role occurrences counted
repeated index passes, not this corpus's distinct function inventory.

Sharing still performs 208 passes and 6,728 graph comparisons. Indexed bodies
fall from 18,688 to 18,651; graph-owned bodies remain 17,961. Body comparisons
increase from 6,098 to 6,111: removing orphaned helpers permits previously
incomplete ownership graphs to enter structural comparison. These counters are
reported separately rather than claiming every individual count decreases.
The authoritative benefit is 53 fewer bodies lowered and compiled, with 6,360
fewer native bytes. Elapsed samples taken with concurrent validation workloads
are not comparative performance evidence.

The reference invariant checks the module/index/body bijections and all
continuation owners. It roots the entry, semantic executable entries, and
callable wrapper/member functions, then closes over direct calls, tail calls,
call continuations, and receive guard/body/after edges. Construction identity
words are not module functions: every MakeFnRef, MakeClosure, and ClosureCapture
word must resolve to a uniquely published callable boundary. The invariant
reuses the existing native control-reference enumeration and is test-only.

Focused RED tests on the predecessor expose two unused dispatch branch helpers
in `00152_case_wildcard_unreachable.fz` and a delivery resume after non-tail
`panic(:done)`. Both turn GREEN through the actual producer. Synthetic tests
exercise broken indexes, owners, identities and references, and transitive
control closure; a worklist test proves self/mutual requests are queued once.

The emitter no longer preallocates every backend entry or walks that whole
inventory to build helpers. Actual native references allocate a typed helper
once and queue its body; draining those requests discovers only further used
helpers. Unused helpers, their body facts, and their IR functions are never
built. There is no post-hoc native DCE or parallel backend reachability model.

Independent interpreter/native runs preserve the expected outputs and every
product-family evaluation/settlement count for range, predicate, take/drop,
and the small wildcard-branch witness. All four backend dumps are byte-identical
to the predecessor. The witness's CLIF difference is exactly its two removed
dead functions.

The larger three CLIF dumps retain all 144, 472, and 1,036 function bodies.
Reference-constrained bijections preserve every instruction, constant,
signature, SSA operand, stack layout, and call target. Demand-order allocation
changes generated helper numbering and declaration order; replay-stub keys
still name the same mapped callee and ABI shape (21, 50, and 53 keys). Those
derived ordinals and generated labels explain the differences. This is an
explicit structural comparison, not a claim of cross-version CLIF byte equality.
