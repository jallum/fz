# fz-tfn.55: exact runtime lifetime observations

Status: implementation, all local gates and final ticket-cold review accepted.
Commit/close/push and subsequent CI are tracked in the ticket and draft PR.
fz-tfn.49 must still be restored and reverified on this accepted prerequisite.

## Boundary and diagnosed failure

Implementation starts at accepted .50,
`21af71f13ff6f9b254cfadcecf2f37285c0fc274`, whose exact CI run
`34028301967` is green. The reviewed .49 candidate is parked in immutable stash
`59f2fc17c7073583e9d9ecf4432973be446337b2`; root checked all eight tracked and
two new files against their pre-stash hashes, preserving all nine unrelated
untracked files. .49 must be restored and reverified after this prerequisite.
The independent .46 parking boundary remains untouched.

The .49 default-parallel runtime gate failed with 209 passed and one failed:
`heap::heap_test::alloc_procbin_pushes_into_mso_chain_with_strict_layout`
read global `live_count` as 1 after dropping its heap, versus baseline 0.
The original log is `/tmp/fz-tfn49-runtime.log`. Isolated and serial tests passed
diagnostically; they do not replace the failed parallel gate.

Independent source inspection identified unannotated tests that keep unrelated
SharedBins alive while the lifetime test's `serial_test` lock excludes only
other annotated tests. The same unannotated value-projection test also allocates
a Resource, whose tests use an analogous global baseline. No source corruption
or actual leak follows from these observations. The failed log does not identify
the historical competing allocator; the interleaving is source-proven.

## Deterministic RED

Each isolated regression test snapshots the old gauge, allocates its own object,
then holds a second thread's unrelated object alive using a barrier while the
owner releases its object. It captures the incorrect count, releases and joins
the competitor, then asserts. Both tests fail with 1 versus baseline 0:

- `/tmp/fz-tfn55-sharedbin-red.log`
- `/tmp/fz-tfn55-resource-red.log`

Root inspected both terminal failure logs and the source diff at that boundary:
only the two test files changed, adding 44 lines. No production change preceded
the RED. There are no sleeps or probabilistic retries in this reproduction.

## Existing production work is real

The two private gauges have test-only getters but five production update sites:
SharedBin allocation/final heap destruction and Resource allocation/immediate
final release/deferred final release. Essential per-object refcount atomics are
separate and must remain unchanged.

Root independently inspected accepted .50's immutable binary:
`/tmp/fz-tfn50-final.ZVlAcZ/fz2`, SHA256
`02ef4472dcd698f99f57fea3c2e988efb3911cc64887cf74d1babd6ab4e829b5`.
`nm` exposes both private `LIVE_COUNT` symbols at `0x101f497f8` (SharedBin)
and `0x101f49800` (Resource). Targeted Mach-O disassembly confirms calls to
atomic operations using those exact gauge addresses:

| Operation | Gauge atomic call address |
| --- | --- |
| SharedBin allocation increment | `0x101235f50` |
| SharedBin heap destructor decrement | `0x101236b9c` |
| Resource allocation increment | `0x10125ad28` |
| Resource immediate final-release decrement | `0x10125b034` |
| Resource deferred final-release decrement | `0x10125ae88` |

These are observations of this frozen binary, not assumptions about optimizer
behavior in every build profile. The Resource release functions also contain
their essential refcount decrements; those are not removal targets.

For targeted inspection, the Mach-O-specific option is
`xcrun llvm-objdump --macho --disassemble --dis-symname SYMBOL BINARY`.

## Approved proof model

Heap tests observe the exact reference owned by each heap through existing
handles/refcounts, keeping pointer reads valid. Such a retained witness alone
does not establish final destruction. Separate scoped destructor observations
must prove final release exactly once, including cross-thread release.

The SharedBin final-release fixture uses the real allocator, carries a scoped
observer through its test bytes, installs the test destructor before publication,
and delegates final buffer/header reclamation to the real heap destructor.
Resource already has a payload/destructor seam for scoped observation; deferred
release must preserve its distinct returned-payload/no-inline-destructor contract.
The final tests retain the RED's coordinated unrelated allocation interleaving.

The production change should delete both gauges and all five unused updates,
without new runtime fields, ABI layout changes, registries, or alternate lifetime
authorities. Tests should remove superseded global guards/destructor counters and
gauge-only serial annotations, retaining unrelated global-state synchronization.

## Frozen candidate and completed checks

The nine-path tracked source/documentation diff against accepted .50 has SHA256
`19cb0bc2fb0078e797f8f74a9774640dcfd076db022b941b4472daf3b7e8b49d`.
Production changes remove the two gauges and five updates; essential retain,
release, destructor and layout code is unchanged. All gauge-only runtime serial
annotations are gone. The process-global umask test keeps its annotation and
the `serial_test` dependency.

The preserved coordinated regression tests pass together under default parallel
execution (`/tmp/fz-tfn55-isolation-green.log`). Each owner is destroyed once
while its competitor is still alive; the competitor's observation stays zero
until its own release, then becomes one. Both scoped observer references return
to their single test-owned edge.

The final default-parallel runtime suite passes 214 tests with none failed or
ignored (`/tmp/fz-tfn55-final-runtime.log`, terminal session 90742). Relative to
the accepted 210-test baseline, six new isolation/deferred/concurrency/GC/sharing
controls and two proof-preserving folds produce a net four tests. The folds
combine custom-destructor proof with handle-drop proof, and three-entry chain
layout with per-entry final destruction. Original-data heap controls retain
their data/layout assertions and use exact live handles for edge counts.

The unchanged retain/release loom model passes under
`RUSTFLAGS="--cfg loom" cargo test --release -p fz-runtime loom_`
(`/tmp/fz-tfn55-loom.log`, terminal session 96566). This run preceded the two
ordinary-test folds; production and model code stayed identical. Strict
workspace/all-target Clippy completed successfully (terminal session 34535).
The compiler library passes 1,953 tests with no failures and six existing
ignored tests (`/tmp/fz-tfn55-library.log`, terminal session 96935).
The serial fixture matrix passes all 537 cases with none failed or ignored
(`/tmp/fz-tfn55-fixtures.log`, terminal session 12428). Root independently ran
`cargo fmt --all -- --check` and `git diff --check`; both pass and the frozen
tracked diff fingerprint remains unchanged.
CLI tests pass 30/30 and the AOT integration test passes 1/1
(`/tmp/fz-tfn55-cli-aot.log`, terminal session 78987). Workspace documentation
tests pass with one existing ignored compiler example
(`/tmp/fz-tfn55-docs.log`). No test retries, new ignores, broadened locks or
increased budgets are part of the cutover.
Ticket-cold source review found no actionable issue at the exact frozen diff;
the reviewer also independently verified both binary hashes, the disassembled
atomic-call reductions, artifact/work comparisons, ordered validation metadata
and compiler-library result. Final review also accepted the matrix, CLI, AOT,
documentation and format evidence without actionable findings.

## Independent final binary and artifact proof

The normal debug build completed (session 44242). Root independently verified
the immutable candidate `/tmp/fz-tfn55-final.IJgNg2/fz2`, SHA256
`c77e8dc71c3cf867d4c4230393f60cc2e0b00d984a337e10649030cebecf15d2`.
`nm` finds neither `LIVE_COUNT` symbol. Targeted disassembly of the same five
functions in both frozen binaries proves these atomic-call counts:

| Function | Accepted .50 | Candidate .55 |
| --- | ---: | ---: |
| SharedBin allocation | 1 | 0 |
| SharedBin heap destruction | 1 | 0 |
| Resource allocation | 1 | 0 |
| Resource immediate release | 2 | 1 |
| Resource deferred release | 2 | 1 |

The remaining Resource decrements are the essential per-object refcount
operations. Thus this binary removes the five dead gauge updates, not merely
their source names. No wall-clock or whole-compiler speedup is inferred.

Root's six-door proof completed successfully (session 45623), using
`/tmp/fz-tfn46-proof-tool.jZn1af/verify.cjs` with its baseline explicitly set to
accepted .50 at `/tmp/fz-tfn50-accepted-proof.0IjODW`. Candidate output is
`/tmp/fz-tfn55-final-proof.xXBuIO`; the log is
`/tmp/fz-tfn55-final-proof.log`. All three fixtures in both interpreter and native
execution match their output goldens with empty stderr. All three backend and
three CLIF artifacts are byte-identical. Every typed job/request/evaluation/
settlement family, body-walk count, native function count and native code-byte
count matches the accepted baseline. This compares generated compiler artifacts,
not executable bytes: the linked runtime intentionally loses gauge instructions.

A separate root comparison checks the complete ordered ProductValidation
metadata, not just sums: it is identical for both doors of range (69 events),
predicate (174 events), and take-drop (246 events). The runtime-only cutover
does not add compiler evaluations or validation observations in these controls.

## Landing boundary

All planned local gates and cold reviews are complete. Root rechecked prior
commit `21af71f13ff6f9b254cfadcecf2f37285c0fc274`: exact CI run `34028301967`
is completed/success. The new commit's own CI is tracked separately. Any source
revision requires revalidating the frozen candidate and affected evidence.
