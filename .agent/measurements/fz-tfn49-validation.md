# fz-tfn.49: product mutation-wave work

Status: restored unchanged on accepted fz-tfn.55; all combined local gates,
independent artifact/work proof, and final ticket-cold source/evidence review
pass. Commit/close/push and subsequent CI are tracked in the ticket and draft
PR. No whole-fixture runtime speedup is claimed.

## Acceptance boundary

The algorithmic baseline is accepted fz-tfn.50, commit
`21af71f13ff6f9b254cfadcecf2f37285c0fc274`. Its exact CI run
`34028301967` passed tests and strict lint. The unaccepted fz-tfn.46 candidate
remains parked; this ticket does not restore it or change source ownership.

The landing base is accepted fz-tfn.55, commit
`a7978bc09ec50d2d83c6173e30e80b353aa15b1d`. Its exact CI run
`34031914458` passed tests and strict lint. That prerequisite removes unrelated
global runtime lifetime gauges; it does not change this ticket's compiler
algorithm or its old-algorithm comparison.

The change must eliminate repeated minimum scanning and duplicate selection,
preserving the effective typed mutation order, external readiness transitions,
dependency ownership, equal-result reuse, and artifacts. Scheduling counts alone
are not an exhaustive measure of compiler work: key ownership, map operations,
dependency propagation, and unchanged displacement/unlink operations also enter
the argument. No healthy work budget may increase.

## Genuine old-algorithm RED

The first test exercised produced, observed products through
`ProductMemo::mutate_product_wave`, before production changes. With 32 unique
products repeated four times, exact withdrawals and unique effective mutations
passed, then selection failed: 8,128 comparisons exceeded the 896 bound.
Log: `/tmp/fz-tfn49-selection-red.log`.

Expanded production-path observations retained the original selector and
post-pop `HashSet` deduplication:

| Case | Admission attempts | Pops | Effective mutations | Propagation/readiness edges | Comparisons |
| --- | ---: | ---: | ---: | ---: | ---: |
| 512 independent products, four repetitions | 2,048 | 2,048 | 512 | 0 | 2,096,128 |
| 512-leaf diamond | 1,025 | 1,025 | 514 | 1,024 | 392,448 |

Log: `/tmp/fz-tfn49-total-wave-red.log` (terminal failure on the work bounds).
The dynamic-smaller-reader baseline control passed under both seed orders:
`/tmp/fz-tfn49-dynamic-order-baseline.log`.

The mixed-strength control initially expected displacement to erase external
generation. That expectation was incorrect: `external_state` retains the
displaced generation and clears readiness. Its corrected old-algorithm run
passed, including pending-cycle escalation under both seed orders:
`/tmp/fz-tfn49-strength-cycle-baseline.log`. This test-model correction is not
a compiler defect or a performance RED.

## Independent instrumented-old fixture proof

The original scan was frozen with complete wave counters and consolidated
reporting, before the worklist cutover:

- Binary: `/tmp/fz-tfn49-instrumented-old.2Xlkx6/fz2`
- SHA256: `cb4087647bc551b5134207c2fa57491d93b47eba96473ec588ebfd880291127d`
- Build log: `/tmp/fz-tfn49-instrumented-old-build.log`
- Recorded tracked diff SHA256:
  `9ff52f108a8e0a32f0324654721ef760423083828d1a7180c156f1a58daaf6a5`
- Independent output: `/tmp/fz-tfn49-old-independent-proof.f7VV9j`
- Independent log: `/tmp/fz-tfn49-old-independent-proof.log` (terminal success)
- Accepted comparison data: `/tmp/fz-tfn50-accepted-proof.0IjODW`
- Verifier: `/tmp/fz-tfn46-proof-tool.jZn1af/verify.cjs`, SHA256
  `f965b874f858ccc45191e35ce419dacb01a823bebb764367cc80755d5401a060`

All six interpreter/native outputs match their goldens with empty stderr.
All three backend and three CLIF artifacts are byte-identical to accepted .50.
Every job, product request/evaluation/settlement family, body-walk count, native
function count, and native code-byte count is unchanged.

Complete old interpreter observations:

| Fixture | Waves | One-mutation waves | Attempts = pops = mutations | Propagation/readiness edges | All ordering comparisons |
| --- | ---: | ---: | ---: | ---: | ---: |
| range | 386 | 205 | 676 | 332 | 2,072 |
| predicate | 904 | 428 | 1,705 | 915 | 7,349 |
| take/drop | 1,771 | 951 | 3,102 | 1,464 | 21,647 |

Here the singleton column means one effective mutation, not an inference about
the number of distinct products in every multi-mutation wave. Maximum effective
wave sizes are 5, 6, and 6. These fixtures contain no duplicate exact mutation
pairs. Each native door adds one attempt/pop/mutation and one edge, with the
same ordering total.

Only 17, 66, and 130 comparisons respectively are newly observed mutation
selection work; the remaining comparisons were already counted elsewhere.
Existing vertex/edge validation and rooted-witness work sums remain exact.
Thus synthetic fan-out improvements cannot establish a whole-fixture speedup.

Complete reporting emits 455, 1,078, and 2,017 validation events versus .50's
69, 174, and 246: formerly unreported waves are now observed. This is added
observability, not reduced work. Raw event dispatch is not free even without
observers; no zero-overhead telemetry claim is made.

`mutation_edges` covers ordinary-reader propagation, rooted-reader notification
inspections, and short-circuit Refresh readiness inspections. It excludes
dependency unlink scans during displacement. Those operations must remain
unchanged through the same effective mutation sequence, rather than disappear
from the total-work argument because they are absent from this counter.

## Intermediate verification and review corrections

The first heap prototype passed the three focused wave controls
(`/tmp/fz-tfn49-wave-prototype.log`). Review then removed an attribution-only
positioned-key clone during Dirty escalation: accepted owned work moves its key;
rejected owned work returns that same key for final reporting.

The next candidate passed admission/hash/backing controls (the seven-test filter
also includes two unrelated existing tests), all 108 pull tests, and the compiler
library: 1,959 passed, zero failed, six existing ignores. Logs:
`/tmp/fz-tfn49-admission-controls.log`, `/tmp/fz-tfn49-pull-controls.log`, and
`/tmp/fz-tfn49-library.log`.

Root independently checked this intermediate frozen binary:
`/tmp/fz-tfn49-candidate.yTwb0Y/fz2`, SHA256
`f75b1ed8f919ed1e41540338c892feb4a127c4dbffd1e1a91ab85a4ae81dfcf6`.
Output `/tmp/fz-tfn49-candidate-proof.DgQjoN` and log
`/tmp/fz-tfn49-candidate-proof.log` show all six goldens and backend/CLIF bytes
unchanged against accepted .50, with every producer/job work family unchanged.
Against the instrumented-old binary, every complete validation sum, event count,
and wave-size histogram is identical in all six doors. The representative
fixtures therefore show no selection-comparison reduction.

Cold review found that the accepted queue's pop and effective-visit counters
advanced together by construction. The final implementation retains only
`mutation_pops`; the redundant field and JSON alias are gone. The historical
old-algorithm evidence retains both because they differed there. A focused
shared-reader control now exercises equal-plus-changed group publication under
both input orders: the changed input advances generation, the equal input does
not, and Refresh cannot resurrect the invalidated reader or its subscriptions.

## Final frozen candidate

- Binary: `/tmp/fz-tfn49-final.ChN8MS/fz2`
- SHA256: `702106ab687e1d21dcdf65905985e9903e466159f193d5a62ab932e88a07b2b4`
- Tracked eight-path diff SHA256:
  `418b8f618d438cf7b8d37a70c114d17428938a13f65e1b69e5a53fab4868dd2a`
- New, explicitly formatted `pull/mutation_test.rs` SHA256:
  `50dd2f9cab33bbd6e71394eb6fc8e4cb6f621198474593dd237aa4ff22f87305`
- Independent output: `/tmp/fz-tfn49-final-proof.4UGxvc`
- Independent log: `/tmp/fz-tfn49-final-proof.log` (terminal success)

The final six interpreter/native goldens and all six backend/CLIF artifacts
remain exact against accepted .50. Every job, product request/evaluation/
settlement family, body walk, native function, and native byte count is unchanged.
Every validation sum, event count, and wave histogram matches instrumented-old
after removing its redundant visits field. In these fixtures its visits equal
pops, so this normalization removes no difference.

The production-path tests prove the following bounds and exact selections;
candidate comparison numbers below are upper bounds, not recorded exact totals:

| Case | Old pops | Final pops | Old comparisons | Final comparison bound |
| --- | ---: | ---: | ---: | ---: |
| 512 independent products, four repetitions | 2,048 | 512 | 2,096,128 | ≤22,528 |
| 512-leaf diamond | 1,025 | 514 | 392,448 | ≤22,616 |

Admission attempts and inspected edges remain 2,048/0 and 1,025/1,024
respectively. Initial sorting and heap insertion/removal comparisons all enter
the bounds. The new helper uses the existing move-only `OrderedWorklist`;
there is no second ordering algorithm or retained scheduling store.

Direct controls establish one admission-key clone per distinct product across
all strengths, no clone on rejected borrowed admission, zero key hashes for a
single-product wave, and linear actual Hash calls through promotion/growth in
the tested admission workload. Promotion moves the original inline key. Real
positioned-key controls preserve the seed vector, original heap inputs, one
map-owned input across strengths, and moved/recovered owned escalation keys.
Upstream seed/rooted-reader construction copies and unchanged dependency
unlinking are not erased by these claims. No total allocator or runtime speedup
follows merely from the synthetic comparison bounds.

Final source/test/docs cold review found no remaining actionable ticket defect.
The reviewer independently checked the corrected counter model, group control,
109 focused tests, strict Clippy, final binary hash and six-door proof. Their
initial acceptance excluded this then-in-progress measurement and remaining full
gates. A combined review on accepted .55 subsequently rechecked the restored
source, tests, documentation, gates and proof without an actionable finding.

## Historical pre-prerequisite local gates

- Focused pull suite: 109 passed.
- Compiler library: 1,960 passed, zero failed, six existing ignores;
  `/tmp/fz-tfn49-final-library.log`.
- Strict Clippy: passed.
- Repository formatting and explicit formatting of the new include-backed test:
  passed. `cargo fmt --all` alone does not traverse `include!` files.
- Serial fixture matrix: 537 passed; `/tmp/fz-tfn49-fixtures.log`.
- CLI/cross-process: 30 passed; AOT: one passed;
  `/tmp/fz-tfn49-cli-aot.log`.
- Workspace documentation: passed with one existing compiler doctest ignore;
  `/tmp/fz-tfn49-docs.log`.
- Default-parallel runtime: 209 passed, one failed;
  `/tmp/fz-tfn49-runtime.log`. This gate is not accepted.
- Diagnostic isolated runtime test: one passed; serial runtime: 210 passed;
  `/tmp/fz-tfn49-runtime-isolated.log` and
  `/tmp/fz-tfn49-runtime-serial.log`. These do not replace the parallel gate.

The failing unchanged test
`heap::heap_test::alloc_procbin_pushes_into_mso_chain_with_strict_layout`
observes global `live_count` as 1 after its own heap drops, versus baseline 0.
Independent diagnosis identified unannotated tests that allocate unrelated
SharedBins concurrently, outside the lifetime test's `serial_test` lock. The
same pattern affects Resource lifetime gauges. Source proves the interfering
interleaving; the failed log does not identify which allocator overlapped.
Runtime and Cargo files are unchanged by .49. Both gauges also have unconditional
production updates but only test readers.

That failure led to fz-tfn.55. It established exact owner-scoped observations,
removed the two unused gauges and five production atomic updates, passed its own
review and gates, and landed before this candidate was restored. The diagnostic
isolated/serial passes above were never used as substitutes for the failed gate.

## Combined accepted-.55 candidate

The complete .49 candidate was restored with `git stash apply` from immutable
stash `59f2fc17c7073583e9d9ecf4432973be446337b2`; the stash was not dropped.
Root compared all eight tracked and two new files byte-for-byte with the stash,
and all ten .55 commit paths byte-for-byte with `HEAD`. No merge resolution or
source edit was required.

- Landing base: `a7978bc09ec50d2d83c6173e30e80b353aa15b1d`
- Tracked .49 diff SHA256:
  `418b8f618d438cf7b8d37a70c114d17428938a13f65e1b69e5a53fab4868dd2a`
- Explicitly formatted `pull/mutation_test.rs` SHA256:
  `50dd2f9cab33bbd6e71394eb6fc8e4cb6f621198474593dd237aa4ff22f87305`
- Frozen combined binary: `/tmp/fz-tfn49-combined-final.V2fAvh/fz2`
- Binary SHA256:
  `a50d833d8d033a6ea746837680b5e16a7be7cf0073e931cd27370c3682d0e5df`

Combined gates all pass without a source change, retry, raised budget, new
ignore, or test serialization:

- Focused pull suite: 109/109; `/tmp/fz-tfn49-combined-pull.log`.
- Compiler library: 1,960 passed, zero failed, six existing ignores;
  `/tmp/fz-tfn49-combined-library.log`.
- Default-parallel runtime: 214/214;
  `/tmp/fz-tfn49-combined-runtime.log`.
- Serial fixture matrix: 537/537;
  `/tmp/fz-tfn49-combined-fixtures.log`.
- CLI/cross-process: 30/30; AOT: 1/1;
  `/tmp/fz-tfn49-combined-cli-aot.log`.
- Workspace documentation: passed with one existing compiler doctest ignore;
  `/tmp/fz-tfn49-combined-docs.log`.
- Strict workspace/all-target Clippy, repository formatting, explicit rustfmt
  for the include-backed new test, and diff checks: passed.

Root independently ran the unchanged verifier against accepted .55:

- Output: `/tmp/fz-tfn49-combined-proof.wdnWZu`
- Log: `/tmp/fz-tfn49-combined-proof.log` (terminal success, session 48496)
- Baseline: `/tmp/fz-tfn55-final-proof.xXBuIO`

All six interpreter/native outputs match their goldens with empty stderr. All
three backend and three CLIF artifacts are byte-identical to accepted .55.
Every typed job, product request/evaluation/settlement family, body-walk count,
native function count and native code-byte count is unchanged.

Root separately compared the ordered `ProductValidation` work payloads with the
instrumented-old run after asserting its obsolete `mutation_visits` equals
`mutation_pops` and removing only that redundant field. Work sums, event counts
and histograms are exact across all six doors: 455 range, 1,078 predicate and
2,017 take/drop events. Each native door adds one admission/pop and one edge,
as before. The ordered work payload sequence also matches the pre-.55 final .49
candidate. Product attribution metadata and timestamps are excluded: interned
input IDs can renumber across a rebuilt prerequisite without changing the typed
work or artifacts. Representative fixtures therefore still show no
selection-work or wall-clock reduction; the ticket's demonstrated reduction is
the bounded large-wave production path above.

The ticket-cold reviewer independently verified the restored hashes, accepted
.55 preservation, exact-pair semantics, ownership controls, all combined gates,
artifact/work equality, and complete old/new validation comparisons. No
actionable source, test, documentation, or total-work claim defect was found.

Final factual-record review accepted the corrected comparand without further
findings.
The old selector, post-pop duplicate handling, partial tuple return, and obsolete
refresh/duplicate-visit counters are removed; no temporary successful-value
print, allocator probe, or old-scan compatibility implementation is retained.
