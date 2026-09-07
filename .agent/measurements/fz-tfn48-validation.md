# Retained formula dependency ownership

Baseline: `ad0ac47d3`, epic branch `fz-tfn/long-lived-recalculator`.
The independent fz-tfn.46 candidate is parked in immutable stash
`288b1531c515bf02f4ac9375ae422e8eb3c1ad58`.

## Contract and model

Final acceptance: all implementation, broad gates, independent artifact/work
proof and fresh cold review are complete. No Cargo handles or implementation
work remain; root owns staging, the single commit and ticket close.

Dynamic admission passes focused `7186` (98 controls) and
`14951` (99 controls). It replaces the existing frame wait Vec with a comparator
min-heap and routes exact clearance/reparent effects to the same pending attempt.
Static batch collection, off-path summary and provenance enums are deleted.
The retained scalar complete-proof path remains. Routing marks use the actual
request ID inside existing dirty nodes; no new epoch, key cache, root graph, or
pending Rc allocation exists. Same-attempt failure/retry releases selected and
queued admissions. Partial cancellation RED54362→GREEN13427 preserves the
still-demanded boundary owner's parent admission. Positioned owner-copy
RED8847→GREEN18795 transfers selected ownership into the frame; cancellation
also moves its boundary owner back out. Drive18795 passes40 controls.

The retained converse and alternate-reparent REDs59620 are GREEN7186.
Reparent-locality RED43972 (105>72 positions atD=K8)→GREEN59774 across8/32/64
reuses the exact clear active prefix. Whole-drive comparison bounds are n log n;
original3N witness/12N maintenance bounds remain unchanged. Heap swaps each
follow a counted comparison, bounding logical relocation without redundant
telemetry. The utility has no Clone bound and retains input Vec/payload storage.

Independent immutable checkpoint `a116067a` is at
`/tmp/fz-tfn48-admission.ZxOuo0/README.md`; parent report
`/tmp/fz-tfn48-admission-proof.pdRCcz/README.md` reviews all28 differences as
request-only reductions. All6 goldens/no stderr, all3backend+3CLIF bytes, every
job/evaluation/settlement/bodywalk/nativefunction+byte family equal baseline.
Interp requests2037→1939,5080→4814,10392→9940; root requests70→10,175→10,247→10.
Cache-hit reductions38/101/215 plus validation-only root reductions60/165/237
account98/266/452 requests. Native root-backend request counts are one lower
on each side; request reductions are identical. Native total requests are
2039→1941,5082→4816,10394→9942. This historical binary predates the
partial-cancel and selected-owner transfer fixes; the final proof below
supersedes this checkpoint.

The distinct-parent once-only prototype pin was corrected with parent approval:
immutable ad0 source selectsC3 before unobservedowner5→D2, so C first discovers
D2 then resumes once. The test observes those exact outcomes. This baseline2
is source-derived, not a measured execution; it does not relax healthy budgets.

Final-review correction: restored interior-entrance admission RED72695 (reader2
vs1)→GREEN6730 emits only successful external restoration entrances through the
existing reparent event. No descendant scan/store is added. Recursive publication
controls73707 cover inner-before-outer clearance and cancellation from an
ordinary suffix in the same group. Full library56652 had1944passed/6ignored and
one public trace pin relying on an eliminated incidental cold cache hit;
parent-approved deliberate retained reuse preserves all payload assertions and
adds exact root-hit coverage (GREEN16192). Fact consumption ablation20752 proves
ascending order fails; descending restored. Owned frame storage RED8847→GREEN18795
removes the introduced positioned input copy without changing existing diagnostic
copies. Final fmt/diff check and strict workspace/all-target Clippy47268 pass.
Workspace library62170 passes: compiler1946 passed/6 existing ignored,
runtime210 passed. Log `/tmp/fz-tfn48-gates.ZjjGKR/library.log`.
Final binary build94641 passes; immutable
`/tmp/fz-tfn48-final.I3A9oR/fz2` SHA256
`7e49e354cd3d6e0ebbd25baa40a98f04017e13f8ede53978e7c1d640a6935d55`.
Its README records tracked diff `a83c6ae149ba47020b99aa61ee68d507b28b466b9e18c00b902d0f77b142b5d7`
and all new-file hashes. Independent final proof68566 plus report comparison
0c7d6e accepts this exact binary: all six outputs and artifacts/work match the
reviewed checkpoint, with only the same28 accounted request reductions.
Report `/tmp/fz-tfn48-accepted-proof.kYZFpt/README.md`. Serial matrix65393
passes537/537. AOT40096 passes1; docs24240 passes with1 existing ignored
compiler doctest and no runtime doctests. CLI40096 passes29/30 with a cache-hit
budget15→7: measured181before/after logs remove3materialized+3shape+2callable
cache queries and9validation-only root requests, all evaluation/settlement
families unchanged. Root independently verifies559f3b and approves only this
downward pin correction, preserving239 settlement/generation/changed counts,
0unchanged/displacement and each recursive effect-member cache hit1.
CLI64258 passes30/30; production source/binary stays frozen. Test-only diff
`88e424651933c2abfd42557f2ebb9f09404863095d430a8ab738b11398a01e28`
adds `tests/fz2_cli.rs` to the inventory; aggregate tracked diff is
`bcf980962472e19a8b0e0ff445c7847bb12f43f9a286600c0ae3f96bcb64b92c`.
Fresh cold review accepts the supplemental test-only change and final tracked
diff; final strict Clippy24496 passes after clean fmt/diff checks. No
implementation work is deferred. Root owns staging/commit/close, not this agent.

### Structural cutover accounting

Removed production mechanisms: semantic-sorted unordered dependency validation;
recursive shared external dependency union/preparation; prior pending-attempt
unions; flat rooted dirty inventory and repeated discovery/sorting; unused
ordinary staged peers, one-element completion batch and current ordinary
copublished emitter. Historical public decoding remains active. Construction
prototypes removed at cutover: ProductDemand/RootedStale, static pending
frontier collector, active off-path sibling summary and its summary-only pin.

Retained authority is one World for facts and one ProductMemo for product
values/generations/current observations plus committed membership witness.
New inline observation data records the actual rooted read boundary and
delivery; PendingProduct owns its original request and optional live frame
routing position. Sparse nodes index existing dirty witness paths, with a
first-live-child cursor and request marks only for current admitted work.
The cancellation slot and exposure Vec contain transient drive effects and
are drained/released on teardown; neither retains value or membership answers.
The existing drive wait inventory is one move-only heap per suspended frame.

Storage proof is scoped: equal payload Rc/generation retained; observation map
and membership storage moved; borrowed positioned validation edges; selected
positioned key transferred into/out of frame; heap Vec/payload addresses
preserved with a non-Clone item. IndexMap adds dense storage and recursive
members have individual immutable Rc records instead of one shared union, so
total allocator calls are not claimed unchanged or reduced. Heap logical moves
are bounded by counted comparisons and actual push/pop operations, not another
redundant public metric. Preexisting diagnostic wait copies remain separately
scoped outside this implementation; no new owner copy is hidden behind them.

Current producer observations own validation. Ordinary product reads retain
first-observation order in one IndexMap. Facts retain reconciled World
snapshots. Recursive completion retains each member's own reads, including
internal edges stamped with the co-published final generations. Equal values
retain their allocation and generation. Atomic publication excludes already
solved peers from its invalidation wave.

Removed: semantic-sorted dependency-bag validation, the shared recursive
external-read union and its deep-copy preparation, and unions of prior pending
attempts. Each member retains one immutable Rc dependency snapshot: the guard
keeps observation storage borrowed while complete validation clears memo
readiness. Edge keys are borrowed, including positioned keys with boxed input
types; they are not deep-cloned per edge. Ordinary baseline already used Rc;
recursive baseline shared one union allocation, so this is not a claim of
unchanged total allocations. Pending attempts retain only current
reads and do not publish prospective membership.

One transient checked traversal validates cycles. A completely successful
traversal clears checked dirty state atomically and refreshes only boundary
readers. Failed traversals cannot justify later sibling membership. Rooted
membership uses the existing parent witness to validate owners before their
children; transient witness permissions are traversal state only.

The actual rooted read also records its boundary among ordered observations.
Both committed and live pending validation check earlier ordinary controls
before that witness. Registration alone never authorizes its old seed. A
pending formula which reached this boundary can wait on further members
without reevaluating its packaging formula; missing ordinary observations or
invalidated controls cannot resume the boundary.

## Established signals

All following synthetic controls exercise ProductReadContext/ProductDriver;
ordinary and recursive control tests use the production product-drive seam.

- Baseline direct ordinary control: RED, obsolete child is the only producer
  attempted before changed Selector (session45416; repeated with production
  drive in72421).
- Baseline direct recursive control: RED, obsolete child is the only producer
  attempted before A's Selector (83138; production drive72421).
- Baseline indirect ordinary and recursive selectors: both RED, same obsolete
  work despite initially unchanged wrapper generations (57708).
- Baseline pending reread: RED, old attempt's dependency remains alongside
  current attempt (59992).
- Corrected ordinary direct/indirect controls: GREEN72518, including equal
  selector exact Rc/generation and no reader evaluations.
- Pull suite: 64 GREEN29162, including discordant recursive snapshots,
  recursive edge replacement, exact owned external dependencies, membership
  alternate support/cycles and equal readiness.
- Corrected recursive direct/indirect controls: GREEN13381. Retained edges
  survive relevant input growth and narrowing; both member generations move
  together, repeats evaluate no member. Selector equality retains allocation
  and generation; selector deselection attempts no obsolete child.
- Shared-input rings of 8/64/256 members: GREEN13381. Exactly N dirty vertices
  and 2N product-edge scans; one boundary refresh, zero cleanup ordering
  comparisons. The next validation does no work. This measures generic ring
  validation, not rooted sorting or allocator calls.
- Rooted owner-before-child unit: RED82393 before witness traversal, choosing
  old child0 instead of owning seed2.

## Source prerequisite separation

The healthy closure source changes 41 to42 and shifts its source offsets to
avoid the separately tracked same-label collision. It discovers old generated
identity from LowerFunction's FunctionDefined output, so it does not require
fz-tfn.46's new function-kind fact.

With generic value ownership alone, the source control fails materializing
obsolete generated function31. `/tmp/fz-tfn48-source-product-trace.log` records
refreshed main/new32 followed by Backend31 → ABI31 → Effects31 → Materialized31.
Materialization panics at jobs/artifact.rs141.

With witness-owned rooted validation, interp returns42. The phase trace at
`/tmp/fz-tfn48-source-phase-trace.log` has replacement marker line142 and no
old31 product requests after it. Baseline semantic fact demand still runs
DefineFunction31 (lines173/190) while servicing root/main prerequisites.
That routing is fz-tfn.46's independently parked responsibility: its restored
source tests must retain the no-invalid-old-definition-job assertion. This
ticket's source boundary asserts no obsolete product request and result42.

## Historical implementation controls

The displaced-root shared-selector sibling test failed35807 with an actual
obsolete-child attempt and passed92281 after stopping at the first failed
retained validation. Public JSON work roundtrip and focused validation suite
passed51320. Membership-storage clone ablation failed32526 as expected; the
move has been restored. These focused successes are not commit readiness.

The cumulative equal membership-chain regression was pinned by RED6774.
For eight directly invalidated Unit-valued members plus their
packaging product, one request performs64 witness visits and9 packaging
evaluations. This confirms quadratic whole-request discovery, despite each
individual visitor being linear. The producer test uses the same telemetry
instance as the real product driver; no witness work is hidden in a fresh bus.

Root-control test26630 independently failed by requesting an old unavailable
seed before refreshing its selector. Recording the actual observation boundary
passes78497 for retained and waiting formulas with direct and indirect controls.
Pending boundary resumption reduces the eight-member chain to2 packaging
evaluations, but77211 remains RED with43 witness visits: repeated ancestor
discovery is still quadratic and no work acceptance is waived.

Changed-head/equal-tail control52699 separately pinned64 witness visits and9
packaging evaluations at N8. Standing rooted contribution changes incorrectly
invalidated each waiting attempt again, even for later equal publications.
Both chain controls now cover8/32/64 with forward/reverse/permuted invalidation
order. The other69 focused pull controls pass51845; the known chain is excluded
explicitly, not treated as an acceptance pass.

The typed rooted observation distinguishes Waiting from Delivered. A rejected
preserve-all-pending proposal fails89327 by following an obsolete ordinary
suffix after rooted readiness changed; the typed state passes84457. Repeated
delivery also exposed early acknowledgement:52260 incorrectly produced an
answer after a waiting attempt consumed its root changes. Reading now retains
the existing changes inventory until accepted publication;76962 passes, and
failure/repair coverage passes in71 focused controls38819 (both chain controls
excluded). Rejected publication retains changes too (GREEN7855).

Prefix work is separately pinned: an eight-observation prefix with an eight
member chain rescanned64 ordinary edges (RED71808). Capturing delivery validity
from actual read outcomes once at the rooted boundary, then relying on existing
pending reverse-edge invalidation, removes those rescans (GREEN56276 across
8/32/64 and three invalidation orders). No per-resume map scan remains. At that
checkpoint rooted witness traversal still blocked acceptance; the sparse
advancement and complete-proof controls below resolve it.

Edge-only validation telemetry was previously dropped (RED51654); emitting on
any nonzero work passes31961. Clean zero-work validation remains event-free.

## Interim independent artifact proof

The immutable intermediate binary is `/tmp/fz-tfn48-interim.f4lCuz/fz2`,
SHA256 `00f6ec8ccf1767b68bfef960916e5ccdc3c53e809186413858c555e1814ad400`.
Its README identifies exact tracked/untracked source diffs. This predates the
prefix-rescan removal and is not a final freeze.

Root's independent report `/tmp/fz-tfn48-interim-proof.sX8i0l/README.md`
(session77120, terminal0) verifies all six original interp/native goldens, no
stderr, three backend and three CLIF artifacts byte-identical to24 baseline,
and exactly unchanged job/product-evaluation/product-settlement families.
Jobs are1393/2394/4233 and body walks243/589/1280 on both doors. This healthy
control evidence does not waive the known retained-chain work regression.

## Ownership and cumulative work verification

The sparse DirtyWitness index replaces the flat dirty HashSet and
per-read sorting/permissions/path scanner. Sparse nodes carry direct dirty bits
and live indexed witness-child links; the active cursor advances only through
authoritatively cleared owners. Marking grows only the previously unindexed
upward suffix, without a per-mark temporary path allocation. IndexMap first/
get_index_of/swap_remove avoid repeated wide-child scans. Alternate reparent
relinks the sparse branch and truncates only a changed active suffix;
off-active reparent does not rewind it.

Equal chain GREEN11971 and all77 focused pull controls GREEN47968 include the
changed-head and prefix variants, sizes8/32/64 and three invalidation orders.
The original3N witness-visit and2 packaging-evaluation bounds are unchanged.
Successful replacement without a rooted observation retires only its own
witness (RED24152→GREEN39624), preserving another reader's subscriptions.

Active-path reparent retains the unaffected prefix and lets existing pruning
repair the changed suffix. RED21062 repeats90 witness positions at N8 when
one dirty leaf toggles between two local supports K=N times beneath N unchanged
ancestors; GREEN87179 uses suffix-only truncation at sizes8/32/64. Later
GREEN41160 covers a dirty alternative parent, surviving old sibling, and wide
frontiers8/64/256 with N+1 positions and linear total maintenance. Whole-chain
equal/changed-head/prefix cases include all mutation events from before
invalidation, bounding maintenance by12N without increasing original3N visits
or2 packaging evaluations. Equal owners retaining their next edge and adding
one leaf also keep2 packaging evaluations, with work bounded by the2N affected
members. These added controls initially passed the corrected implementation.

Historical cold regressions prevented freeze after77 focused tests:
80848 failed both new dirty-sibling insertion and off-active alternative
reparent: reverse indexed-child traversal leaves appended work behind the
active cursor. The correction (GREEN24516) uses the first live child and forward successor
order, so appended off-path work stays ahead without a prefix reset.
The production-path dirty-cycle-prefix test also failed (terminal command
chunk18ed64): at N8, A/B equal validation repeats40 ordinary edge scans versus
the bound8 while membership-chain owners settle. Selector is reproduced equal
through the real driver before this request, establishing the dirty prefix.

The always-deferred Validate driver proposal was rejected on a static
one-root counterexample: R includes A/B and both read retained R, so separate
fresh waits can alternate A→B→A. No such result/queue was implemented. The
implementation invokes the existing complete member walk+atomic cleanup
locally at the selected rooted boundary; nested root/value obligations must
remain inside that full checked traversal. No private SCC/fixpoint solver.
Cycle-prefix control is now GREEN98217 across sizes8/32/64. Sibling root/value
backedges plus missing-child failure/repair are GREEN53455; these initially
passed the complete-walk implementation and pin a rejected proposal, not an
original-baseline defect. Shared-ancestor refinement first exposed23 vs16
witness positions (RED43683), then1 vs0 redundant active-reader refreshes
(RED99996). Existing pruning now advances past its already-inspected surviving
parent, and only the active validating reader's redundant Refresh is deferred
to the outer proof. Nested proof work is accumulated transiently and emitted
once at the actual validation boundary: the original one-event,2N witness,
N+1 vertices,zero edges/refreshes pins remain intact.89 focused controls are
GREEN82776 with no warnings. An independent member proof followed by a stale
later reader control keeps that reader unsettled, reports the independently
settled member, and repairs successfully. The positioned-storage control moves
a dependency key with32 boxed input types without changing its map-element or
input-buffer address; this is storage-move evidence, not total allocator calls.

Same-request ready cleanup RED8451 reports2 sparse updates instead of3;
GREEN38463 includes disposal before emission and leaves unchanged follow-up
event-free. Replacement/retirement disposal RED54818 reports3 instead of4;
GREEN76034 covers both replacing a waiting witness and retiring it. Exact
touched-root mutation/commit maintenance is drained at that operation using
the existing validation payload; mutation events do not label Dirty/Invalidate
work as refresh visits. Successor ascent, discarded active positions, sparse
node/marker/link changes, and pruning inspections are counted. Whole-chain
controls capture from before invalidation through completion, including these
separate mutation events; branch and cumulative controls above are green.

Pending membership handoff RED11912 proves that the noncurrent member of a
real production-drive recursive completion loses its child. GREEN41838 removes
the premature pending-membership clear. Current prospective membership stays
in the existing attempt and publishes only on accepted completion; waiting,
abort and rejected-completion lifecycle controls retain old committed edges.

## Rejected gate candidate: healthy-work regression

Pipeline and instrumentation docs describe the current ownership, continuation,
acknowledgement, sparse advancement and operation-local accounting. Formatting
has run. Public validation controls (14,6234), source replacement (44c587), and
full library (91891:1928passed/6existingignored) are green without warnings.
Serial fixture matrix71892 is also GREEN537/537. These passes do not establish
acceptance: root's independent comparison rejects the frozen gate binary
`/tmp/fz-tfn48-candidate.7iPB2o/fz2`, SHA256
`a0ba2affc64daa868602cdb2e9db68fce1558f865691084d1684a2ad7c114556`.
Report: `/tmp/fz-tfn48-final-proof.MajmJX/README.md`, session74511 terminal1.
All six interp/native goldens, stderr, backend and CLIF artifacts, job and
settlement families, body walks, native function counts and bytes match the
baseline. Producer evaluations do not: both doors show range backend109→107
and callable156→162 (net+4), predicate backend284→279 and callable483→485
(net−3), take/drop backend386→401, callable716→733, shape7015→7007 (net+24).
No increase was waived; this candidate held subsequent gates until correction.

Range's extra calls are initial prerequisite waits: two fn175 input0 products
go1→2 by waiting on fn82 value2; each of those two fn82 products goes1→3 by
first waiting on its shape, then on input2's callable construction. Actual
order first diverges after backend fn20/arrow314: baseline visits the sibling
fn20/arrow248, candidate descends into fn31/arrow314. Thus DFS advancement
changes prerequisite availability, beyond swap-removal's sibling promotion.
This candidate was blocked on extra work, not wrong output or settled content.
Its replacement checkpoint and current final gates are recorded above.

### Historical scheduling prototypes (all superseded)

RED20227 exposed the DFS prerequisite loss: seed includes A/B, A exposes C,
and C reads B. Guarded frames addressed bare-batch revocation RED31531 and
nested cancellation RED21685 (GREEN21438); exact originating attempt, oldest
registration, replacement/slot reuse and teardown controls passed18765.
Ordinary pending dependencies stayed inline throughout.

Sibling-only batching34266 passed94 controls but missed distinct-parent
prerequisite opportunities. Full-frontier10237 passed96 controls and
RED43269's exhausted-prefix scan using an active sibling summary. That
prototype's once-only distinct-parent expectation was later shown unsupported
by baseline observation order and corrected explicitly, as recorded above.
ConverseRED22321 rejected fixed batches: A1 exposesC2 while queuedB3 readsC;
newly exposed C must compete with remaining old work. ProductDemand,
RootedStale, the pending frontier collector, and the active sibling summary
were removed during dynamic-frame cutover. They are not retained compatibility
paths. No healthy evaluation increase was accepted.

Real fact-pump RED61246 is GREEN26956, including the still-selected undefined
root error counterpart and all38 existing product-drive error/lifecycle controls.
Invalid initial source fixtures80798/39081 were not behavioral RED evidence.
At each pump iteration exact delivered movements reconcile before further
requested-fact expansion; cancellation remains pending for the owner-frame
handler. Genuine job errors are not blanket-suppressed.

Production reachability audit finds no writer for the old `staged` ordinary
peer vector: only the actual anchor was ever appended. That field, completion
tuple slot and assertions are deleted; ordinary Single completion also removes
its one-element vector allocation. Recursive publication keeps duplicate and
semantic-identity guards, snapshot conflict checks and atomic final-edge repair.
The redundant ordinary batch-order fixture is deleted; diamond/final-edge
controls use the genuine recursive completion boundary.72278 reports95 GREEN
and only the known22321 static-batch RED. Unreachable ordinary copublished
emission/current-enable check is removed; historical public decoding stays.

Cold review also identified stale shared-union documentation in fact-engine.md;
that section and membership prose are corrected. The docs-only supplemental
patch is retained beside the gate snapshot with SHA256
`6824c33fbe6bb4b2ac19e1dc486494b6ddd6b424a8f28b3ad46a443a0c3d6742`.
No acceptance pin has been raised. Temporary source print probes have been
removed. No ticket commit/close has occurred.
