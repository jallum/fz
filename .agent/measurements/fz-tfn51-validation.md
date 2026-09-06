# fz-tfn.51: rooted alternate-parent repair work

Status: final source, tests, documentation, local gates, deterministic work
proof, immutable artifact comparison and ticket-cold review are complete. Root
owns the single commit, close and CI-gated push.

## Accepted boundary

The ticket begins at fz-tfn.49 commit
`9a66849631f6e4a92650445bb360bbc6831e0315`. Its local source, semantic,
artifact, work and runtime gates passed before commit; exact CI run
`34036595774` subsequently passed lint and the full test/coverage job for that
exact head. The predecessor push gate is green.

The separately parked fz-tfn.46 candidate remains untouched pending the source
ownership policy in fz-tfn.53. Three unrelated untracked measurement paths are
preserved and are not part of this ticket.

## Current source signal

`RootedProducts` stores one reachability witness over committed membership:
`parents` names the selected proof edge and `children` is its reverse index.
When a selected parent edge disappears, `remove_edge` considers committed
alternate owners from `ProductMemo::membership_readers`. For each candidate it
calls `below(candidate, removed_child)`; `below` independently follows selected
parents toward the seed. A candidate below the removed child must be rejected
because reparenting to it would make the witness cyclic.

The sparse `DirtyWitness` added by fz-tfn.48 indexes only demanded dirty paths.
Its active prefix accelerates dirty traversal and wait admission; it is not a
complete ancestor authority for clean witness members. Reusing it as if it were
the full reachability graph would be unsound.

The current ticket description supplies a production-reachable shape whose
many alternate checks share a long clean prefix. Source inspection alone is not
RED evidence. The implementation agent must reproduce the shape through the
retained `OwnershipProducers`/drive seam at depth and width 8, 32 and 64,
separately observing candidate checks and actual ancestry visits across the
whole membership-repair request. Semantic assertions must pass before the old
work bound fails.

## Genuine current-base RED

The unchanged production algorithm was exercised through that retained drive
seam. The failing run is immutable at `/tmp/fz-tfn51-prefix-red.log` (PTY
session 98670, exit 101); the RED diff SHA-256 is
`87102237af28ec0210a232ffdb3450fb7d917f181a52c87767c4c1a061c0baf1`.

The new causal fields distinguish reverse-membership candidates inspected from
selected-parent witness nodes inspected. The observed totals were:

| depth = width | candidates | ancestor visits | required bound |
| ---: | ---: | ---: | ---: |
| 8 | 8 | 80 | 56 |
| 32 | 32 | 1,088 | 200 |
| 64 | 64 | 4,224 | 392 |

Before the final work assertion failed, the test proved the existing fz-tfn.48
admission bound, one evaluation and stable generation per affected owner and
child, stable prefix/alternate `Rc` dependencies, exact withdrawal of obsolete
owner membership and support, and zero new repair work for unchanged and
unrelated controls. Exactly K committed-owner repair reports show that the
quadratic ancestry work spans K ordinary `ProductCompletion::Single`
completions inside one real drive; a cache local to one `remove_edge` or one
completion cannot remove it.

The RED was then expanded without changing production. Immutable log
`/tmp/fz-tfn51-asymmetric-red.log` (PTY 56667, exit 101) retains the original
fz-tfn.48 healthy cap and observes:

| depth = width | shape | admission visits | candidates | ancestor visits |
| ---: | --- | ---: | ---: | ---: |
| 8 | one long alternate | 114 | 8 | 144 |
| 32 | one long alternate | 1,218 | 32 | 2,112 |
| 64 | one long alternate | 4,482 | 64 | 8,320 |
| 8 | two long alternates | 114 | 16 | 288 |
| 32 | two long alternates | 1,218 | 64 | 4,224 |
| 64 | two long alternates | 4,482 | 128 | 16,640 |

This exposed separate preexisting fz-tfn.48 admission work: the long alternate
adds exactly 64/1,024/4,096 = K*D visits. It is not hidden in this ticket or
charged against its cycle-proof result. Required tail ticket `fz-tfn.56` owns
that work and the concordant generalized nonleaf shared-prefix case; it blocks
the final CI cleanup ticket.

## Approved construction

The reproduced fz-tfn.51 repairs remove witness leaves. The retained `children`
reverse witness relation proves in one lookup that no distinct reached
candidate can be below such a key. Production may therefore reject a self
candidate explicitly and choose the same typed-minimum distinct candidate
without walking its parent path. Nonleaf removals retain the existing exact
parent-chain fallback.

This cut introduces no cache lifetime, invalidation, allocation, key clone,
subtree walk, detach/rebuild, or new ancestry authority. The leaf-index
inspection and every fallback parent visit remain causally counted. Direct self/back-edge,
nonleaf/stale reparent-detach-reattach controls and an independent parent-chain
randomized oracle must guard the construction. The ticket does not claim to
amortize nonleaf shared prefixes; `fz-tfn.56` owns their required holistic
cutover with the dirty-admission prefix work.

## Final implementation and deterministic work

The final public causal field is named `reparent_proof_nodes`, because its one
leaf child-index inspection is not an ancestor visit. The immutable RED logs
print that historical counter as `ancestor_visits`; instrumented-old JSON names
it `reparent_ancestors`. Candidate inspection remains separate in
`reparent_candidates`; detached-entrance inspections are included because they
are real alternate-repair work.

The leaf test is lazy. Absent reverse membership, self candidates and unreached
candidates perform zero proof-node inspections. A distinct reached candidate
causes one `children` lookup for the whole alternate selection. If the removed
key is a leaf, every such candidate is known external and no parent walk runs.
If it is not a leaf, the existing exact `below` parent walk runs and every node
is counted. Typed-minimum selection is unchanged.

All twelve retained-drive shapes at depth/width 8, 32 and 64 are GREEN in
`/tmp/fz-tfn51-final-pull.log` (111 focused tests, terminal success): the
original shallow alternate, one long alternate, two simultaneously valid long
alternates and genuinely alternating long endpoints. Each shape inspects
exactly K proof nodes (8/32/64), rather than the old 80/1,088/4,224 on the
original shape or up to 288/4,224/16,640 with two long candidates. Candidate
counts remain exact at K or 2K. The original fz-tfn.48 admission cap is
unchanged. Unchanged and unrelated controls emit no repair work.

The direct memo controls cover self membership, a valid leaf alternate, gaining
a real witness child and back edge, exact nonleaf cycle rejection, withdrawal,
reattachment and repetition so no stale leaf assumption can survive. The
randomized 1,200-edit oracle no longer calls the production `below` helper: it
independently walks selected parents, proves acyclicity and asserts that
`children` is exactly the reverse of `parents` after every edit.

Final seven-path tracked source/docs diff SHA-256:
`1ae48b2ebccf65631717bd3f77d4adead63f6caa9945b7f1c1241ee7219a37eb`.
The root-owned measurement is the eighth intended path. No unrelated untracked
path is included.

## Gates and immutable comparison

- Focused pull: 111 passed; `/tmp/fz-tfn51-final-pull.log`.
- Compiler library: 1,962 passed, zero failed, six existing ignored;
  `/tmp/fz-tfn51-final-library.log`.
- Default-parallel runtime: 214 passed; `/tmp/fz-tfn51-runtime.log`.
- Serial fixture matrix: 537 passed; `/tmp/fz-tfn51-matrix.log`.
- CLI and AOT: 30 + 1 passed; `/tmp/fz-tfn51-cli-aot.log`.
- Workspace docs passed with one existing ignored compiler example;
  `/tmp/fz-tfn51-docs.log`.
- Strict workspace/all-target Clippy, repository formatting, explicit rustfmt
  for both include-backed tests and `git diff --check` passed.

Normal immutable final binary:
`/tmp/fz-tfn51-final.wYwiRE/fz2`, SHA-256
`0780fd56048f928ef37ff21d2fe90192d4ed127547a9947cbc0b92f03487ff02`.
Instrumented-old binary:
`/tmp/fz-tfn51-instrumented-old.271jhV/fz2`, SHA-256
`1611364affe128b05ed669f9ced221bca7f2b929c3aa0f66aca5e8672eb656cc`.

Root independently ran both binaries through all three interpreter and native
fixture doors with verifier
`/tmp/fz-tfn46-proof-tool.jZn1af/verify.cjs` against the accepted fz-tfn.49
record. Outputs are in `/tmp/fz-tfn51-root-old-proof.3NVkJd` and
`/tmp/fz-tfn51-root-final-proof.vJArEZ`; logs are
`/tmp/fz-tfn51-root-old-proof.log` and
`/tmp/fz-tfn51-root-final-proof.log`. Every golden output matches with empty
stderr, and all job/request/evaluation/settlement families, body walks, native
function counts and code-byte counts match the accepted base.

`/tmp/fz-tfn51-root-comparison.log` proves the old and final binary hashes, six
byte-identical backend/CLIF artifacts, and exact ordered ProductValidation work
payloads after mapping historical `reparent_ancestors` to final
`reparent_proof_nodes`. The three representative fixtures perform no alternate
repair, so they corroborate semantic/work preservation but do not establish a
whole-fixture runtime speedup. The exact synthetic drive reductions above are
the authoritative performance signal.

The fresh ticket-cold reviewer accepted source, tests and documentation at the
recorded diff hash with no actionable finding. The review confirms semantic
equivalence of the leaf proof, lazy zero-work behavior, typed selection,
nonleaf fallback, independent oracle and absence of cache/subtree/allocation
machinery. It explicitly excludes this root-owned record and the then-pending
gates; a final factual record review follows before commit.

## Open pull requests

Root enumerated every open PR file inventory. Only stacked base PR #110 touches
the relevant paths, through `.agent/docs/fact-engine.md`; its head
`c2c723c63afdbda22078bb0a164cb313b8c7dfa8` is already an ancestor of this
branch. No other open PR changes `rooted.rs`, `rooted/`, or the two relevant
agent docs. There is no separate implementation to import or reconcile.

## Required final evidence

The accepted cutover must preserve exact alternate support, back-edge cycle
rejection, detachment and reattachment, seed reachability, unaffected branches,
owner withdrawal, equal allocation/generation reuse and artifacts. The measured
leaf repairs must not multiply shared clean-prefix work by branch count;
generalized nonleaf amortization remains a required fz-tfn.56 cutover. Unchanged
and unrelated requests must add no repair work. Candidate checks, ancestry proof,
and any proof upkeep must be counted together so work is not moved behind a new
authority.

No retained ancestor graph, broad request scan, display identity, permanent
clearance cache, compatibility path, raised budget, or temporary probe may
remain. Final source/docs, deterministic work comparisons, full relevant gates,
immutable artifact proof and a ticket-cold adversarial review are required before
one commit, close and CI-gated push.
