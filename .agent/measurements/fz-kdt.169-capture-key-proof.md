# fz-kdt.169: transported-closure activation key

Measured 2026-09-06 at fz-tfn.51,
`40563eeb756636153df0aac67d01940864fe2556`. The experiment counts below belong
to that head; later accepted tickets had already moved five inventories from
the ticket's discovery baseline. Final acceptance was repeated after
fz-kdt.185 (`b5969795f8aaf2d3f39af7c822736a84da2b999f`) made the runtime collection
domains exact; that later base does not change the rejected-prototype census.

## Goal, signal, strategy

The goal was to determine whether this compiler can omit more capture
information from the activation key of a non-recursive callable transporter
while preserving dispatch-free static grounding. The signal was fewer semantic
activations and executables without new runtime dispatch,
widened capture lanes, changed artifacts, or changed behavior. The strategy
was to keep the static same-lambda `int`/`float` and dynamic three-door controls
green, prototype a flow-sensitive erasure in the existing demand lattice, and
measure its causal work across the whole corpus.

## What the context-free evidence proves

After closure-brand erasure, the key no longer knows whether two values came
from the same lambda or different lambdas. Therefore a context-free projection
cannot condition its answer on that distinction. In particular, erasing the
whole capture tuple (or keeping only its arity) would merge the static witness's
same lambda at one `int` and one `float` capture slot. The key would no longer
ground those executable capture lanes separately; a runtime choice would have
to recover the distinction.

This establishes the conservative law used here: without a flow-sensitive
proof that a transported callable's capture layout cannot become observable,
retain its capture tuple after erasing its brand. This rejects whole-tuple and
arity-only erasure as context-free ways to preserve dispatch-free static
grounding. It does **not** show either projection changes program semantics --
the three-door behavior remained correct -- or prove that every possible
capture-tuple component is universally necessary.

## Rejected flow-sensitive projection

The TDD prototype added capture-layout relevance as a fourth component of the
one `InputDemand` fact. It reused the existing forwarding graph and lattice
join: a slot kept its capture tuple if this body consumed callable identity, or
if return/forward flow reached a body that did. Otherwise the activation key
erased the whole closure literal. The actor-ring inventory RED turned GREEN,
while the static typed `FunctionId`/`int`-vs-`float` gate and dynamic
interpreter/JIT/AOT gate stayed GREEN.

The durable experiment is the ticket attachment
`fz-kdt169-rejected-flow-sensitive.patch` (SHA-256
`81aa29c5eef52e106c16f69e4060a81b23cf65467cd84ed29ebef7300c4afb1e`).
The rejected production mechanism was 62 additions and 6 deletions across six
files (`git apply --numstat` on the attached patch). The temporary review
prototype binary is `/tmp/fz-kdt169-full-prototype-fz2` (SHA-256
`facd015195a0928ade8496c1b0a193d092f2a3ac2e85ae66c4b9c2ebc07322d1`);
the retained binary is `/tmp/fz-kdt169-base-fz2` (SHA-256
`30498167a55d3fb5b1098dcb01d8aeba9e6440b681a4060987e6a187cce96981`).

Across the 478 fixtures that produce a backend artifact, the prototype changed
only three executable inventories:

| fixture | executables retained -> prototype | product evaluations delta |
| --- | ---: | ---: |
| `actor_ring` | 24 -> 22 | -27 |
| `mailbox_closure_each` | 31 -> 29 | -31 |
| `mailbox_closure_reduce` | 41 -> 39 | -31 |

Thus six executables and 89 product evaluations disappeared. Across all 478
fixtures, however, work-graph applies rose from 140,285 to 143,458 (+3,173).
Product evaluations fell from 172,177 to 172,088 (-89). The claim sweep ran
`fz2 --log-telemetry TRACE interp FIXTURE` and counted raw JSONL events:
`fz.compiler2.work_graph.applied` for work-graph applies and
`fz.compiler2.pull.product.evaluated` for product evaluations. Its attempted
`fz.compiler2.job.start` counter was zero because that event is not present in
these traces; no equality with applies is claimed. The retained arithmetic is
therefore raw-telemetry causal evidence, not an `--emit=stats` or time proxy.

The recurring cost comes from requiring and reading `Recursive`, joining the
fourth demand component, and transforming ignored slots on every relevant
keying run. This is one richer `InputDemand`, not a second authority, but the
extra recurring analysis is disproportionate to its narrow savings. The
prototype was therefore removed.

## Full-corpus controls and mover classification

The ticket attachments `fz-kdt169-corpus-sweep.py`,
`fz-kdt169-corpus-analyze.py`, and `fz-kdt169-claim-sweep.py` reconstruct the
sweep from the recorded base commit plus the attached prototype patch. The
sweep ran these four phases for each of 607 fixtures and both binaries, with a
30-second per-command timeout and four workers:

```text
fz2 interp --dump backend=... --dump activations=... FIXTURE
fz2 run FIXTURE
fz2 build FIXTURE -o AOT
AOT
```

The durable result set is also attached by basename:

- `fixtures.txt` (SHA-256
  `21b3cddc7835a100c7fa81069129cc151414119a3fc6a345700b2cbafc0c4888`);
- `retained-behavior.sha256` and `prototype-behavior.sha256` (each SHA-256
  `53a8197e69e39c9165e481b0f4526ba30df67c736165f98f1f79d5cb1caad598`);
- `backend-movers.tsv` (SHA-256
  `fc71646b5685ff504fe2457d08c8cf7f8ed8530027e6b78e6bc4a4743ac243c5`);
- `claim-movers.tsv` (SHA-256
  `417da557ebb08e03514feaad327fb1cd8792f6578e3a9f818d9db1b5e4a8ece0`);
- `work-movers.tsv` (SHA-256
  `ae26ba6ab6e9c4d4804f851cd120b7f02ae915158ee0d4b1210d2b71ff0d05d0`);
- `claim-totals.json` (SHA-256
  `bf4d8116f1e99138c07cd62be0722edd5325b736a802fc379415a7eef19c61b1`);
- `summary.txt` (SHA-256
  `87de08d768612222cd51468670d4ce7bb57f1018b46caa62237a1e357bf4daf5`).

The normalizer replaces thread numeric ids, hexadecimal addresses, and the
side-specific compiler/AOT paths. It does not alter other output. Each side's
behavior manifest has 7,284 entries (`607 fixtures * 4 phases * rc/out/err`).
The attached `retained-behavior.sha256` and `prototype-behavior.sha256`
manifests are byte-identical, with the hash recorded above.

There were zero normalized behavior or exit-status movers and zero root
activation-dump movers. Backend canon moved in 16 fixtures. Counts below are
`executables/plans/decision-test-nodes`, retained -> prototype:

| fixture | backend counts |
| --- | ---: |
| `00185_spawn_receive_capture` | 12/1/0 -> 12/1/0 |
| `00240_large_int_from_spawn` | 9/1/0 -> 9/1/0 |
| `00242_spawn_tagged_receive` | 11/1/3 -> 11/1/3 |
| `00288_spawn_with_captures` | 12/1/0 -> 12/1/0 |
| `00410_spawn_closure_capture` | 12/1/0 -> 12/1/0 |
| `00512_spawn_send_receive` | 10/2/0 -> 10/2/0 |
| `00513_spawn_new_fn_resume` | 11/2/0 -> 11/2/0 |
| `00515_spawn_receive_after` | 8/1/7 -> 8/1/7 |
| `00516_spawn2_heap_hint` | 8/1/0 -> 8/1/0 |
| `actor_ring` | 24/5/7 -> 22/5/7 |
| `closure_render_arity` | 21/3/14 -> 21/3/14 |
| `enum_reduce_suspend` | 15/1/2 -> 15/1/2 |
| `mailbox_closure_each` | 31/4/8 -> 29/4/8 |
| `mailbox_closure_reduce` | 41/7/20 -> 39/7/20 |
| `shared_heap_send_large_bitstring` | 9/1/0 -> 9/1/0 |
| `spawn_with_captures` | 12/1/0 -> 12/1/0 |

The three inventory movers are the intended reductions. In the other 13, only
key text changed where `spawn`, `fz_spawn`, `dbg`, or `fz_dbg_value` omitted
an unobserved capture tuple. All 16 plan and test-node counts are flat.

All 16 retained/prototype executable, dispatcher-plan, and decision-node counts
and canon hashes are in the attached `backend-movers.tsv`. No mover added
dispatch or widened a capture lane.

Twelve fixtures moved raw claim lifecycles. Each cell is
`distinct/first-appearances/retractions`, retained -> prototype; callsite
summary and target rows were identical throughout:

| fixture | Activation | CallSiteSummary/Targets |
| --- | ---: | ---: |
| `00279_enum_find_find_value` | 28/28/0 -> 29/29/1 | 26/28/2 -> 27/29/2 |
| `00280_enum_find_index` | 28/28/0 -> 29/29/1 | 27/27/0 -> 28/28/0 |
| `00284_enum_find_early_halt` | 17/17/0 -> 18/18/1 | 15/15/0 -> 16/16/0 |
| `00418_enum_count_range` | 52/52/0 -> 52/52/1 | 59/62/3 -> 59/61/2 |
| `actor_ring` | 25/25/0 -> 23/23/0 | 24/24/0 -> 23/23/0 |
| `dead_closure_capture_empty_list` | 39/39/0 -> 40/40/1 | 41/41/0 -> 42/42/0 |
| `enum_hof_three_distinct_closures` | 43/43/0 -> 44/44/1 | 51/51/0 -> 52/52/0 |
| `enum_reduce_halt_arm_order` | 26/26/0 -> 24/24/0 | 28/28/0 -> 27/27/0 |
| `mailbox_closure_each` | 33/33/0 -> 31/31/0 | 35/35/0 -> 34/34/0 |
| `mailbox_closure_reduce` | 43/43/0 -> 41/41/0 | 54/54/0 -> 53/53/0 |
| `mutual_recursion` | 10/10/0 -> 9/9/0 | 16/18/2 -> 15/15/0 |
| `with_index_users_keep_nested_list_elements` | 52/52/0 -> 52/52/0 | 56/57/1 -> 56/56/0 |

`actor_ring`, `mailbox_closure_each`, and `mailbox_closure_reduce` are the
intended final population reductions. The other nine have byte-identical
backend canon, root activation dump, and product-evaluation count. They are
transient schedule/lifecycle changes caused by the added `Recursive` wait/read.
Corpus totals were Activation 6,761/6,764/5 -> 6,757/6,760/11 and each callsite
family 7,263/7,430/167 -> 7,263/7,426/163. Exact rows are in the attached
`claim-movers.tsv`, and the aggregate is in `claim-totals.json`. The 449
fixtures where either causal count moved are in the attached `work-movers.tsv`;
448 increased `work_graph.applied`, none decreased it, and one was flat.
Product evaluations decreased in three rows, increased in none, and were flat
in 446. `mailbox_closure_reduce` is the one flat-apply row (782 -> 782), while
its product evaluations fell 1,121 -> 1,090.

## Retained pins

The retained inventory ratchet now pins all eight cost-fixture paths.
`00275_enum_count_member_reduce` moved from the non-matrix corpus root to
`fixtures2/behavior/enum_count_member_reduce.fz`, alongside one Elixir oracle
and one stdout golden. Fz-kdt.185 made the runtime collection domains exact;
its centralized warning-totality test now reads the promoted fixture, and all
three doors need no diagnostic sidecar. The compile-only port test and runtime
TODO were deleted: the oracle plus the run/interp/build matrix now own the
stronger contract. This is a move, so the all-`.fz` corpus remains 607 files;
the behavior matrix gains exactly three trials.

`00420_enum_take_drop_split` differs from its behavior twin only in comments;
their backend bytes and observed claim/work rows are identical. Prototype claim
movers are evidence about a mechanism that did not land, so they are classified
above rather than becoming another production claim-count authority. The static
same-lambda `int`/`float` typed-identity test and dynamic three-door witness
remain the semantic controls.

## Retained-key acceptance run

The experiment's actor-ring inventory target began RED at 24 retained
executables against the intended 22 and turned GREEN under the prototype. The
prototype was then rejected by the corpus work signal and fully reverted. The
new eight-fixture retained inventory ratchet is GREEN at
26/153/31/41/24/166/237/237.

The new oracle-backed fixture first ran RED on all three doors because no
golden existed; each reported the observed `{3, true, 6, {:done, 6}}` stdout.
At the experiment base they also reported two pre-existing runtime-domain
warnings, so a diagnostic sidecar temporarily made that intermediate gate
exact. Fz-kdt.185 then fixed those contracts. On the final base the sidecar is
deleted, the centralized runtime-totality test is GREEN, and run, interpreter,
and build are warning-free. `oracle_goldens_match_elixir` independently
confirms the stdout against the real Elixir program.

The static capture-layout gate formerly classified its interned types through
rendered strings. Rewriting it to typed `FunctionId`, `Ty`, and
`lit_arrow_shapes` comparisons first produced a genuine RED (2 detected
forwarders against 4): filtering for anonymous literals accidentally omitted
the branded identity-consuming `twice` bodies. Admitting both branded and
anonymous typed shapes made the intended four typed int/float splits GREEN,
still with zero dispatch plans.

At the frozen retained candidate:

- focused log `/tmp/fz-kdt169-integrated-focused.log`: inventory 1/1, static
  and dynamic capture semantics 2/2, erasure 1/1, same-shape sharing 1/1,
  runtime warning totality 1/1, the oracle-backed fixture matrix 3/3, the
  real-Elixir oracle check 1/1, and doctests 0 failed/1 ignored;
- `cargo fmt --all --check` and `git diff --check`: clean;
- strict clippy log `/tmp/fz-kdt169-integrated-clippy.log`: clean with
  `--all-targets --all-features -- -D warnings`;
- library log `/tmp/fz-kdt169-integrated-lib.log`: 1,961 passed, 0 failed, 6
  ignored;
- serial fixture log `/tmp/fz-kdt169-integrated-matrix.log`: 540 passed, 0
  failed.

The `/tmp` copies of binaries, raw corpus, manifests, TSVs, and gate logs are
temporary review artifacts and should be deleted after ticket acceptance. The
durable reconstruction recipe is the recorded base commit plus ticket
attachments `fz-kdt169-rejected-flow-sensitive.patch`,
`fz-kdt169-corpus-sweep.py`,
`fz-kdt169-corpus-analyze.py`, `fz-kdt169-claim-sweep.py`, `fixtures.txt`,
`retained-behavior.sha256`, `prototype-behavior.sha256`,
`backend-movers.tsv`, `claim-movers.tsv`, `work-movers.tsv`,
`claim-totals.json`, and `summary.txt`; the hashes above make reproduction
independently checkable.
