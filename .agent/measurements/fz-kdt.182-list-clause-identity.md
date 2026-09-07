# fz-kdt.182: decidable list-clause identity

Measured 2026-09-06 from exact base
`d3054abd302b62e56cc92b1f7d40973c5c2a7fa0`.

## Goal, signal, strategy

The goal is one interned identity for the concrete list denotation
`empty_list() | list(T) = list(T)`. The signal is exact `Ty` equality at the
type boundary, followed by one activation key, one fact revision, and one
executable at the production boundary. The strategy is to decide containment
from the two dimensions the list representation actually stores -- empty-list
membership and the non-empty element type -- and absorb a contained plain
positive clause at `Types::intern`.

This is deliberately narrower than full denotational type identity. It does
not normalize arbitrary DNF carvings or claim that the remaining equivalent
identities are the same defect.

## TDD result

The first test constructed `empty_list()`, `list(int)`, and their union. At the
base, `union(empty, list_int)` returned `Ty(3)` while `list_int` was `Ty(2)`.
The retained A15 test now proves both arrival orders return the exact
`list_int` handle.

The production proof reuses the existing activation-input revision test: both
arrival orders and `non_empty_list(int) | list(int)` produce the same
activation key, and reproducing the contribution advances no fact revision and
wakes no work. The existing eight-fixture inventory ratchet now also rejects
any two executable keys with the same exact root, function and need and
pairwise mutually-subtype inputs. It uses the memoized `Types::is_subtype`,
not diagnostic or canonical strings.

## Correct-by-construction boundary

For two plain positive list clauses `A` and `B`, `A` is contained in `B` when:

- every empty list admitted by `A` is admitted by `B`; and
- if `A` admits non-empty lists, `B` does too and `A`'s element type is a
  subtype of `B`'s.

That decision is exact for this representation. General conjunctive clauses
retain only the always-sound structural rule that a conjunction with a
superset of literals denotes a subset. A failed proof keeps both clauses.
Element subtyping goes through the existing operation-tagged World/`Types`
comparison memo. No display form, canonical string, raw-id order, downstream
dedup, new cache, or debug-only repeated semantic sweep is an authority.

## Full-corpus result

The sweep covered all 607 `fixtures2/**/*.fz` sources and 478 backend
producers with four workers. Each side ran interpreter (with raw telemetry,
stats, and backend canon), JIT, build, and the resulting AOT artifact. The
normalizer replaces only compiler/temp paths, hexadecimal addresses, runtime
thread/PID tokens, and dyld process ids. The two 607-source behavior manifests
are byte-identical at SHA-256
`e345777558d4f92594d86f06718678862f28445d159b13ae9068c63e97179f65`:
zero exit-status, stdout, or diagnostic movers.

Across the 478 backend producers:

| signal | base | changed | delta |
| --- | ---: | ---: | ---: |
| executables | 5,784 | 5,750 | -34 |
| typed-equivalent executable excess | 42 | 8 | -34 |
| typed executable classes | 5,742 | 5,742 | 0 |
| fixtures carrying a duplicate key | 16 | 6 | -10 |

Exactly ten fixtures have both a smaller executable inventory and less typed
identity excess. The count changes agree per fixture:

| fixture | executables | duplicate extras |
| --- | ---: | ---: |
| `00127_operator_sugar_rewrites` | 10 -> 8 | 2 -> 0 |
| `00276_enum_to_list_and_map` | 27 -> 25 | 2 -> 0 |
| `00277_enum_tier0_fixture` | 178 -> 176 | 2 -> 0 |
| `00420_enum_take_drop_split` | 237 -> 230 | 7 -> 0 |
| `00531_elixir_binop_operators` | 9 -> 7 | 2 -> 0 |
| `enum_map_family` | 153 -> 149 | 4 -> 0 |
| `enum_take_drop_split` | 237 -> 230 | 7 -> 0 |
| `enum_tier0` | 259 -> 257 | 2 -> 0 |
| `list_primitives` | 21 -> 19 | 2 -> 0 |
| `operator_sugars` | 18 -> 14 | 4 -> 0 |

The eight remaining typed-equivalent executable extras are in six fixtures and
belong to other denotational carvings; this concrete list rule does not hide or
claim them. The equal aggregate typed-class counts do not by themselves match
classes across separate Worlds. Normalized behavior is the cross-version
semantic gate; rendered backend differences corroborate where work
disappeared, but are not identity evidence.

The full-arena measurement drives every source and forms classes solely with
memoized mutual `Types::is_subtype` comparisons. Total interned allocations
fall from 32,620 to 32,353 (-267), while typed identity excess falls from 1,874
to 1,601 (-273). Typed classes total 30,746 at the base and 30,752 after the
change. Fifty-five fixtures allocate fewer types. The two take/drop twins each
have three more typed classes, so class counts rise by six corpus-wide even as
allocation and identity excess fall. Rendered inspection suggests those are
closure-arrow forms, but that is display corroboration rather than semantic
classification. The census compares authoritative typed relations within each
World; it never groups by display or canonical strings.

## Causal work

All changed causal totals decrease; none increase:

| signal | base | changed | delta |
| --- | ---: | ---: | ---: |
| `activation_analysis.defined` | 17,350 | 17,221 | -129 |
| `activation_inputs.defined` | 7,197 | 7,153 | -44 |
| `callsite.defined` | 18,493 | 18,400 | -93 |
| `return_type.defined` | 7,492 | 7,420 | -72 |
| `job.start` | 143,572 | 143,220 | -352 |
| `work_graph.applied` | 143,535 | 143,183 | -352 |
| `pull.product.requested` | 175,483 | 174,697 | -786 |
| `pull.product.evaluated` | 174,085 | 173,299 | -786 |
| `pull.product.settled` | 112,468 | 111,982 | -486 |
| `pull.product.validation` | 44,805 | 44,600 | -205 |

Sixteen fixtures move at least one causal count. Ten are the artifact/inventory
movers above; six retain byte-identical backend canons while doing less
analysis: `00285_enum_sort_stable`, `dead_closure_capture_empty_list`,
`enum_hof_three_distinct_closures`, `enum_oracle_smoke`, `enum_sort`, and
`fz_f98_range_map_converges`.

The checked-in target-fixture ratchets move only downward. On `00420`, final
reachable executables fall 239 -> 232. In the retained-request harness, cold
RuntimeDemand body walks fall 1,283 -> 1,239 and replacement-request walks fall
758 -> 730; at the fresh-process CLI boundary, cold body walks fall by the
same 44, from 1,280 -> 1,236. Its
activation identities fall 270 -> 261, callsite identities 459 -> 449, and
analysis evaluations 918 -> 905. On `fz_f98_range_map_converges`, activation
identities fall 76 -> 70, callsite identities 85 -> 79, shift wakes 31 -> 22,
and analysis evaluations 235 -> 212. All corresponding `uncaused` and
readiness-only counts remain zero.

## Historical claims at the current branch root

Fz-kdt.183 recorded 73 same-key extras, 39 byte-identical pairs, and 17
fixtures at its historical head. Intervening accepted tickets had already
moved the population: this ticket's exact base has 42 typed-equivalent extras
over 16 fixtures. The `00420` claim is 11 historically, 7 at this exact base,
and 0 after this cut. `00531` has 2 at this base and 0 after the cut. These
numbers are not silently compared across different heads.

## Reproduction fingerprints

```text
base fz2       37010287b43b06157cb678d206ae175be1a3eaab88de930c1ce7554b6bc1799d
changed fz2    b516d342b592b6fc39f9bddcd188de1f2f062328b0081e58275576b99cd370df
sweep harness  93daaf024eab624f54401062a024293bcdf4531f84182d8720ad9b7124c4d33a
compare script cd4ddb5ca3f6ff3c4d0186e83f014ffcd43172cdcbd2b2dba762f3065881c689
typed census   see attached fz-kdt182-typed-census.patch
```

The ticket attachments retain the two scripts, the replacement typed-census
patch and tables, aggregate summary, backend and causal mover tables, the
historical display-corroboration tables, and the two full result files. The
census patch is measurement-only; it and every other temporary probe are
absent from the landed source.

| attachment | SHA-256 |
| --- | --- |
| `fz-kdt182-corpus-sweep.py` | `93daaf024eab624f54401062a024293bcdf4531f84182d8720ad9b7124c4d33a` |
| `fz-kdt182-compare.py` | `cd4ddb5ca3f6ff3c4d0186e83f014ffcd43172cdcbd2b2dba762f3065881c689` |
| `fz-kdt182-typed-census.patch` | `710a1854a4b695985a3eb8f4ac60e2878d1879e915c1a7d3ab5541c015ee2de3` |
| `fz-kdt182-typed-census-base.tsv` | `6fc25cda962e2b1f6f04eb49c89b6d415f81aabdb8c6d8582b4918ee37d0fed7` |
| `fz-kdt182-typed-census-head.tsv` | `cc8dc0f4e0e8b7b0345e388dd571968e7e65f86870d127fcbdd755459f721006` |
| `base-00420-classes.txt` | `139486c69fe3a3c0002e44858158990050931d76bb26d30f65addfe5822f9eb5` |
| `head-00420-classes.txt` | `4094b23fd56ac4a1a86302658c6c20855e4a8d4bc4cfa6a130b2babe20f1134c` |
| `summary.json` | `879262b05f2c75dceee73be4c232011c0e78b9ea1de5001f180aa946663d0262` |
| `backend-movers.tsv` | `5bc1df90b6badf6d5fd8988d3beebd202747f73a0559488854dfa7b149bcfc14` |
| `work-movers.tsv` | `88ee10c6724d0ecd65d798da706b471ae8135f4d2bc2c4bb372a1d887eb69d62` |
| `base-behavior.json` | `e345777558d4f92594d86f06718678862f28445d159b13ae9068c63e97179f65` |
| `head-behavior.json` | `e345777558d4f92594d86f06718678862f28445d159b13ae9068c63e97179f65` |
| `base-results.json` | `5dea8e5944d234dfc1170a706f7ea969149809fd42d31bebfd024333986ee447` |
| `head-results.json` | `14872e77b0da792a12509ba15f9dd200bc0b03343d38e8640376b47c8d58ea08` |
