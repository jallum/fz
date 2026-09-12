# Correlated call-input publication

The production comparison starts at `55cec21ffc34c47aa52d6d50237f4cf696a358c0`.
Both binaries were built with `cargo build --bin fz2` in the same worktree.
The baseline contained only the new regression test; its production code was
unchanged. Baseline binary SHA-256:
`c24000b8881e38456b82125f091de61e3da94bd4a7671517dfe30ef0ac56aa19`.
Candidate binary SHA-256:
`f66d178cfd251c48fb67167e590da7bab3cd8b3650e5bbba2919bc661ba9394b`.

## Contract and red/green evidence

The regression drives real `main`, `relay`, and `sink` source through the
semantic pipeline. The two rows are
`(int, non_empty_list(int), non_empty_list(:left))` and
`(int, non_empty_list(:right), non_empty_list(int))`; assertions establish that
both select the same recursive relay and sink keys. It then inspects the actual
`AnalyzeActivation` conclusion and completes that conclusion through `World`.

Before deletion, the conclusion contains one blended sink row instead of the
two real rows: recursive publication has already allowed the fabricated row
to dominate both originals. The focused test fails with actual count 1 versus
expected count 2. After deletion, both original rows survive in the conclusion
and the published `ActivationInputs` alternatives. The existing exact-row
deduplication/publisher-ownership test also remains green.

The deleted coalesced-call rebuild and its sole call-resolution helper supplied
the invented row. Coalescing retains the walked targets, joined return evidence,
and original contributions. It needs no observation counter or second
resolution pass.

## Fresh-process measurements

For each binary, the command is:

```text
fz2 --log-telemetry <trace> interp --dump backend=<dump> <fixture>
```

The public traces are parsed by `fz::causal::parse_public_trace` and replayed
with `CausalReport::derive`; these are whole-invocation counts, including nested
macro work. No elapsed-time claim is made.

| Fixture | Formula evaluations | Product evaluations | Product settlements | Executables + wrappers |
| --- | ---: | ---: | ---: | ---: |
| `behavior/quicksort.fz` | 334 → 334 | 404 → 404 | 282 → 282 | 17 + 0 → 17 + 0 |
| `00420_enum_take_drop_split.fz` | 4154 → 4132 | 9569 → 9575 | 6588 → 6588 | 226 + 38 → 226 + 38 |
| `behavior/enum_predicate_search.fz` | 2474 → 2483 | 4743 → 4882 | 3041 → 3121 | 166 + 32 → 170 + 32 |

All fixture paths are relative to `fixtures2/`. Stdout is byte-identical on
all three comparisons. Quicksort's complete canonical causal multiset and
backend are byte-identical. Take/drop and predicate backend dumps preserve
separate callable input rows where the baseline contains a blended surface.
Predicate's executable delta is six added and two removed
`List.reduce_while_step/3` keys: the accumulator alternatives retain their
individual return payloads instead of the two broader joined keys.

Formula evaluations with no cause, undefined first uses, unsanctioned work
starts, and root scans are zero in every observation. The explicit unexplained
product-evaluation counts are 0 → 0, 15 → 15, and **25 → 33**, respectively.
The predicate increase is not accepted as explained work or hidden by an
exclusion: `fz-tfn.47` owns resolving those generic product retry causes.

The retained-request tests separately measure cold, unchanged, unreachable
edit, reached-leaf edit, and callee replacement. Exact rows increase predicate
cold demand body walks 592 → 596 and reached-edit walks 58 → 64; take/drop
reached-edit walks rise 63 → 70. Unchanged and unreachable requests retain zero
demand body walks and zero product evaluations. Numerical census pins reflect
these measured populations; every dispatch/construction escape count remains
zero.

## Verification

- Focused correlated-row red/green and existing deduplication/ownership tests.
- Full library: 1971 passed, 6 existing ignored tests.
- Serial fixture matrix: 642 passed, none failed or ignored.
- CLI suite: 30 passed, including separate-process causal/backend determinism.
- Workspace all-target/all-feature check and strict clippy.
- Formatting and diff whitespace checks.

Temporary measurement probes are removed from the source tree. The change
adds no evidence store, activation-identity policy, telemetry payload, or retry
exception.
