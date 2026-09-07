# fz-kdt.185 membership and `with_index` runtime warning contracts

Measured from exact base `40563eeb756636153df0aac67d01940864fe2556`.
The comparison compiled every `fixtures2/**/*.fz` source through `fz2 interp`
with `--emit=stats`, diagnostic telemetry, and a backend dump. It found 607
sources and 478 backend producers on both sides.

The ticket's original membership scope and its historical live
`Enum.with_index_list/2,3` warning report are one contract-evidence class: each
helper was total over the values its caller publishes, but its declaration did
not state that domain. This measurement covers both parts of the cut.

## Output contract

- `Enum.member_result/3` consumes only `{:ok, bool} | {:error, any}`, the result
  domain published by `Enumerable.member?/2`.
- `List.member?/2` consumes a list and any search value. Its second parameter
  intentionally remains `any`: searching `[1]` for `:missing` is valid and
  returns `false`.
- Both `Enum.with_index_list` arities consume lists; the mapper arity carries
  the element and index types through its callback result.

These are declaration facts, not activation observations. The runtime helpers
are total over those domains; values outside them correctly remain function
clause failures rather than being admitted by a wildcard.

## Corpus result

Normalized exit status and stdout had zero movers. The warning population fell
from 94 to 78. All 16 removed warnings were the four controlled runtime sites;
no warning or error was added:

| source | warnings | removed site |
| --- | ---: | --- |
| `00128_membership_sugar_rewrites` | 2 -> 0 | `Enum.member_result/3`, `List.member?/2` |
| `00275_enum_count_member_reduce` | 2 -> 0 | `Enum.member_result/3`, `List.member?/2` |
| `00277_enum_tier0_fixture` | 1 -> 0 | `Enum.member_result/3` |
| `enum_list_allocations` | 2 -> 0 | `Enum.member_result/3`, `List.member?/2` |
| `enum_map_family` | 15 -> 13 | both `Enum.with_index_list` arities |
| `enum_tier0` | 1 -> 0 | `Enum.member_result/3` |
| `membership_operator` | 2 -> 0 | `Enum.member_result/3`, `List.member?/2` |
| `with_index_users_keep_nested_list_elements` | 2 -> 0 | both `Enum.with_index_list` arities |
| `with_index_users_key_apart_by_element` | 2 -> 0 | both `Enum.with_index_list` arities |

The five diagnostics sidecars made wholly obsolete by this result were deleted.
`enum_map_family.expected.diagnostics` retains its 13 independent warnings and
only its two `with_index_list` blocks were removed.

## Causal work and products

The exact declarations add one `FunctionContract` derivation when a newly
contracted helper is activated: one for membership programs and two for the
program that activates both `with_index_list` arities. Across the whole corpus:

| causal signal | before | after | delta |
| --- | ---: | ---: | ---: |
| `function_contract.defined` | 2,754 | 2,764 | +10 |
| `job.start` | 143,562 | 143,572 | +10 |
| `work_graph.applied` | 143,525 | 143,535 | +10 |
| `activation_analysis.defined` | 17,350 | 17,350 | 0 |
| `pull.product.requested` | 175,483 | 175,483 | 0 |
| `pull.product.evaluated` | 174,085 | 174,085 | 0 |
| `pull.product.settled` | 112,468 | 112,468 | 0 |
| `pull.product.cache_hit` | 1,398 | 1,398 | 0 |

The added work is exact and edge-triggered: only a helper whose declaration is
loaded derives the new contract. It does not create an activation, product, or
downstream product evaluation.

## Backend artifacts

Twenty-eight of the 478 backend dump hashes moved:

```text
00128_membership_sugar_rewrites
00183_enum_take_list_range
00230_enum_take_chained
00275_enum_count_member_reduce
00276_enum_to_list_and_map
00277_enum_tier0_fixture
00279_enum_find_find_value
00280_enum_find_index
00285_enum_sort_stable
00418_enum_count_range
00419_enum_take_mixed
00420_enum_take_drop_split
dead_closure_capture_empty_list
dispatch_list_head_separates
dispatch_seat_element_blind
enum_hof_three_distinct_closures
enum_list_allocations
enum_map_family
enum_oracle_smoke
enum_predicate_search
enum_sort
enum_take_drop_split
enum_tier0
mailbox_closure_enum_hofs
membership_operator
unused_range_binding
with_index_users_keep_nested_list_elements
with_index_users_key_apart_by_element
```

Every paired dump has the same byte length. A second comparison normalized only
`runtime:Enum.fz` span ranges and `Enum`/`Enumerable` lambda source ranges; all
28 then became byte-identical. The declarations add source bytes before later
runtime functions, so their provenance ranges correctly move. Executable
content, types, dispatch, inventory, and all non-Enum provenance are unchanged:
there are zero semantic backend movers.

## Reproduction fingerprints

```text
base fz2       1229c63f19910ebc3e29486b41857c055b289dc91840c18f07ea14118dd0aa54
changed fz2    3aacc3ea219f874e642525e6ef850102b8d22dbf034388063d4aacc9a3686aae
base results   c508553670b486fa0a1705f58b8e8d4c69ef1748eeaddc7022c1ae45a0edfd97
changed result 1dc4e870899fdb149d28ac6149771a09eaafcbfaa7fb18fc6c87603a440f0fb1
sweep harness  a405cc8a94e090b1aa82a41eadceb53d32c4c4d607031d7100dc8d17cd9e5d13
```

## Reproduction

The attachment-ready evidence lives by basename on the ticket. Run the sweep
from the repository root. In separate worktrees at the exact base and changed
trees, `cargo build --bin fz2` produced the two binaries fingerprinted above;
copy each `target/debug/fz2` before building the other tree. Then run:

```text
python3 fz-kdt185-corpus-sweep.py BASE_FZ2 base-results.json --root REPO --workers 3
python3 fz-kdt185-corpus-sweep.py CHANGED_FZ2 current-results.json --root REPO --workers 3
python3 fz-kdt185-compare.py base-results.json current-results.json RESULTS
python3 fz-kdt185-retain-canons.py BASE_FZ2 CHANGED_FZ2 base-results.json current-results.json REPO CANONS
python3 fz-kdt185-normalize-canons.py CANONS/base CANONS/current canon-normalization.json
```

For every sorted `fixtures2/**/*.fz` path, the sweep runs exactly:

```text
FZ2 --emit=stats --log-telemetry TEMP/telemetry.jsonl interp \
  --dump backend=TEMP/backend.txt FIXTURE
```

It records exit status; stdout after replacing hexadecimal addresses and
decimal thread ids; diagnostics before the `telemetry stats:` section; every
emitted stat; and the backend byte length and SHA-256. It retains no raw
telemetry or backend corpus. The comparison emits the aggregate summary and
exact diagnostic, backend, and causal-work mover tables.

The canon proof re-emits only the 28 moved backend dumps. Its normalizer replaces
only `runtime:Enum.fz:<start>-<end>` ranges and source ranges in
`Enum.*#lambda@<start>-<end>` or `Enumerable.*#lambda@<start>-<end>` labels.
`canon-normalization.json` records all 28 comparisons and the empty semantic
mover list; no type, inventory, dispatch, user-source provenance, or other text
is normalized.

| attachment basename | SHA-256 |
| --- | --- |
| `fz-kdt185-corpus-sweep.py` | `a405cc8a94e090b1aa82a41eadceb53d32c4c4d607031d7100dc8d17cd9e5d13` |
| `fz-kdt185-compare.py` | `18c6469c0e714b080913c6dbfe01f4031ec4394f00e8131879f4d8c685392b6c` |
| `fz-kdt185-retain-canons.py` | `7d761cfbed5e51e0743a808eaa527e0b9237fce6e58fc865355ce0d132462f01` |
| `fz-kdt185-normalize-canons.py` | `46c1f52a18877aa1bf72b698f0b3311d98d9b1f5dbcef2a5502ff36c8e18c29f` |
| `base-results.json.gz` | `d551700d444c5f0b02c7ccec3727629b035bbd6816d7292ae018d0b0a541deb7` |
| `current-results.json.gz` | `f81b633f9a6edb19ac990c0587e6f9c5beda837368788f1385b6923c26c2afcc` |
| `summary.json` | `e9715e8430100aa9156a0745b35cb340f0d1e895d62fcaad6f8ac3b768272165` |
| `diagnostic-movers.tsv` | `9d366a05e7addbcf1e9ccf870dbd8b5370cb846576da849cb1b323bb28f24521` |
| `backend-movers.tsv` | `50eed13bea925cb8703f8b14903cdc7dfdcb8c84ac8b5967001deac95ea3327c` |
| `work-movers.tsv` | `ce0025b7365ceeb87af1d536128a25f1db3863a9a409006323b0153feba50bda` |
| `canon-normalization.json` | `0fc165438cb6331b882f0c9649b531228accafe1c53c781b18ed6bf59fa549c1` |
