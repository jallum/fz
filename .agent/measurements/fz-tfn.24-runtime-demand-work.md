# RuntimeDemand body-work budget

The compiler predecessor is `534570e5a`; `4fc5616d8` additionally contains
harness-only telemetry-file ownership. The candidate removes one premature
`continue` from `derive_runtime_demand_fact`: a discovered construction target
and its available input vector enter the same snapshot before another body
walk. It changes neither the dependency scheduler nor the semantic formula.

`JobEffects.runtime_demand_evaluations` increments immediately before
`derive_executable_runtime_demand`. The existing `JobCompletion` carries that
count into public JSONL and causal replay. A prerequisite-only return reports
zero; successive local walks count separately. Replay excludes this state from
formula identity. There is no second event stream, retained counter authority,
or compiler comparison mode.

## Comparable mainline work

| Original fixture | Door | Mainline body derivations | Candidate body derivations | Candidate scheduler jobs |
| --- | --- | ---: | ---: | ---: |
| `fz_f98_range_map_converges` | run | 2,971 | 243 | 1,393 |
| `enum_predicate_search` | interp | 6,378 | 589 | 2,394 |
| `00420_enum_take_drop_split` | interp | 6,252 | 1,280 | 4,233 |

The mainline revision is `a3a9761d1209165e5230625b9347cf6b0ad09b83`.
The old counter increments immediately before `derive_member_demand`, so
the comparable unit is one executable body derivation, not one scheduler job
or one cone settlement. Range's native baseline is recorded in the ticket.
Predicate's exact-main three-run baseline is recorded in `fz-f98.23`; raw
`/tmp/fz-f98.23-enum-predicate.71630.jsonl` contains ten cone events totaling
6,378 (SHA256 `ee72eea45123a5d2aa884e397a526c1e7a782917c96b925f1ede4743d6aec072`).
Take/drop's raw `/tmp/fz-kdt5-cold-00420-a3a9761d.jsonl` contains
`[2, 2, 1028, 1028, 1028, 1028, 1068, 1068]`, totaling 6,252
(SHA256 `50fdfeb20ccd7e97981f46dd6158a8f9c73953a99a8a49fcd82714f7f8eb001d`).
The earlier 6,250 claim was an arithmetic error. A separate historical range
interp trace totals 2,401, but lacks proven exact-main provenance and is not
used as the mainline acceptance baseline.

The existing CLI observation bundle compiles each original fixture twice in
separate interpreter processes. Its actual-work pins are 243 / 589 / 1,280,
and its causal work and backend artifacts reproduce exactly. The existing
all-door test also reads range's native trace and compares 243 with the native
2,971 baseline. No additional compiler invocation was added for these ratchets.
Every non-initial RuntimeDemand job names changed content; readiness-only and
unattributed counts remain zero. Source inspection finds no demand-cone
collector, replay, round, retry, publication, or corresponding telemetry.

## Local cutover and retained requests

The existing five-request causal regression adds reached and unreachable leaf
functions to each fixture. These augmented sources are a separate comparison
population; they are not substituted for the original-fixture mainline table.

| Fixture | Cold walks before / after | Reached edit before / after | Replaced callee before / after |
| --- | ---: | ---: | ---: |
| range | 246 / 246 | 9 / 9 | 179 / 179 |
| predicate | 632 / 592 | 75 / 58 | 463 / 394 |
| take/drop | 1,451 / 1,283 | 83 / 63 | 878 / 758 |

Unchanged and unrelated requests perform zero body walks in every case.
Scheduler completions, changed outputs and wakes are unchanged by the local
cutover. The predicate cold ratchet fails with 632 versus 592 when the old
premature `continue` is restored (`/tmp/fz-tfn24-red-coherent-input.log`).
A synthetic replay test separately proves that changing a body-work count
neither creates a new formula identity nor constitutes new input evidence.
The old scheduler-completion-versus-cone-derivation assertion is deleted.

## Artifacts and runtime

Independent original-fixture interpreter and native executions use the copied
candidate `/tmp/fz-tfn24-after.n6luYj/fz2` (SHA256
`49fedc62aa0778487ee68de320599c550b39dab186c456198b6096b8ba5c8b77`).
All six commands exit successfully and match fixture output goldens. Backend
and CLIF dumps for all three fixtures are byte-identical to the predecessor
in `/tmp/fz-tfn27-after.2d8YSN`; every product-family evaluation and settlement
count and the scheduler-job totals above are also unchanged. Both execution
doors report the same actual demand-body counts. The predecessor's approved
unused-helper removal is preserved, not reversed to match older inventories.
Native codegen also preserves exactly 144 / 472 / 1,036 functions and
31,004 / 101,744 / 302,304 compiled bytes for range / predicate / take/drop.

Wall-clock fixture limits remain nontermination guards, not work budgets.
Deterministic derivations, causal records and artifacts are the acceptance
evidence; release-mode elapsed samples are corroborative only.

## Release-mode distribution

`cargo build --release --bin fz2` produces the copied
`/tmp/fz-tfn24-after.n6luYj/fz2-release`, SHA256
`61e5f32ccfb1d1a6b9aa670de51cfd104065a9319ee82ff5b7b68d8495530d08`.
After all local Cargo/test gates finish, run each original fixture through
`fz2-release run <fixture>` once as warmup, then 15 times each in round-robin
fixture order. Telemetry and dumps are disabled. Each child must exit zero
and match the fixture's stdout golden. A monotonic parent clock measures
the entire child process, including native compilation and execution.

| Fixture | Minimum ms | Median ms | p90 ms | Maximum ms |
| --- | ---: | ---: | ---: | ---: |
| range | 70.820 | 74.271 | 81.394 | 94.146 |
| predicate | 155.676 | 165.342 | 177.844 | 181.930 |
| take/drop | 346.678 | 369.535 | 402.528 | 413.552 |

These are one-machine candidate samples, not a before/after comparison or a
test threshold. The full 45 samples are in
`/tmp/fz-tfn24-release-distribution.log` (SHA256
`043ed966400b997c7d40c096e8f93be8f9b31ebc51d7fc3343f1b76420b9d815`),
using arm64 and rustc 1.98.0 (`88d9e12ae`, 2026-08-18); all outputs match. The deterministic
body-work reduction, not this distribution, proves the performance claim.

## Verification

- Full library: 1,896 passed, six existing ignored.
- Serial fixture matrix: 537 passed.
- CLI: 30 passed, including all three execution doors and cross-process work
  and artifact determinism; the final repeat passes after cleanup formatting.
- Strict workspace/all-target/all-feature clippy and formatting: clean.
- Documentation tests: clean, one existing ignored.
- No temporary print, comparison switch or additional fixture compile loop
  remains. The retained body-work count is part of the existing causal report.
