# Fixture Conventions

A fixture is a tiny `.fz` program under `fixtures2/behavior/` that proves something
about the language. Each fixture pins its claim in the **most direct medium** for
what it is actually testing. This file defines those media, the rule for choosing
between them, and the realignment map for the current suite.

See `.agent/docs/fixtures.md` for the holistic orientation (anatomy, the
three-path matrix, pass/fail mechanics, the BLESS workflow).

## The media

A fixture proves its claim through one (occasionally two) of these:

1. **In-language assertion** — `assert(expr == expected, "why")` / `refute(...)`.
   The claim is a value equality or boolean invariant. The program checks itself
   and aborts (`Kernel.panic`) on failure, which the matrix scores as a failure
   on *every* path. No golden file. This is the default for behavioural claims.

2. **Rendering golden** — `dbg(x)` + `expected.txt`. Use only when the *rendered
   string itself* is the artifact under test (how a value prints), not merely a
   proxy for a value equality.

3. **Memory-floor stats** — `Process.heap_alloc_stats()` + (per-path) golden.
   Pins allocation counts/bytes. These are intrinsically cross-run and
   path-variant (`build` reuses cons cells; `interp` is the direct-IR baseline;
   `run` must equal `build`), so they stay harness-level — no single
   in-program assertion can express "run equals build". Do not dump the whole map by
   default: if only a few counters matter, print or assert those scalars and
   keep the sidecar as small as the actual claim.

4. **Expect-failure** — `expect: abort` / `expect: diagnostic` frontmatter +
   `expected.stderr`. The claim is that a program is *rejected* (compile-time
   diagnostic) or *aborts* (run-time panic). The program must exit nonzero and
   its stderr must contain the `expected.stderr` golden as a substring (a
   substring, not an exact match, so per-path prefixes like `fz interp:` and
   absolute source paths stay out of the pin). The default, `expect: success`,
   is the ordinary contract every other medium relies on: exit 0, goldens match.
   Use this for negative claims — what the language must *refuse* — which the
   positive media cannot express.

A compiler2 fixture under `fixtures2/` may instead carry a comment-frontmatter
compiler contract. That medium pins compiler2-native semantic/codegen facts:
metrics, selected call edges, or a dense canonical snapshot.

## Choosing rule

> Pin in the medium your *purpose* requires. One fixture, one job.

- Purpose is "this feature computes / dispatches / matches correctly" →
  **assertion**, no golden.
- Purpose is "this value renders as exactly this string" → **rendering golden**.
- Purpose is "this allocates exactly this much" → **memory-floor stats**.
- Purpose is "this lowers to this shape" → a **compiler2 contract**.
- Purpose is "this is rejected / aborts" → **expect-failure** (`expect:` +
  `expected.stderr`).

Behavioural correctness is path-invariant, so an assertion runs all three paths
for free. Compiler-shape and memory facts are not the program's behaviour, so
they do not belong in the program; they stay as contract metrics and stats
goldens respectively. Do **not** add an assertion to a shape-primary fixture: the
`assert` adds IR (an `==`, an `if`, a panic branch) and pollutes the very shape
it pins.

## Source Comment Convention

A fixture's source comments are a plain statement of facts about the current
state: what the fixture proves, in present tense, no adornment and no
chronology. They do not contain duplicated code — the code is the `.fz` file
itself. State the fact instead.

The `purpose:` frontmatter line is the single source of the one-line
description. The prose comments below the frontmatter are **optional**: include
them only when they say something `purpose:` does not — a mechanism, a
rationale, an allocation target. When `purpose:` is the whole story, the file
should just keep the frontmatter and the program.

## Realignment map

Decision for the current suite (the executable subset of this is the `fz-6df`
conversion arc):

**Assertion (behavioural-primary; convert `dbg`→`assert`, drop golden):**
`classify_two_clause`, `wildcard_then_specific`, `type_dispatch`,
`multi_clause_body_with_call`, `destructure_tuple`, `destructure_cons`,
`destructure_mixed`, `case_tuple_pattern_sequential`, `mutual_recursion`,
`tail_recursion`, `list_primitives`, `higher_order`, `polymorphic`,
`utf8_equality`, `utf8_pattern_match`, `keyword_lists`,
`guard_calls_pure_user_fn`, `map_three_path_parity`, `nested_tuple_producer`,
`relay`, `multi_relay`, `three_process_chain`, `concurrency_ping_pong`,
`actor_ring`, `spawn_with_captures`. Template:
`make_ref_distinct`.

**Expect-failure (negative claims):** `assert_abort_message` (a failed `assert`
aborts with its message). Template for the `expect: abort` / `expect: diagnostic`
medium.

**Assertion + `__info__` (module-structure):** `attributes`, `import`, `alias`,
`modules`, `nested_modules`, `cross_module_macro` assert their structure via the
synthesized `__info__/1` (see `module_info`) alongside the behavioural calls.
`fn_ref_ampersand` and `macro_inc` are top-level (no module), so they convert to
behavioural assertions only.

**Keep rendering golden (the string is the artifact):** `hello`,
`utf8_literal_print`, `empty_list_distinct_from_nil`, `utf8_smart_constructor`
(its `{:ok, utf8} | {:error, :invalid_utf8}` result is a sum type whose rendered
tuples are the informative artifact — both the `:ok`-wrapped decoded string and
the `:error` tag are visible in one golden).

**Compiler-shape pins live in compiler2 contracts under `fixtures2/`:**
`00547_compiler_contract_smoke`, `00548_contract_ast_eval`,
`00549_contract_closure_typed_captures`, `00550_contract_curried_add`,
`00551_contract_fib_tailrec`, `00552_contract_multi_clause`.

**Keep memory-floor stats (harness-level):** `append`, `reverse`, `filter`,
`tree`, `quicksort`, `enum_sort`, `enum_list_allocations`, `enum_reduce_suspend`,
`process_heap_stats`, `opaque_fn_value_join`, `map_key_unreached`.

**Keep golden — observed side-effect ordering:** `resource_lifecycle`,
`file_resource_lifecycle`, `file_handle`, `a-resource_aot_dtor` (the dtor firing is
observed through printed output order).

