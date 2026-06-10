# Macro Expansion

Macro expansion is compiler2's quoted-source rewrite layer. It takes quoted AST
roots on an Fz heap, runs `defmacro` bodies against that same heap, and hands
back quoted AST roots that the rest of compiler2 can keep treating as source.

The recursive rewrite engine lives in `src/compiler2/quoted_expander.rs`.
Scope publication and demand-time function staging both call that same engine;
they differ only in where expansion starts and what they do with the expanded
root afterward.

Three pieces matter:

- source publication decides what exists at module scope
- staged function expansion decides what a demanded function body means
- macro runtime turns a defined `defmacro` into something the backend
  interpreter can run

The same macro executable path serves both item macros and body-local macros.
The difference is when expansion happens.

## The Two Expansion Sites

Compiler2 expands macros in exactly two places.

**Item macros expand during `ScopeCode` / `DefineModule`.**
An item macro can create sibling definitions, so module scoping cannot proceed
until the expansion result is known. `ScopeSession::apply_item_macro_call` in
`src/compiler2/source_publish.rs` hands the quoted call to
`QuotedExpansionCtx::expand_ast_call(...)`, reads the returned root as a source
fragment, reserves any new local definitions, and applies them in source order.

**Ordinary function-body macros expand only when the function is demanded.**
`ScopeCode` publishes raw `FunctionSource(function)` facts without walking
inside the body. `DefineFunction(function)` waits on
`ExpandedFunctionSource(function)`, and `Job::ExpandFunctionSource(function)` in
`src/compiler2/jobs/source.rs` uses the same `QuotedExpansionCtx` walker for
body-local expansion.

That split is the main policy choice:

```text
item macro           changes surrounding scope     => eager
body-local macro     changes only one function     => lazy
```

## What Source Publication Owns

`publish_scope(...)` in `src/compiler2/source_publish.rs` owns source-order
module scoping.

It does four macro-relevant jobs:

1. Reserve local names first.
   Functions become `NamespaceSymbol::Function` or `NamespaceSymbol::Macro`
   before ordered application starts, so forward references inside the same
   scope can resolve.

2. Process `require`.
   `ScopeSession::apply_require` waits for the provider module's
   `ModuleDefined(module)` fact, selects the requested macro exports, waits for
   their `MacroExecutable(function)` facts, and records those exact
   `FunctionId`s in `required_remote_macros`.

3. Publish raw function source.
   `define_source_function(...)` writes `FunctionSource { source,
   required_remote_macros, ... }` without expanding ordinary bodies first.

4. Expand item macros.
   `apply_item_macro_call(...)` expands the call through the same macro runtime
   used elsewhere, but treats the result as a source fragment instead of a body
   expression.

The important invariant is that source publication owns scope shape, not
function internals.

## What Staged Function Expansion Owns

`Job::ExpandFunctionSource(function)` in `src/compiler2/jobs/source.rs` owns
everything inside an ordinary function body that has to settle before
`DefineFunction`.

`FunctionSourceExpander` starts from raw `FunctionSource(function)` and uses the
shared `QuotedExpansionCtx` engine while keeping the grouped function root
intact:

- attached attributes stay attached
- clause heads stay intact
- only each `do:` body is recursively expanded

The shared recursive walk does three things:

1. Rewrite source sugar first.
   `rewrite_source_sugar(...)` runs before macro-call handling, so source-only
   sugars such as `|>`, capture shorthand, multi-clause lambda sugar, and
   operator sugar collapse into ordinary quoted forms before function decoding.

2. Detect macro calls.
   `expand_ast_call(...)` treats `quote` as inert quoted data, resolves local
   macro names through `lookup_callable_namespace`, and resolves remote macro
   calls through module exports.

3. Run the macro and recurse on its result.
   `expand_macro_invocation(...)` waits on `MacroExecutable(function)`, projects
   `__CALLER__` from the current `ScopeSnapshot`, runs the macro, emits
   telemetry, and then immediately re-enters expansion on the returned root.

Expansion stops only when the returned tree contains no more source sugar and
no more eligible macro calls.

## How Remote Macros Stay Honest

Remote macros are not available just because a module exports them.

`require Helpers` does two separate things:

- it proves the provider module surface exists
- it proves the selected exported macros are executable

Only after that does the current scope record those `FunctionId`s in
`required_remote_macros`.

Later, when expansion sees `Helpers.twice(...)`, it:

1. resolves `Helpers` to a `ModuleId`
2. waits for `ModuleDefined(Helpers)` if needed
3. resolves `twice/1` against that module's exports
4. rejects the call with `macro/not-required` if the selected `FunctionId`
   is not in `required_remote_macros`

That is why an unrequired remote macro fails during source expansion instead of
silently reaching body lowering.

## What A Macro Executable Is

`Job::BuildMacroExecutable(function)` in `src/compiler2/jobs/macro_runtime.rs`
turns a defined macro function into an interpreter-ready backend artifact.

It does not invent a second macro-only lowering path.

The job:

1. waits for `FunctionDefined(function)`
2. checks that the function surface is actually `is_macro`
3. asks `World::macro_root(function)` for the hidden compile-time root
4. waits on `BackendProgram(root)` with follow-up
   `SeedRoot(root), LowerBackendProgram(root)`
5. publishes `MacroExecutable(function)`

`World::macro_root(function)` builds a `RootEntry` with:

- `kind: RootKind::Macro`
- one `Any` slot for `__CALLER__`
- one `Any` slot per captured variable
- one `Any` slot per user-visible macro argument

So macros share ordinary function definition, ordinary body lowering, and the
ordinary backend artifact ladder. The special part is the hidden compile-time
root and its ABI shape.

## How Macro Bodies Are Lowered

Macro bodies decode through the same quoted-function reader as ordinary
functions. `quoted_function.rs` turns quoted `quote` into `Expr::Quote(...)`
and quoted `unquote` into `Expr::Unquote(...)`.

`jobs/body.rs` then lowers macro bodies with one macro-specific rule:

- if `surface.is_macro`, `lower_clause(...)` prepends a `__CALLER__` parameter
  before captures and user parameters

The body lowerer now keeps quote-specific work behind the dedicated
`QuoteLowerer` helper in `jobs/body.rs`, so the ordinary body lowerer only
hands off `Expr::Quote(...)` instead of owning the quoted-AST construction
logic inline.

That quote seam treats quote/unquote specially:

- `Expr::Quote(inner)` lowers through `lower_quote_expr(...)`
- `Expr::Unquote(inner)` is legal only inside `quote`
- inside quote lowering, `unquote(...)` evaluates the inner expression and
  splices its runtime value into the quoted tree being constructed

The result is a backend program that builds Fz-shaped AST values on the process
heap. The backend interpreter then runs that program like any other backend
entry.

Two important guardrails fall out of this:

- `resolve_direct_callee(...)` rejects any macro call that survives into body
  lowering; if a macro call reaches lowering, source expansion failed
- `seed_root(...)` rejects runtime roots targeting macro functions; macros are
  compile-time entries only

## How The Macro Actually Runs

`World::run_macro_on_source(...)` is the final handoff.

It:

1. fetches the cached `MacroExecutable`
2. builds the runtime argument vector as
   `[__CALLER__, arg1, arg2, ...]`
3. borrows the quoted source heap's process with `source.lend_process(...)`
4. runs `ir_interp::run_backend_entry_on_process(...)`
5. requires the return to be `RuntimeValue::Ref(root)`
6. wraps that root back into `QuotedSourceRoot` with `source.subroot(root)`

The returned root is therefore still rooted in the same quoted-source heap as
the input carrier root.

That same-heap transport is the central data contract:

```text
macro input   = {heap, root} plus __CALLER__ and quoted args on that heap
macro output  = new root on the same heap
```

Compiler2 never stringifies the AST and never converts through an old parser AST
to run the macro.

## Tiny Walkthroughs

**Item macro**

```text
defmacro make_answer() do
  {:fn, %{}, [{:answer, %{}, []}, [{:do, 42}]]}
end

make_answer()
fn main(), do: answer()
```

`ScopeCode`:

1. reserves `make_answer/0`
2. publishes its raw `FunctionSource`
3. hits `make_answer()`
4. waits for `MacroExecutable(make_answer)` if needed
5. runs the macro and gets quoted `fn answer(), do: 42`
6. applies that fragment as source
7. publishes `answer/0`, then `main/0`

The macro changes what exists in the module, so it runs eagerly.

**Body-local macro**

```text
defmacro inc(x), do: quote do: unquote(x) + 1
fn main(), do: inc(41)
```

`ScopeCode` publishes raw `FunctionSource(main)` that still contains `inc(41)`.

Later, `DefineFunction(main)` triggers `ExpandFunctionSource(main)`:

1. find `inc(41)` in the `do:` body
2. wait for `MacroExecutable(inc)` if needed
3. run the macro with `__CALLER__` and quoted arg `41`
4. get quoted `41 + 1`
5. recurse on the result until stable
6. publish `ExpandedFunctionSource(main)`
7. decode and define `main`

The macro changes only `main`'s internals, so it waits behind demand.

## Telemetry And Proof

These events are the main observability surface:

- `[fz, compiler2, compiler_service, define]`
  raw function-source publication
- `[fz, compiler2, macro_executable, defined]`
  macro backend readiness
- `[fz, compiler2, macro, expanded]`
  one macro invocation over quoted source
- `[fz, compiler2, function, source, expanded]`
  staged body expansion for a demanded function

Good proof gates:

```text
cargo test --lib compiler2::drive_test::compiler2_macro_executable_runs_quote_unquote_on_the_source_heap
cargo test --lib compiler2::drive_test::compiler2_require_remote_macro_waits_executable_and_expands
cargo test --lib compiler2::source_publish_test::source_publication_expands_item_macros_as_scope_fragments
cargo test --lib compiler2::source_publish_test::source_publication_defers_local_macro_expansion_until_function_demand
```

Those four tests cover the four important contracts:

- macros lower to backend interpreter-ready form
- `require` gates remote macros
- item macros are eager source fragments
- ordinary function-body macros are lazy behind demand
