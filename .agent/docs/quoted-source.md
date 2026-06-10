# Quoted Source

`src/compiler2/source.rs` is the compiler2-owned quoted-source substrate for
the `fz-rh2.11.7.*` arc.

## What It Owns

- One source graph lives on one Fz `Process` heap, carried as runtime-shaped
  values only: atoms, lists, tuple structs, maps, and bitstrings.
- A source root is an `AnyValueRef` into that heap.
- The durable source key is `{heap, root}`:
  `QuotedSourceKey { heap_id, root }`.
- Structural comparison is separate:
  `QuotedSourceRoot::semantically_eq(&other, Horizon)` — a two-sided lockstep
  walk over both graphs that fast-fails at the first difference. No canonical
  rendering or digest is ever materialized.

## Why The Split Matters

- `{heap, root}` answers "which quoted source root is this?"
- `semantically_eq` answers "do these roots contain the same source shape?"
- A rebuilt equivalent graph on a different heap gets a different key but
  compares semantically equal — atoms compare by rendered name, not id, so the
  walk is cross-heap stable.
- `Horizon` selects how deep the comparison descends:
  `Horizon::Full` compares to the leaves (function identity — the body is part
  of the definition), `Horizon::Surface` skips each `do:` body (module/code
  identity — bodies belong to their own per-function facts, so a body-only
  edit leaves the surface unchanged).
- Compiler2 uses that split deliberately:
  code/module source revisions compare at `Horizon::Surface`,
  function-definition revisions compare at `Horizon::Full`. Transport identity
  (a fresh heap from a re-parse) never bumps a revision by itself.

## Source Shape

- AST nodes are Elixir-shaped 3-tuples:
  `{head, meta_map, tail}`.
- Most calls use an atom head and `tail = [arg, ...]`.
- Remote calls and closure calls are allowed to carry a quoted callee AST in
  `head`, not just an atom.
- Variables use `tail = lexical_context_map`.
- Module aliases use `{:__aliases__, meta, [:Foo, :Bar]}`.
- Keyword items are ordinary 2-tuples inside lists.
- FZ `extern` items are quoted as `{:extern, meta, [abi_binary, options_map]}`.
  `options_map` carries the symbol `name`, `variadic`, and token payloads for
  `params`, `return`, and optional `when` constraints.
- `@spec`, `@type`, and extern type-position surfaces carry compiler2 token
  payloads produced by the frontdoor while it is already walking the source
  token stream. A token payload is Fz-shaped quoted data, not a source string:
  a list of encoded lexer tokens with kind, payload, span bounds, and
  `space_before`. Quoted readers decode those payloads directly; they never
  re-enter `Lexer` for type fragments.
- Postfix bracket access quotes through an Elixir-shaped `Access.get` remote
  callee form.
- `cond do` quotes through ordinary `{:cond, meta, [[do: [{:->, ...}, ...]]]}`.
  structure.
- Capture refs cover local names, remote names, and bare/operator refs such as
  `&Kernel.+/2` and `&+/2`.
- Source-only sugars may appear in raw quoted source, but not in published
  function source. `src/compiler2/source_sugar.rs` rewrites them during source
  publication, on the same quoted heap, before `FunctionSource` is saved.
- Source-sugar rewrites emit ordinary quoted forms: `|>` becomes a normal call
  or a subject-bearing `case`, capture placeholders become direct lambdas,
  multi/guarded lambdas become one lambda whose body is a `case`, and operators
  become ordinary helper calls such as `List.concat`, `Enum.member?`,
  `Kernel.fz_binary_concat`, and `Range.new`.
- Remote helper calls are emitted in canonical quoted remote-call shape with
  `{:., meta, [{:__aliases__, meta, [...]}, :fun]}` heads. Dotted atom names are
  not a compiler2 source interchange format.
- Extern-symbol folding for adjacent `ident::ident` names is only valid in
  ordinary expression/capture position. Bitstring segment parsing suppresses
  that folding so forms like `payload::binary-size(len)` stay quoted as
  segment/type AST, not as fake extern-symbol variables.

## Surface Grouping

- Raw quoted source still preserves one top-level form per source clause.
- Compiler2 function surfaces are then composed back into first-class grouped
  quoted roots on that same heap:
  a logical function surface is a quoted list carrying attached `@doc` /
  `@spec` items plus every grouped `fn` / `fnp` / `defmacro` clause, or a
  single `extern` item surface.
- Grouping is by `{name, arity}` and flushes at the same non-function
  boundaries the legacy item surface exposes.
- Grouped roots are interned per quoted-source heap. Re-reading the same body
  must yield the same `{heap, root}` for the same logical function surface.
- Protocol-impl callback bodies use that same grouped-root substrate; they are
  not a second special-case function source format.
- `FactKey::FunctionSource(FunctionId)` is the lazy authoritative function
  source fact. Source production saves it through the `Fz.Compiler.define`
  compiler-service boundary; `FunctionDefined` is derived on demand from that
  fact.
- `FunctionDefined` now carries a compiler2-owned `FunctionSurface` decoded
  from grouped quoted source. Source-defined functions and generated lambdas
  both use that same callable-surface model.
- `DefineFunction` runs compiler2-owned source diagnostics over that expanded
  `FunctionSurface`. Partial `case` and `with else` surfaces emit
  `type/no-matching-clause` warnings through the normal diagnostic telemetry bus
  without reopening the old frontend pattern-check pass.
- The noted function-source fact must carry enough callable surface to keep
  pre-definition name resolution honest. Today that explicitly includes the
  variadic bit, because lowering may need callable matching before
  `FunctionDefined` exists.

## Bootstrap Coverage

- `src/compiler2/frontdoor.rs` now quotes the compiler-owned bootstrap/runtime
  surface directly, including:
  `extern`,
  runtime-prelude operator import filters such as `only: [+: 2]`,
  `if`,
  `with`,
  `receive ... after`,
  and anonymous `fn ... end`.
- Runtime library sources are expected to reach quoted roots without an old-AST
  fallback path.
- Compiler2 source ingestion lexes each submitted source once. Type fragments,
  attributes, and extern signatures are transported as quoted token payloads
  from that pass, so there is no fragment re-lexing under synthetic source
  names such as `<quoted-type-alias>`.

## Private Metadata Keys

- `__fz_lexical__`: stable lexical context; semantic content, compared by
  `semantically_eq`.
- `__fz_span__`: diagnostic-only span payload; not semantic content, skipped
  by `semantically_eq`.
- `__fz_namespace_id__`: transport-only namespace handle; not semantic
  content, skipped by `semantically_eq`.

## Scope Authority

- Compiler2 does not maintain a second mutable compile-env store for quoted
  source.
- `ScopeSnapshot` is the one scope projection carrier:
  `{module_id, namespace_head, function_id?}`.
- `World::scope_lexical_context` derives quoted lexical metadata from that
  snapshot.
- `World::project_module_value` and `World::project_env_value` project
  `__MODULE__` / `__ENV__` as Fz-shaped values from the same snapshot.
- The namespace id carried in quoted metadata is transport only; it helps jobs
  and tests line contexts back up with the live namespace chain, but it is not
  semantic identity.

## Publication Authority

- `src/compiler2/source_publish.rs` is the compiler-owned publication boundary
  for quoted source forms.
- `ScopeSession` is the mutable in-progress scope state for one scope walk:
  it carries the current module, namespace head, local protocol names, pending
  type declarations, reads, outputs, exports, and the revision floor a module
  definition must absorb.
- `jobs/source.rs` schedules jobs and publishes final job facts, but does not
  own source-form rules. It parses/reads quoted source, delegates discovery to
  `source_publish::discover_modules`, delegates scope/module publication to
  `publish_scope` / `publish_protocol_surface`, and derives
  `FunctionDefined` from the lazy `FunctionSource` fact.
- `Fz.Compiler.define(source_root, __ENV__)` is the compiler-service entry into
  this boundary. The first argument is an Fz `AnyValueRef` source root on the
  active quoted source heap; the second argument is the caller environment root
  that records the source-session authority. The service reads the source root
  as a scope form and applies it in source order through the live
  `ScopeSession`.
- Literal function forms, protocol-impl callbacks, and synthesized `__info__/1`
  functions are applied as `Fz.Compiler.define` publications with a projected
  `__ENV__`. There is no second raw function-body save path during module
  indexing.
- Source publication notes `@type` declarations, records function/type
  reference wait sets, binds aliases/imports/requires, saves expanded grouped
  function roots as `FunctionSource` through `Fz.Compiler.define`, scopes child
  modules, notes protocol-domain type declarations, publishes protocol
  callback/dispatch facts, and records protocol impl callback sources.
- Function source expansion is body-only. Function heads define identity; they
  are not expression positions and are never macro-expanded. Each grouped
  function source keeps attached attributes and clause heads intact while
  recursively expanding only each `do:` body before publication.
- Body expansion also normalizes source-only sugar recursively. Macro-returned
  AST re-enters the same expansion loop on the same quoted heap, so downstream
  function decoding and lowering never need separate support for pipe,
  placeholder captures, guarded anonymous-function sugar, or source operator
  sugar.
- `%Module{...}` source must decode as a struct literal before `%/2` is
  considered as an operator. That ordering keeps runtime structs such as
  `%Range{}` on the struct path after `Range.new` has been introduced by source
  sugar rewriting.
- Exact `import Mod, only: [...]` may reserve placeholder function bindings
  before `Mod` is defined, but a body that calls such a binding waits for the
  provider `ModuleDefined` fact before the body can be saved. Once the provider
  surface is known, import binds the real exported symbol kind. Imported macros
  additionally wait for `MacroExecutable(function)`.
- `require Mod` waits for the provider surface, selects the requested macro
  exports (`only:` or all macros minus `except:`), and waits for those exact
  `MacroExecutable` facts. It records exactly those macro function ids as
  required in the source session. It does not import bare names; only required
  remote macro calls such as `Mod.m(...)` are available to source expansion.
- Source-order item macro calls expand through the same
  `MacroExecutable(function)` fact as expression macros. The returned root is
  read as a source fragment, local definitions are reserved, and the fragment is
  applied immediately in source order.
- Remote calls to user modules may wait for the provider `ModuleDefined` fact
  during body expansion so source production can distinguish ordinary functions
  from macros before saving `FunctionSource`. If the provider exports a macro
  and the current scope did not `require` it, source publication emits
  `macro/not-required` instead of letting a macro call leak into body lowering.
  Current-module remote calls use the live source-session callable map instead
  of waiting for the module fact the active job is producing. Runtime helper
  modules introduced by source-sugar rewrites are not eagerly submitted just to
  prove they are not macros.
- Module publication synthesizes a normal `__info__/1` function for non-global
  modules that do not define one. The body is ordinary quoted source
  (`case kind do ... end`) derived from the module exports, so reflection uses
  the same `FunctionSource`/export path as user functions.

## Macro Runtime

- `FactKey::MacroExecutable(FunctionId)` is the readiness fact for a compiled
  macro function. `Job::BuildMacroExecutable(function)` waits for
  `FunctionDefined(function)`, creates one hidden macro root, waits for the
  ordinary `BackendProgram(root)`, then publishes the executable fact.
- A macro root is `RootKind::Macro`. Its input vector is explicit:
  `__CALLER__` followed by capture inputs and user-visible macro arguments, all
  typed as `Any`. That input vector is part of the activation key and the
  published `Activation` fact value.
- A runtime root is `RootKind::Runtime`. Runtime roots reject macro entry
  functions during `SeedRoot`, and `LowerBackendProgram` only schedules
  `LowerNativeProgram` for runtime roots. Compile-time macro roots stop at the
  backend interpreter-ready rung.
- `LowerFunction` and `PlanEntryDispatch` are shared by runtime functions and
  macros. The difference is the hidden compile-time ABI slot, not a second
  macro-only body or dispatch implementation.
- `quote` / `unquote` lower to normal compiler2 body steps that construct Fz
  values (`Const`, `Tuple`, `List`, `Map`) on the active process heap.
  `unquote` is the only part of a quote that is evaluated while building the
  quoted source value.
- Quoted callable heads are canonicalized against the macro definition
  namespace while lowering `quote`. A quoted `double(...)` inside
  `Helpers.twice/1` becomes `Helpers.double(...)` before the macro returns, so
  expanded source carries the definition-context callable identity downstream
  without a second scoped-expression representation.
- Macro execution lends the owning `QuotedSourceHeap` process to the backend
  interpreter and restores it after the run. Macro arguments and returns are
  `AnyValueRef` roots in that same heap; the returned root becomes another
  `QuotedSourceRoot` over the same owner. There is no AST codec, copied scratch
  heap, or old `CompileTimeEvaluator` on this path.
- `Fz.Compiler` host services are not part of macro executable readiness.
  Source production owns their authority: expanded forms call compiler services
  in source order, and those services publish through the active `ScopeSession`
  instead of mutating `World` from inside interpreter execution.

## Discovery Authority

- `QuotedCodeSource` now carries two compiler2-owned views of one source
  submission:
  the authoritative quoted root and a derived `ScopeSurface` read model.
- `ScopeSurface` is intentionally narrow:
  top-level attrs plus decoded scope forms for `alias`, `import`, `require`,
  compiler services, functions, modules, protocols, protocol impls, structs,
  and macro-call
  surface forms.
- Code/module/protocol discovery facts read those decoded forms directly from
  quoted roots; they no longer store or zip against old parser `Rc<Item>`
  payloads.
- Module bodies and protocol bodies use the same `ScopeSurface` shape as
  top-level code, so nested discovery and protocol-impl callback discovery stay
  in one quoted-source world.
- Function bodies, contracts, and dispatch planning now read compiler2-owned
  `FunctionSurface` data directly rather than old parser function records.

## Rooting Contract

- `QuotedSourceRoot` retains the owning `QuotedSourceHeap` by `Rc`, so the
  heap outlives the `AnyValueRef`.
- The raw `AnyValueRef` is never treated as durable without its heap owner.
- Runtime bitstring/procbin readers operate on heap-object words
  (`AnyValueRef::heap_object_word()`), not `AnyValueRef::raw_word()`.
- Quoted graphs are built bottom-up on an immutable heap, so they are acyclic
  by construction. The semantic walk treats unsupported runtime-only value
  kinds as a structural error, which `semantically_eq` reports conservatively
  as "not equal" (forcing a revision bump rather than risking a missed change).
