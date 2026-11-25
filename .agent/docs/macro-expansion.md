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
The fragment's items are the expansion's own shape, read by
`item_macro_fragment_root` in `src/compiler2/quoted_expander.rs`: a list is its
elements, a `__block__` is its statements, a block inside either is its
statements in turn, and anything else is the one item. So a macro defines
several functions with one `quote do ... end` holding several `def`s.
A module body cannot invoke a macro the same module defines. The module is
still being defined when its body runs, so its own macros do not exist to call
yet, and `item_macro_invocation` refuses the call with
`macro/own-module-item-call` at the call's span. Elixir draws the same line and
reports the call as an undefined function. The macro belongs in another module
the body imports; a function body of the defining module may call it, because
by then the module is compiled.

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

Lambda identity comes from a typed source occurrence assigned once during final
function decoding, not a lowered value or quoted metadata. Two macro expansions
with identical spans (including missing metadata) therefore define distinct
lambdas. Generated functions retain their
typed owner chain; `__ENV__.function` and quoted lexical context reflect the
enclosing named source function, never an internal generated display name.
A generated function's `FunctionSource.body` is `FunctionBody::Generated { owner }`:
it holds no source text, its owner's `LowerFunction` publishes its
`FunctionDefined`, and its source is never expanded. When a revision makes the
owner stop minting a lambda, the lambda is orphaned (`World::is_orphaned`): each
job on it is retired: it concludes empty, reports `fz.compiler2.job.retired`
with reason `orphaned_lambda`, and reads
the owner's `LoweredBody` so it wakes if the owner mints the lambda again. A
retired `AnalyzeActivation` also clears its activation slot, and a concluded
read of a retired job's product does not hold its reader back.
The existing recursive decoder assigns occurrences across the grouped function's
clauses; unchanged decoding retries reproduce them. AST cloning preserves them,
so duplicating a `with`-else branch in lowering cannot split one denotation.

There is one important sub-case inside the eager bucket — and one origin
exception:

- `runtime.fz` defines the compiler-owned definition macros `def`, `defp`,
  `defmacro`, `defmacrop`, `defmodule`, `defprotocol`, and `defimpl`.
- `def`, `defp` and `defmacrop` are ordinary identifier calls at the lexer and
  front door; none has a token kind or a definition-specific item parser. Their
  runtime macros forward the untouched grouped clause root and `__CALLER__` to
  `Fz.Compiler.define`.
- In ordinary (user) source there is exactly one read: a def-head parses to a
  `MacroCall` (`build_form` in `quoted_surface.rs`), and its structure emerges
  from the expand -> `Fz.Compiler.define` -> define pipeline, never from a
  second mode-gated source parse.
- The bootstrap is the lone exception. `is_bootstrap(owner)` source — the prelude
  and the runtime library modules — is read canonically: the same one reader,
  then `canonicalize_definitions` turns each def-head `MacroCall` into its typed
  form via `build_definition_form`, because the macros that implement def-heads
  are defined *in* the bootstrap and so cannot be bounced through. Post-expansion
  content (a `Fz.Compiler.define` payload, item-macro output, protocol/impl
  bodies) is canonical the same way.
- `DefinitionForm` (`src/ast`) is the one reading of a definition keyword,
  and `TryForm::Definition` carries it for a definition read as an implicit
  `try`: `defmacro` and `defmacrop` define macros, `defp` and
  `defmacrop` define functions private to their module. A private macro
  expands wherever its own module calls it and is left out of the module's
  exported interface, so a call from another module is refused as a call to a
  `defp` is (`01783`, `01784`).

## What Source Publication Owns

`publish_scope(...)` in `src/compiler2/source_publish.rs` owns source-order
module scoping.

It does four macro-relevant jobs:

1. Reserve local names first.
   Functions become `NamespaceSymbol::Function` or `NamespaceSymbol::Macro`
   before ordered application starts, so forward references inside the same
   scope can resolve.

2. Process `require`.
   `ScopeSession::apply_require` selects macro exports from the provider's
   `ModuleInterface`, or reserves exact macro identities from `only:` while
   that interface is pending. It binds each one into the namespace as a
   required-macro entry (`NamespaceStore::bind_required_macro`). An invocation
   demands the macro's backend content.

3. Publish raw function source.
   `define_source_function(...)` writes `FunctionSource { owner, source,
   namespace, ... }` without expanding ordinary bodies first. The
   lexical publisher remains an owner while every returned node carries its own
   immutable version; see
   [`quoted-source`](quoted-source.md#source-identity-and-provenance).

4. Expand item macros.
   `apply_item_macro_call(...)` expands the call through the same macro runtime
   used elsewhere, but treats the result as a source fragment instead of a body
   expression.

For compiler-owned definition macros, the returned fragment is expected to cross
back into the compiler through `Fz.Compiler.define(source, __CALLER__)`. That
callback is the single source-publication authority for top-level definitions.
At quoted-surface extraction, `defp` becomes `FunctionForm { is_private: true,
.. }`; downstream publication consumes that flag and never branches on the
source spelling.

For module/protocol/impl fragments, nested indexing advances through the
same callback path:

- `ScopeCode` indexes the outer fragment when its definition macro expands
- `DefineModule(parent)` expands nested scope-definition macros inside the
  parent body and indexes child modules from those compiler-defined fragments
- direct demands on a placeholder nested module wait on the dotted parent
  module definition instead of on a raw-source pre-index pass

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
   sugars such as `|>`, capture shorthand, multi-clause lambda sugar, `for`
   comprehensions, and operator sugar collapse into ordinary quoted forms
   before function decoding.
   Each successful rewrite is memoized in its owning `QuotedSourceHeap` by the
   original node identity. Retries therefore revisit the same rewritten root
   and every synthesized descendant macro keeps one invocation identity (a
   capture can synthesize several). The memo dies with the source heap; it is a
   deterministic representation cache, not another source or product authority.

2. Detect macro calls.
   `expand_ast_call(...)` treats `quote` as inert quoted data, resolves local
   macro names through `lookup_callable_namespace`, and resolves remote macro
   calls through module exports.

3. Run the macro and recurse on its result.
   `expand_macro_invocation(...)` reads `FunctionDefined(function)` and the
   hidden root's retained `RootBackendProduct(root)`, projects
   `__CALLER__` from the source-visible caller scope, runs the macro, emits
   telemetry, memoizes that immediate output by invocation identity, caller
   scope, and retained backend-product identity, and then
   immediately re-enters expansion on the returned root. A downstream wait can
   therefore retry recursive expansion without replaying the macro. The cache
   owns the quoted invocation/output roots but only a `Weak<BackendProgram>`;
   retiring a macro product releases it and makes the next lookup miss.

Expansion stops only when the returned tree contains no more source sugar and
no more eligible macro calls.

## `__ENV__` And `__CALLER__`

Both are compile-time environment reflections, but they enter expansion
differently because one is constant and one varies per call.

`__ENV__` is the definition env — constant for a given definition. Just before a
body is expanded, `FunctionSourceExpander::expand` projects it from the
definition's own scope (`project_env_value(def_scope, Definition)`, so
`__ENV__.function` is the definition itself, by construction) and binds it into
the namespace as `NamespaceSymbol::Splice`. The expander resolves a reserved
`__`-prefixed variable against the namespace and splices a `Splice` binding in
place — generically: it knows about splice bindings, not about `__ENV__`. The
binding is transient; it is never recorded on the function. The env is a `%Macro.Env{}`
(below). (`decode_expr` decodes a raw map value as a map literal, alongside
lists and tuples, so the spliced env map decodes as source.)

A module attribute is a splice too, bound as `"@name"` when the module sets it
(modules.md, "A module attribute"). The read `@name` is not a `__` variable,
so the expander recognizes its `{:@, _, [{name, _, nil}]}` shape and splices
the binding in force, or warns and reads `nil` when there is none.

`__MODULE__` is bound beside `__ENV__` as a second splice: the atom the
definition's module is in value position (`World::module_atom_value`), and nil
in a definition outside any module. Code a macro quotes is expanded in the
function it lands in, so a quoted `__MODULE__` names the module that called the
macro. The atom stands wherever a module can:

- as a value, it is the atom;
- as the receiver of a call, it is a call on a module atom;
- as the name of `%__MODULE__{}`, in a literal or a pattern. The front door
  reads `%__MODULE__{...}` with the variable in the name position, and
  `decode_module_target` reads a module atom there as that exact module.

A clause head's parameters are patterns and expand as the patterns of a `case`
clause do (`FunctionSourceExpander::expand_signature`), so a splice in a head
pattern is resolved. The signature itself is the definition's name and is not
expanded as a call.

### The `%Macro.Env{}` struct

`__ENV__` and `__CALLER__` are `%Macro.Env{}` structs, projected by
`World::project_env_value` (`src/compiler2/env_projection.rs`) with Elixir's
field order. The `Macro.Env` module (`lib/macro_env.fz`) holds the
`defstruct` and `in_match?/1` and `in_guard?/1`. Where each field comes from:

| field | value |
| --- | --- |
| `module`, `function` | the scope's module (its atom, as `__MODULE__`; `nil` outside a module) and function (`{name, arity}` or `nil`) |
| `context` | the expansion context: `nil`, `:match` or `:guard` |
| `file`, `line` | where the macro call is written (`__CALLER__`) or the definition is (`__ENV__`); `"nofile"` and `0` with no source position (`CallSite::locate`) |
| `aliases` | `[{Short, Full}]` for each module the namespace binds under a name that is not its own, in the order written |
| `functions`, `macros` | `[{Module, [{name, arity}]}]` for each callable the namespace binds that another module owns, modules and pairs sorted |
| `requires` | the modules the namespace `require`s, macros or not, plus those it imports from, sorted |
| `context_modules` | `[Module]` inside a module, `[]` outside |
| `lexical_tracker`, `macro_aliases`, `tracers`, `versioned_vars` | `nil`, `[]`, `[]`, `%{}`: fz has no tracker, tracers or variable tracking in the expander |

The macro-expansion memo key holds the call site (`file` and `line`) and the
expansion context beside the macro, the call and the scope, since the env a
macro reads differs by each.

### Expansion context

`ExpansionContext` (`Expression`, `Match`, `Guard`) in `quoted_expander.rs` is
the one state the expander keeps about where a call stands. A position that
binds a pattern expands it in `Match`: function-head parameters, the left of
`=` and `<-`, and the left of `->` in `case`, `fn`, `receive`, `try`'s
`rescue`, `catch` and `else`, `with`'s `else`, and `for ... reduce:` clauses.
A `when` guard expands in `Guard`. The `->` clauses of `cond` and of
`receive`'s `after` hold tests, so their left sides stay `Expression`, as in
Elixir. `Macro.Env.in_match?/1` and `in_guard?/1` read it, so one macro can
build a value in an expression and match any value in a pattern.

`__CALLER__` varies per invocation and cannot be a compile-time splice: a macro
is compiled once and executed many times, and the caller is unknown when the
macro body is expanded. So it stays a runtime parameter — `lower_clause`
prepends it, and `expand_macro_invocation` projects it from the call-site scope
(`project_env_value(scope, context, call_site)`) and passes it as the macro's first
argument. Function-body expansion strips its transient `__ENV__` splice from
that source-visible scope, so retries cannot invent a new macro-cache identity. The def-head macros capture `__CALLER__` as
`Fz.Compiler.define(source, __CALLER__)`, the Elixir-aligned def-site env seam.

## How Remote Macros Stay Honest

Remote macros are not available just because a module exports them.

A remote macro may be called by its qualified name when the call's namespace
either holds a required-macro entry for it or holds any binding from its module
(`World::macro_callable_remotely`). Both live in the lexical namespace, so a
`require` or `import` covers its own scope and no sibling.

- `require Helpers` binds a required-macro entry per selected exported macro. An
  exact `only:` list can reserve those identities before the provider interface
  is ready; `except:` removes the denied ones. A required-macro entry binds no
  name: name lookups never meet it.
- `import Helpers` in any shape (`only:`, `except:`, neither) binds callables of
  `Helpers`, and any such binding makes every macro of `Helpers` callable by
  its qualified name, as in Elixir where importing a module requires it. The
  prelude's `import Kernel, only: [...]` therefore makes `Kernel.apply/3`,
  `Kernel.&&/2` and the rest of Kernel's macros callable in every source.

Macro code is demanded when invoked.

Later, when expansion sees `Helpers.twice(...)`, it:

1. resolves `Helpers` to a `ModuleId`
2. asks the call's namespace what `twice/1` is bound to
   (`QuotedExpansionCtx::imported_symbol_of`). When an import bound that
   name and arity to a callable of `Helpers`, the call follows the route an
   unqualified `twice(...)` takes: a `Macro` binding expands, and a `Callable`
   placeholder waits on `ModuleInterface(Helpers)` first. The module's
   definition is not consulted, so the answer does not depend on whether
   `Helpers` is defined yet.
3. otherwise waits for `ModuleDefined(Helpers)` if needed; a runtime module
   whose definition is not yet published is not waited for, and the call is
   left to function resolution (an ordinary `Enum.count(...)` call needs no
   definition to proceed)
4. resolves `twice/1` against that module's exports
5. rejects the call with `macro/not-required` if neither a required-macro entry
   for the selected `FunctionId` nor a binding from `Helpers` is in the
   call's namespace

That is why an unrequired remote macro fails during source expansion instead of
silently reaching body lowering.

## What Owns Macro Code

`World::macro_root(function)` names a hidden compile-time root.
`Compiler2` retains its `PullSession` in `ProductSessions`; the session's
`ProductMemo` owns `RootBackendProduct(root)` and its shared backend program.
The macro caller uses that same backend allocation.

Source jobs record exact product reads and waits through `DependencyKey`.
The scheduler reads product readiness and generations from the retained memo,
and a named wait drives the ordinary product loop. Equal backend reproduction
preserves its allocation and generation. An unchanged backend answer therefore
leaves source consumers quiet.

Macro execution consumes this interpreter-ready content directly. Native
lowering is requested only by native front doors.

`World::macro_root(function)` builds a `RootEntry` with:

- `kind: RootKind::Macro`
- one `Any` slot for `__CALLER__`
- one `Any` slot per captured variable
- one `Any` slot per user-visible macro argument

So macros share ordinary function definition, ordinary body lowering, and the
ordinary backend product path. The special part is the hidden compile-time root
and its ABI shape.

## How Macro Bodies Are Lowered

Macro bodies decode through the same quoted-function reader as ordinary
functions, with one exception: decoding stops at `quote`. `quoted_function.rs`
turns a quoted `quote do ... end` into `Expr::Quote(cursor, splices)`, holding
the quoted-source cursor for the body untouched, rather than a decoded `Expr`
tree, alongside every `unquote(e)` reachable inside that body, each already
decoded into an ordinary `Expr` in the same walk (`collect_quoted_splices`,
called from `decode_quote`) and in the same walk order lowering later
revisits. The body inside a quote otherwise stays quoted data until something
actually splices it in elsewhere; nothing about it but its `unquote` holes is
decoded, resolved, or rejected while the quote itself is only being defined.
Decoding an `unquote`'s content eagerly, alongside the quote, rather than
lazily at lowering time, matters for two reasons: free-name collection (for
lambda capture) can see into an `unquote` like any other expression instead of
treating the whole quote as opaque, and every lambda literal anywhere in the
enclosing function — whether inside an `unquote` or not — gets its occurrence
number from one shared `LambdaOccurrences` counter instead of two independent
ones. Quoted `unquote` outside a quote's body still decodes as an ordinary
`Expr::Unquote(...)`, since an `unquote` only makes sense already inside a
quote that is being lowered.

`jobs/body.rs` then lowers macro bodies with one macro-specific rule:

- if `surface.is_macro`, `lower_clause(...)` prepends a `__CALLER__` parameter
  before captures and user parameters

The body lowerer keeps quote-specific work behind the dedicated
`QuoteLowerer` helper in `jobs/body.rs`, so the ordinary body lowerer only
hands off the cursor and its splices in `Expr::Quote(cursor, splices)`
instead of owning the quoted-AST construction logic inline.

`QuoteLowerer::lower` walks that cursor directly, as one recursive case per
quoted-source shape rather than one case per language construct. Everything in
a quote but what it unquotes is known where the quote is read, so each case
answers either a constant (a `LiteralTerm`) or a step value. A list or tuple
whose items are all constants is itself a constant; a step is pushed only for a
node with an `unquote` beneath it, and the constants beside that `unquote` are
one `Const` step each. A quote with no `unquote` is a single `Const` step, and
a node's metadata is always part of a constant.

- a literal (int, float, atom, bitstring) lowers to the matching constant
- a list recurses over its items
- a two-element tuple recurses over its two items and lowers to a two-element
  tuple directly, matching Elixir's quoted representation; every other tuple
  arity is never a bare tuple at this layer — it already arrived as the
  three-item `{}` AST node, so it falls out of the next case instead. Keyword
  entries depend on this distinction, because each `[key: value]` element is a
  structural two-tuple rather than a tuple-literal AST node.
- a `{head, meta, args}` AST node either:
  - splices `unquote(e)` by taking the next already-decoded splice in walk
    order and lowering it with the same `lower_expr` any other expression
    goes through, exactly as if `e` had been written at that position
    directly
  - binds an atom-headed call to its callable through
    `resolve_quoted_callable`/`lower_call_node`, the same pair every other
    quoted call site uses
  - or, when the node's tail is not list-shaped, builds a bare variable
    reference

Because this walk dispatches on quoted-source shape rather than on which
language construct produced it, a `case`, an `fn`, a bitstring, a struct, or
any other construct made only of these four shapes lowers through it too —
there is no per-construct list to keep in sync.

The result is a backend program that builds Fz-shaped AST values on the process
heap. The backend interpreter then runs that program like any other backend
entry.

Two important guardrails fall out of this:

- `resolve_direct_callee(...)` rejects any macro call that survives into body
  lowering; if a macro call reaches lowering, source expansion failed
- `seed_root(...)` checks the root kind against the current function definition:
  runtime roots reject macros, and macro roots reject ordinary functions. A
  captured macro binding cannot execute an ordinary replacement using the macro ABI.

## Variable Hygiene

A variable's identity is Elixir's: its spelling, its context and its
counter, `Var { name, context: VarContext { context, counter } }`
(`src/ast/mod.rs`).

- The **context** is an atom: `nil` for a variable written by hand, the
  quoting module for one a `quote` wrote (`Elixir` outside any module), and
  the compiler pass for a name the compiler minted (`fz_source_sugar` for the
  capture, lambda and `for` sugar, `fz_guard_hoist` for a hoisted guard call),
  as Elixir mints `&1` in context `:elixir_fn`.
- The **counter** is `VarCounter::Module { module, n }`, the `n`-th expansion
  whose caller is `module`, or `VarCounter::Integer(n)`, from
  `Macro.unique_var/2` or a minted name.

`Expr::Var`, `Pattern::Var`, `Pattern::Pinned`, and a bitstring's `size(n)`
all carry a `Var`, and every map that resolves a variable by name (the
lowering environment, closure free/bound-name tracking, and dispatch_matrix's
pattern-binding tables) is keyed by `Var`, never by a bare string. Two
variables that differ in context or counter never share a binding.

A quoted variable is `{name, meta, context}`: the context atom in the slot a
call's argument list would otherwise occupy, and the counter as Elixir's
`counter:` meta entry, `{module, n}` or an integer.
`QuotedSourceBuilder::variable` is the one constructor for this shape; the
front door, quote lowering, and sugar all build a variable node through it,
and decode reads it back (`decode_var_context`, `quoted_function.rs`).

**Quote.** `Lowerer::lower_variable` (jobs/body.rs) writes the quoting
function's module atom as the context, so `quote(do: x)` in `Main` is
`{:x, [], Main}`.

**Expansion.** `stamp_expansion_counter` (quoted_expander.rs) is Elixir's
`linify_with_context_counter`. It runs over a macro's result right after the
macro runs and before the expansion is memoized. Every variable whose context
is the macro's module and that has no counter gets
`counter: {CallerModule, n}`. That covers a quote in a helper function of the
macro's module as much as one in the macro itself. A variable with another
context, one that already has a counter (a nested expansion's, or
`Macro.unique_var/2`'s), and `_` are left alone. A quote in another module
that the macro calls keeps its context with no counter, so its variables are
shared across expansions, as in Elixir.

`n` comes from the expander, once per macro invocation the job attempt visits,
whether or not the memoization cache already holds the answer, so a retry
reproduces the same numbers. The module-scope expander (`ScopeSession`,
source_publish.rs) counts up from 0 and a function body's expander
(`FunctionSourceExpander`, jobs/source.rs) counts down from -1. A function
body can hold variables stamped by both, and the two ranges never meet.

`var!(x)`, an ordinary macro in `lib/runtime.fz`, deletes a quoted variable's
counter and sets its context to `nil`, so it reads and binds exactly as if the
caller had written it by hand. `Macro.var/2` and `Macro.unique_var/2`
(`lib/macro.fz`) build variables as Elixir's do; `unique_var`'s counter comes
from `:erlang.unique_integer/0`, which draws from the counter `make_ref/0`
draws from.

An undefined variable whose context is not `nil` reports `lower/unbound`, and
the message names the context module.

## How The Macro Actually Runs

`ExecutionContext::run_macro_on_source(...)` is the final handoff.

It:

1. receives the retained backend handle from the recorded product read
2. builds the runtime argument vector as
   `[__CALLER__, arg1, arg2, ...]`
3. borrows the quoted source heap's process with `source.lend_process(...)`
4. runs `ir_interp::run_backend_entry_on_process(...)`
5. boxes the return onto that same process with `AnyValue::as_any_value_ref(...)` —
   a heap ref already has this form, and a bare literal (a number, an atom, a
   string, or a 2-tuple) gets one the same way a scalar argument does, so a
   macro body may end in `quote do: ...` or in a literal outright
6. wraps that boxed word back into `QuotedSourceRoot` with `source.subroot(root)`

The returned root is therefore still rooted in the same quoted-source heap as
the input carrier root.

A macro argument written `x.field` or `__ENV__.line` arrives as Elixir's call
node `{{:., meta, [x, :field]}, [no_parens: true | _], []}` (see
[quoted source](quoted-source.md)), so a macro matches it the way an Elixir
macro does.

A value the macro computes enters the returned code through `Macro.escape/1`
(`lib/macro.fz`), an ordinary lib function the macro body calls. It answers the
quoted code that rebuilds the value, in Elixir's shapes: a tuple that is not a
pair is `{:{}, [], elements}`, a map is `{:%{}, [], pairs}` in `Map.to_list`
order, and a bitstring that is not a binary is a `<<>>` of its leading
`rem(bit_size, 8)` bits and its binary rest. A function a module defines by
name is the capture that names it,
`{:&, [], [{:/, [], [{{:., [], [Mod, :fun]}, [no_parens: true], []}, arity]}]}`,
with `Mod` the module's atom. `escape/1` asks the runtime for the three parts
(`fz_function_name`, which reads the source denotation the `Node` keeps for
every closure) and the quoted reader takes that shape as a capture
(`decode_fn_ref_target` in `src/compiler2/quoted_function.rs`). A function
captured by its local name is the same value as one captured through its
module, so it escapes the same way. A PID, a reference or an anonymous
function, at any depth, raises `ArgumentError`: it names nothing in the
compiled program.

### A macro's result must be quoted syntax

Before anything is stamped, `first_invalid_quoted_expr`
(`src/compiler2/quoted_expander.rs`) checks the macro's result against
Elixir's grammar: atoms, numbers, binaries, lists, two-tuples and call nodes
`{head, meta, args}`. The first part that is not one (a map, a function, a
PID, a tuple of another size, a three-tuple whose metadata is not a list) is
refused as `macro/invalid-quoted-expr` at the call, with Elixir's text
`invalid quoted expression: <inspect>` and a note `expanding macro: M.f/N`.
Three compiler-embedded values are exempt: the environment argument of
`Fz.Compiler.define`, the details map of an `extern` form and lexer tokens
(`decode_token`). Elixir warns for a PID
instead of refusing; fz refuses it with the rest.

### Where expanded code is reported

A `quote` writes no span on the nodes it builds (`meta`,
`src/compiler2/jobs/body.rs`). When the macro returns, `stamp_span_fallback`
(`src/compiler2/quoted_expander.rs`) gives the span of the macro call to every
node of the result that has none, so a fault in quoted code is reported under
the call the program wrote. This is Elixir's rule for a quote without
`location: :keep`, which fz does not have.

An argument spliced in with `unquote` came from the caller's source and
already has a span, so it keeps it. When a macro's quote calls another macro,
the inner call node was itself given the outer call's span, so the inner
macro's result lands there too.

```elixir
defmacro bad(x), do: quote(do: String.nope(unquote(x)))

bad("x")               # reported under `bad("x")`
pass(String.nope(1))   # reported under `String.nope`, the argument
raise NotThere, "x"    # reported under the raise, not inside Kernel
```

A macro that raises while it runs fails the compile. The failure line is the
diagnostic's message, its code is `lower/unsupported`, and its span is the
macro call's (`run_macro_invocation`). `Kernel.apply/3` refuses a call it
cannot rewrite this way.

A macro run answers a `MacroExpansion` (`macro_warning.rs`): the expanded root
and the warnings its body emitted with `IO.warn`, in the order it emitted them.
`run_macro_on_source` hands the interpreter a `MacroRunOutput` sink. A print
still goes to stdout, and the interpreter's warning hook records each `IO.warn`
as a `MacroWarning` (message, and the file and line when the call named any).
`run_macro_invocation` reports each one through `emit_warning_once` as
`macro/warning`, so compilation continues, and the diagnostic reaches stderr
and the `[fz, diag, warning]` event like every other warning. The memoized
expansion stores its warnings beside its root, and a memo hit reports them
again, so a later drive reports what a run did, and `emit_warning_once` keeps a
warning from appearing twice in one drive.

A warning points at the macro call. `IO.warn(message, __CALLER__)` and
`IO.warn(message)` both point there. `IO.warn(message, file: file, line: line)`
points at that line when `file` is the call's own file and the line exists, and
otherwise at the macro call with a note naming `file:line`, since a diagnostic
points only into source the compiler holds. Warnings from one call share its
span, so they print in message order rather than emission order.

A macro runs while the module that invokes it is being defined, so the
functions of that module do not exist yet. A macro, or a function its program
calls, that calls into that module makes the module's definition wait on itself.
The stall report names the call as an undefined function, "(function not
available)", with the macro in a note (see fact-engine.md, the terminal
report). A module body that invokes its own macro is refused where it is
written, as `macro/own-module-item-call`.

One subtle but important lifetime rule lives here:

- `run_backend_entry_on_process(...)` is borrowing the quoted-source process,
  not running an ordinary throwaway runtime task
- when that borrowed backend entry completes, compiler2 must keep the process
  alive exactly as a quoted-source heap carrier
- ordinary backend-task exit cleanup such as deferred binview teardown is
  therefore wrong on this path, because a returned quoted root may still point
  at long shared-binary payloads nested inside the source graph

That rule is what keeps forwarded whole-module source fragments with long
`@doc` payloads readable after macro execution.

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
  {:def, [], [{:answer, [], []}, [{:do, 42}]]}
end

make_answer()
def main(), do: answer()
```

`ScopeCode`:

1. reserves `make_answer/0`
2. publishes its raw `FunctionSource`
3. hits `make_answer()`
4. waits for the hidden macro root's `RootBackendProduct` if needed
5. runs the macro and gets quoted `def answer(), do: 42`
6. applies that fragment as source
7. publishes `answer/0`, then `main/0`

The macro changes what exists in the module, so it runs eagerly.

**Body-local macro**

```text
defmacro inc(x), do: quote do: unquote(x) + 1
def main(), do: inc(41)
```

`ScopeCode` publishes raw `FunctionSource(main)` that still contains `inc(41)`.

Later, `DefineFunction(main)` triggers `ExpandFunctionSource(main)`:

1. find `inc(41)` in the `do:` body
2. wait for the hidden macro root's `RootBackendProduct` if needed
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
- `[fz, compiler2, pull, product, evaluated]` and
  `[fz, compiler2, pull, product, cache_hit]`
  retained product evaluation and reuse
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
- `require` and `import` gate remote macros
- item macros are eager source fragments
- ordinary function-body macros are lazy behind demand
