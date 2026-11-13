# Modules and Namespaces

A module is a unit of naming and definition. The module subsystem owns four
things: stable identity, the lifecycle a module passes through from a bare
reference to optional source plus optional callable interface, the namespace
chain that resolves names inside a scope, and how runtime-library modules enter
a compile. The end-to-end flow that drives these transitions is in
[`pipeline`](pipeline.md); this doc is the data model behind the definition
stratum.

## Identity is allocated on reference

Referencing a module or a function allocates a stable id immediately; defining it
later fills the state behind that id.

- `ModuleId` — `reference_named(name)` for a top-level/runtime module,
  `reference_child_module(parent, local)` for a nested one. `ModuleId::GLOBAL`
  (`0`) is the top-level scope. `ModuleMap` keys and retains `ModuleDenotation`:
  a named module's parsed `ModuleName`, or an implementation's exact
  protocol/target pair. Source boundaries survive reservation, definition,
  lookup, function denotations, and reflected quoted references.
- `FunctionId` — `reference_function(module, name, arity)`; generated lambdas get
  ids through `reference_generated`.
- `FunctionRef { module, denotation }` pairs a World-local module coordinate
  with the shared immutable `FunctionDenotation`. Its typed source origin owns
  semantic order; local ids key resolution and facts.

A function or module can be *referenced* without being *defined*: a placeholder
id exists, callers can name it, and the surface fills in when its source is
scoped. An uncalled definition stays a cold fact (see [`pipeline`](pipeline.md)).

## The module lifecycle

`ModuleState` is the slot behind a `ModuleId`. Source/body state and interface
state are separate concerns, so the slot may have either, both, or neither:

```text
Placeholder { interface? }             referenced, no source yet
Indexed { source, interface? }         source discovered during code indexing
Scoped { source, base, interface? }    a base namespace head has been chosen
Defined { source, base, interface }    the module body is published
```

A module's stage only moves forward for the same source: indexing a Scoped or
Defined module again from the source it already has (`ModuleState::reconcile`)
keeps the stage and reports no change, so a file's top-level walk that re-runs
after `ModuleDefined` does not un-define the module it was waiting on. A
different source starts the module over at Indexed.

`ModuleSource { code, parent, source, kind }` carries the source facts and
parent ownership edge. `ModuleMap` supplies the full module denotation directly;
consumers do not reconstruct it from parent and local display spellings.
`kind` is `Body`, `Protocol`, or `ProtocolImpl` (see
[`protocols`](protocols.md)). `ModuleInterface` is the module-owned callable
surface: exported callables are represented by `FunctionId`-backed entries plus
callable kind (`PublicFunction` or `Macro`) and variadic metadata.

Four jobs drive the transitions:

```text
index_code     parse a code contribution; discover_modules registers each nested
               module/protocol as Indexed, then publishes CodeIndexed
scope_code     pick the base namespace, run define_scope over GLOBAL, publish CodeScoped
define_module_interface
               publish an already-known interface for a module that may not have
               source/body state in this compiler run
define_module  scope the module body (or protocol surface) and publish ModuleDefined
```

`define_module` waits for what it needs and asks for it: a child waits on its
parent's `ModuleDefined` (or `CodeScoped` when the parent is global); a
not-yet-pulled runtime module waits on its `CodeIndexed` after
`ensure_runtime_module` submits its source. `define_module` also derives and
publishes `FactKey::ModuleInterface(module)` for source-defined modules.

`require` and `import` refuse a module defined inside the requiring scope's own
body (`World::module_defined_within`, checked in `apply_require` and
`apply_import`), as Elixir does: that module is not loaded until the scope that
defines it has finished. The diagnostic is `resolve/module-not-loaded` at the
`require`/`import` span. A module defined earlier outside the requiring
`defmodule` is required normally.

The important split is:

- `FactKey::ModuleDefined(module)` — local body/scoping readiness
- `FactKey::ModuleInterface(module)` — cross-module callable visibility

## Namespaces are a savepoint chain

Name resolution is an append-only chain. A `Namespace` is a `BindingId` — a
savepoint into `NamespaceStore.bindings`. Binding a name pushes a
`{ name, symbol, prev }` and returns the new head; lookup walks from a head
backward and the first matching symbol wins. A `NamespaceSymbol` is a `Module`,
`Function`, `Callable`, `Macro`, `Type`, or `Splice`. A `Splice` binds a name to
a quoted AST snippet that the macro expander substitutes in place when the name
is referenced — a generic primitive whose only current use is `__ENV__` (see
macro-expansion.md).

```text
bind(head, "add", Function(f))  -> head'      (a new savepoint over head)
lookup(head', "add")            -> Function(f)
bind(head, "t", Type(type_t))    -> head''     (type names use the same chain)
```

This is what lets a scope extend its parent's visibility without copying: a child
scope's base is its parent's head, and entering/leaving a scope is just choosing
which head to bind onto. Type lookups filter for `NamespaceSymbol::Type`, while
value/callable lookups filter for modules/functions/macros, so a type name and a
value name can share spelling without becoming one binding kind.

A `CallableName` asks the chain at most once. Its qualifier is a `ModuleTarget`,
so an alias path written in source (`Unresolved`) stays distinct from an exact
reflected module (`Exact`), and `World::callable_name_qualifier` answers which
module a qualified name names. Nothing splits a rendered `Module.function`
string back into a module and a name: a callable that was already resolved
travels as the function itself.

## A module name is a value

In value position a module alias is an atom, as in Elixir. The decoder turns
`{:__aliases__, meta, [:Foo, :Bar]}` into `Expr::Alias(ModuleName)`, keeping
the segments it was written with. `World::module_alias_atom` answers which atom
that is: it resolves the alias through `resolve_module_name`, so a name the
namespace binds (`alias Foo.Bar, as: B` makes `B` mean `Foo.Bar`) gives its
target and any other name gives itself, and returns
`ModuleName::atom_name`, the full path under the `Elixir` root
(`Elixir.Foo.Bar`). Body lowering and guard reification both ask it, so `B` in
an expression and `x == B` in a guard are the same constant atom, typed as that
singleton atom. A name no module defines is still its atom: resolving it mints
a placeholder id and starts no module work. A qualified callee
(`Foo.Bar.f()`) reads the same segments as its `ModuleTarget::Unresolved`
qualifier.

## A call on a module value

`m.f(a)` whose base is not a module name is a call on the module the value
`m` holds. A field read is the same syntax without the call (`m.f`), and
`m.f.(a)` calls the closure that field holds. Body lowering emits
`LoweredTail::DirectCall` whose callee is
`DirectCallee::ModuleValue { module, function }`: the value of `m`, lowered
before the arguments, and the name `f`. The module is not one of the call's
arguments.

Semantic analysis resolves the call from the type of `m`
(`jobs::semantic::resolve_module_value_call`, `module_value_receiver`). The
atoms in the type say which modules the value can be.

When the type lists its atoms, they are the modules. Each atom names a module
absolutely through `ModuleName::from_atom_name` and `World::reference_module`,
and `World::module_public_function` answers that module's public `f/n`; a
qualified callee in source asks the same method.

When the type holds atoms it does not list (`atom`, `any`), the value can be
any module a value can name. `World::nameable_modules` is that set: every
module whose source the compile has indexed (`source_publish::
publish_module_indexed`) and every module a lowered body writes as a value, in
an alias or a struct (`Lowerer::name_module_as_value`). The set is the
fact `FactKey::NameableModules`, which the call reads whether or not it holds
anything yet. `nameable_module_callees` waits for each of those modules to be
defined, reads its `ModuleInterface`, and keeps the ones that have a public
`f/n`. It asks for no function body, so a module that lacks `f/n` is defined
for the call and none of its functions is compiled for it.

Each function is then resolved as any direct call is, and its targets carry
the atom that selects them in `CallTargetSummary.selector`.

The values no module claims are the receiver's type less the selectors. When
that is not empty the call has one more target, the miss:
`SelectedCallee::Undefined(UndefinedFunction)`, selected by that remainder,
with no activation and the return type `none`. It carries the function, the
arity and the atoms of the nameable modules that lack the function. The miss
goes through `call_destinations` as any target does and materializes as
`CallTarget::Undefined`.

| type of `m` | the call |
| --- | --- |
| one atom | one target: `CallDestinations::Direct`, and no read of `m` at run time |
| several atoms | one target per atom: `CallDestinations::Dispatch`, whose plan reads `m` as its first input |
| `atom`, `any`, or a listed atom joined with something that is no atom | a target per nameable module that has `f/n`, and the miss |
| a type holding no atom | compile error `type/module-value-call` |
| a listed atom outside the `Elixir.` namespace | compile error `type/module-value-call` |
| a listed atom naming no module, or a module without `f/n` | the compile error a qualified call to it gets |

Both executors lower the miss as a raise that shows the value of `m`. Native
lowering (`NativeLowerer::raise_undefined_function`) ends the block in
`Term::RaiseUndefined`, whose codegen calls `fz_raise_undefined_function`; the
interpreter (`ir_interp::backend::raise_undefined_function`) calls
`failure::raise_undefined_function`. The runtime words the exception as Elixir
does:

| value of `m` | raises |
| --- | --- |
| an atom naming a module that lacks the function | `UndefinedFunctionError`, `function M.f/n is undefined or private` |
| any other atom | `UndefinedFunctionError`, `function :a.f/n is undefined (module :a is not available)` |
| `nil` | `UndefinedFunctionError`, `function nil.f/n is undefined` |
| a value that is no atom, `n > 0` | `ArgumentError`, `you attempted to apply a function on V. Modules (the first argument of apply) must always be an atom` |
| a value that is no atom, `n == 0` | `ArgumentError`, `you attempted to apply a function named :f on V. ...` |

An `UndefinedFunctionError` carries `module`, `function`, `arity`, `reason`
(`nil`) and `message`.

A module in a library file the compile never indexed is not nameable, so a
call that reaches it by a computed atom raises "is not available". With no
arguments and parentheses, `m.f()` on a map raises `ArgumentError`; Elixir
reads the field and warns.

A dispatch plan's inputs are the selector and then the arguments
(`CallSiteSummary::arity`). `BackendTail::DirectCall.selector` holds the value
of `m`; both executors read it for the plan and pass only `args` to the
target, so the arguments stay one-for-one with the callee's inputs.

The activation key keeps `m` whole (`jobs::keying`), so callers passing
different modules keep different keys and each key's call has one target.
`e.__struct__.message(e)` is this call: the `__struct__` field of a struct
type is one atom.

Fixtures `00864` (one module), `00865` (several), `00867` (an atom made at
run time) and `00869` (every miss) agree with Elixir on interp, run and build;
`00866` is the refusal.

## Scoping a body

`define_scope` walks a scope's items in two passes so bodies can reference names
declared later in the same scope:

1. **Reserve.** Bind every local function (as `Function`/`Macro`), every noted
   `@type` name (as `Type`), and every child module / protocol name, so forward
   references resolve in both value and type positions.
2. **Apply, in source order.** Resolve `alias`, `import`, and `require`.
   Exact `only:` imports/requires can mint `FunctionId`s lazily by recording
   interface expectations and binding `Callable` placeholders immediately.
   Set-valued `import M` / `import M, except: ...` and the corresponding
   `require` forms wait on `FactKey::ModuleInterface(module)`, because they
   need the provider's full exported callable set before they can bind names.
   `require` also publishes the required module path into the lexical
   namespace so qualified remote macro calls can resolve the module name. For
   a dotted path such as `Foo.Bar`, the full path is made visible through
   `Foo`; the short name `Bar` still requires an explicit `alias`.
   Separately, `require` records the selected remote macro `FunctionId`s that
   this scope may expand. A visible module without a matching required macro
   entry still trips `macro/not-required`.
   A module or protocol declaration binds a name in its declaring scope as
   Elixir's `defmodule` does: a single-segment name binds itself; a dotted name
   nested in a module binds only its first segment, to the parent's child of
   that segment (`defmodule H.T` inside `M` defines `M.H.T` and makes `H.T`
   reach it); a dotted name declared at the root binds nothing, so `Geo.Pt` is
   reached only by its full path and `Pt` stays free for another module.
   Later jobs wait only when they need more than that placeholder:
   macro expansion waits for the provider interface when it must decide whether
   a reserved callable is a macro, and module-interface publication validates
   that each exact expectation was actually exported. Then define each reserved
   function and scope each child module onto the current head.

A non-private function or macro becomes a `ModuleInterfaceCallable`; `defp`
functions stay callable in-module but out of the interface. Non-global
modules that do not define `__info__/1` get a synthesized ordinary function
source for their callable interface. The pass returns the finished namespace head
plus the callable interface, which `define_module` freezes onto the module slot.

## Runtime library and the prelude

Runtime-library modules are not a special class. At construction the world
`reference_named`s each runtime module so its name is a stable id, but it does
**not** submit any source. The first real reference pulls the owning module's
source through `ensure_runtime_module`, which `submit_code`s it as ordinary code;
the same `index_code` / `scope_code` / `define_module` jobs handle it. Runtime
registration happens before named-parent resolution, so a dotted runtime module
such as `String.Chars` owns and indexes its own source instead of waiting for
its ordinary `String` parent.

A runtime module is registered in two places: its `RuntimeModuleSource` entry in
`src/modules/runtime_library.rs`, which names the file under `lib/`, and an
`alias` line in `lib/runtime.fz`. Without the alias a call such as
`OptionParser.parse/2` from user code is an unresolved direct runtime callee.

The one place the bootstrap is special is *reading*: `is_bootstrap(code)` (the
prelude plus the runtime modules) is read canonically — definition heads are parsed as
definitions rather than macro calls — because the macros that implement def-heads
are defined in the bootstrap and cannot be bounced through. Everything else is
ordinary user source; see macro-expansion.md.

The prelude (`runtime.fz`) is scoped first as ordinary code: when `scope_code`
sees the prelude it scopes from an empty namespace and saves the resulting head
as the prelude head; every other code contribution then scopes from that head
(and waits on the prelude's `CodeScoped`). So default visibility is a saved
namespace head, not a compiler phase.

Root submission does not force that prelude work by sweeping all code. A root
waits for its entry function facts; the function-source demand selects the
indexed code surface that can publish that entry, and that code's `ScopeCode`
is what pulls `CodeScoped(runtime_prelude)` if needed. The ownership chain is
therefore root -> entry fact -> candidate source surface -> prelude namespace,
never root -> every code contribution.

There is no `.fzi`/`.fzo` store and no separate-compilation sidecar: a program's
module world is the source it submits plus the runtime-library source pulled on
demand. A user module is present only when its source was submitted.

## Where it lives

```text
identity.rs    ModuleId / FunctionId / FunctionRef, ModuleState, ModuleSource,
               ModuleMap, FunctionMap
module_interface.rs
               ModuleInterface, callable entries, exact expectations, ready/pending queries
namespace.rs   NamespaceStore, BindingId (Namespace), NamespaceSymbol
runtime.rs     bootstrap — reference runtime module names; pull source lazily
jobs/source.rs index_code / scope_code / define_module / define_scope / discover_modules
```

## Proof gates

```text
cargo test --lib compiler2::world_test
cargo test --lib compiler2::namespace_test
cargo test --lib compiler2::drive_test::a_call_on_one_module_is_a_direct_call_keyed_by_the_module
cargo test --lib compiler2::drive_test::a_call_on_one_of_two_modules_dispatches_on_the_module_and_passes_only_the_arguments
cargo test --lib compiler2::drive_test::compiler2_submit_root_pulls_scope_and_seeds_entry_semantics_without_warming_foo
cargo test --lib compiler2::drive_test::compiler2_enum_reduce_selects_list_protocol_impl_and_callable_reducer
```
