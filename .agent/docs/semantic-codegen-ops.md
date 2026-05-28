# Semantic Codegen Operations

The unit of Cranelift lowering is one fz function body. That body needs a
Cranelift `FunctionBuilder`, the Cranelift module, immutable `CodegenEnv`, a
mutable per-function `CodegenCache`, and function-local imports.

`CodegenFn` is the fz-owned semantic boundary for that unit of work. Ordinary
lowering constructs one `CodegenFn` per lowered fz function body; it owns the
runtime refs and the function-local `FuncId -> FuncRef` import
table. The short-lived `CodegenFnBody` view carries the active
`FunctionBuilder`, module, and per-function cache while a body operation is
being emitted. `CodegenFnSite` is the smaller view for semantic operations
that need the active builder and module but not the cache, such as closure
capture loads/stores and closure code/halt-kind reads. Semantic operations such
as list access, closure capture access, value boxing/unboxing, struct field
writes, owned-cons reuse, argument coercion, typed frame stores, and alias
publication should flow through these contexts instead of threading raw
lowering plumbing through helper signatures.

Runtime-BIF operations -- value boxing/unboxing, ref-tag and truthiness reads,
list head/tail and cons, closure capture get/set, frame and closure allocation,
struct field writes, alias publication, and continuation materialization -- are
defined once on the `CallSite` trait. Both `CodegenFnBody` and `CodegenFnSite`
implement it by exposing their `(CodegenFn, FunctionBuilder, module)` parts;
the operations are default methods built on `call`/`call1`, so a lowering site
emits them as `view.operation(domain_inputs)` with no builder/module threading
and no per-view delegation. `CodegenFn` itself keeps only `func_ref` (the
import-table primitive) and the value-coercion methods; it no longer carries
per-BIF wrappers.

Value coercion is part of that semantic surface. Ordinary body lowering should
prefer `CodegenFnBody` for cache-bearing operations such as `value_as_any_ref`,
`tagged_var`, `any_ref_for_var`, `value_raw_atom`, and publication. Cache-free
operations such as truthiness checks, type-tag tests, and raw int extraction may
use `CodegenFnSite`. The value-coercion methods stay on `CodegenFn`; they reach
runtime BIFs through `CodegenFn::site(...)` rather than carrying their own
builder/module wrappers, and ordinary lowering reaches them through the views.

Generated runtime shim bodies do not have a `CodegenEnv`, so they are built
through `CodegenFn::for_runtime_shim`, which takes runtime refs directly. That
constructor is a boundary marker, not a shortcut for ordinary lowering helpers.
Shims operate only through the cache-free `CodegenFnSite` view; the cache-bearing
`CodegenFnBody` value operations structurally require a `CodegenCache` and a
`var_env` that the shim path never supplies, so ordinary-function-only state
stays out of shims by construction rather than by a type-level marker.

`CallSite` operations may currently call runtime BIFs, but the call is an
implementation detail. A later inline CLIF implementation should be local to
the semantic method, which has exactly one definition to rewrite.

When a lowering site needs the current `FunctionBuilder`, module, and
`CodegenCache` together, use the short-lived `CodegenFn::body(...)` surface
and call intent methods on that body surface. This keeps Rust's explicit
mutable borrows while giving call sites one semantic receiver to migrate
toward; do not hide these borrows behind raw pointers or parallel local caches.
Prefer `body.operation(domain_inputs...)` over helpers shaped like
`helper(cx, b, jmod, cache, ...)`, and bind the body view before use instead
of chaining `cx.body(...).operation(...)` at call sites. The body surface
should grow only with semantic operation names that have active migrated
callers, rather than by exposing generic builder or cache accessors.
If an operation does not need the per-function cache, use `CodegenFn::site(...)`
instead of forcing a cache dependency into the call path.

Direct `declare_func_in_func` use belongs at module-construction boundaries,
dynamic user-function calls, or inside `CallSite`/semantic operation
implementations. Codegen changes should remove the bridge code they replace
before landing; do not leave old and new paths in parallel.

Small runtime helper calls in ordinary body lowering should be named `CallSite`
operations before they spread. `call.rs`, `closure.rs`, and `entry.rs` are
pinned to zero direct function imports; new direct imports there should move
behind a `CallSite` operation unless they are truly dynamic user-function
boundaries.

Current signal: the runtime-BIF wrappers live once on the `CallSite` trait, so
`fn_ctx.rs` carries a single `b: &mut FunctionBuilder` parameter (the `func_ref`
import primitive); `CodegenFn` exposes no marker type parameter, no per-BIF
wrapper, and no satellite import struct. `call.rs`, `closure.rs`, `entry.rs`,
and `support.rs` have zero direct `declare_func_in_func` imports; call-argument
coercion, typed callee-frame stores, and struct field writes live on
`CodegenFnBody`; ordinary `prim.rs`/`terminator.rs` value coercions flow through
`CodegenFnBody` or `CodegenFnSite`; direct `cx.<bif>(b, jmod, ...)` wrapper calls
are absent outside the value-coercion helpers' `CodegenFn::site(...)` bridge; and
retired free helpers have been deleted rather than kept as compatibility shims.
Larger `prim.rs` and `terminator.rs` still contain documented boundary imports
for dynamic calls, externs, and data imports; reduce those only by moving a
complete semantic operation behind a `CallSite` operation, `CodegenFnBody`, or
`CodegenFnSite`.
