# Semantic Codegen Operations

The unit of Cranelift lowering is one fz function body. That body needs a
Cranelift `FunctionBuilder`, the Cranelift module, immutable `CodegenEnv`, a
mutable per-function `CodegenCache`, and function-local imports.

`CodegenFn` is the fz-owned semantic boundary for that unit of work. Ordinary
lowering constructs one `CodegenFn<BodyContext>` per lowered fz function body;
it owns the runtime refs and the function-local `FuncId -> FuncRef` import
table. The short-lived `CodegenFnBody` view carries the active
`FunctionBuilder`, module, and per-function cache while a body operation is
being emitted. `CodegenFnSite` is the smaller view for semantic operations
that need the active builder and module but not the cache, such as closure
capture loads/stores and closure code/halt-kind reads. Semantic operations such
as list access, closure capture access, value boxing/unboxing, struct field
writes, owned-cons reuse, argument coercion, typed frame stores, and alias
publication should flow through these contexts instead of threading raw
lowering plumbing through helper signatures.

Value coercion is part of that semantic surface. Ordinary body lowering should
prefer `CodegenFnBody` for cache-bearing operations such as `value_as_any_ref`,
`tagged_var`, `any_ref_for_var`, `value_raw_atom`, and publication. Cache-free
operations such as truthiness checks, type-tag tests, and raw int extraction may
use `CodegenFnSite`. The broad `CodegenFn` value methods are implementation
plumbing for those semantic views. They are intentionally kept at
module-internal visibility and should only be reached from `CodegenFnBody`,
`CodegenFnSite`, or closely-related value helpers; ordinary lowering should not
call them directly.

Generated runtime shim bodies do not have a `CodegenEnv`, so they use
`CodegenFn<RuntimeShimContext>` through `CodegenFn::for_runtime_shim`. That
constructor is a boundary marker, not a shortcut for ordinary lowering helpers.
Shared semantic operations may be implemented for both context markers, but
new ordinary-function-only state should live on `BodyContext` rather than being
made available to shims by accident.

`CodegenFn` methods may currently call runtime BIFs, but the call is an
implementation detail. A later inline CLIF implementation should be local to
the semantic method.

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
dynamic user-function calls, or inside `CodegenFn`/semantic operation
implementations. Codegen changes should remove the bridge code they replace
before landing; do not leave old and new paths in parallel.

Small runtime helper calls in ordinary body lowering should be named
`CodegenFn` semantic methods before they spread. `call.rs`, `closure.rs`, and
`entry.rs` are pinned to zero direct function imports; new direct imports there
should move behind `CodegenFn` unless they are truly dynamic user-function
boundaries.

Current signal: `call.rs`, `closure.rs`, `entry.rs`, and `support.rs` have zero
direct `declare_func_in_func` imports; `call.rs`, `closure.rs`, and
`support.rs` use `CodegenFn::body(...)` for migrated value/list operations;
call-argument coercion and typed callee-frame stores live on `CodegenFnBody`;
ordinary `prim.rs`/`terminator.rs` value coercions flow through `CodegenFnBody`
or `CodegenFnSite`; direct `cx.value_*`, `cx.tagged_var`, `cx.any_ref_for_var`,
`cx.list_*`, `cx.ref_tag`, and `cx.mark_published_ref_aliased` calls are absent
outside the semantic context/value implementation modules; and retired free
helpers have been deleted rather than kept as compatibility shims. Larger
`prim.rs` and `terminator.rs` still contain documented boundary imports for
dynamic calls, externs, and data imports; reduce those only by moving a complete
semantic operation behind `CodegenFn`, `CodegenFnBody`, or `CodegenFnSite`.
