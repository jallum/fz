# Intrinsics

An intrinsic is an operation the compiler and runtime implement together.
The runtime library declares it as a function with an explicit operation:

```fz
intrinsic "sub_fi" fn fz_op_sub_fi(float, integer) :: float
```

The string identifies the operation at declaration resolution. The function
name remains an ordinary namespace binding: a user function with the same
spelling has its own `FunctionId` and body.

`NativeDeclaration` separates extern and intrinsic source forms on
`FunctionSurface`. Both reuse the existing signature parser, type resolver,
`FunctionDefined`, and `LoweredBody` facts. `LowerFunction` resolves an intrinsic
name to the closed `Intrinsic` enum and validates the resolved semantic
signature, including `send`'s same-type result and the payload/destructor
correlation of `make_resource`. Intrinsic declarations are bootstrap-only and
fixed-arity. `LoweredIntrinsic` retains that identity and semantic contract;
`BackendBody::Intrinsic` and native `Prim::Intrinsic` carry the identity through
execution. There is no symbol lookup or extern marshal plan on that path.

Declaration privilege comes from the exact `FunctionSource.owner: SourceOwner`
retained by `FunctionDefined`. Quoted diagnostic spans are user-controlled
metadata: even a user item macro naming bootstrap code in `__fz_span__` cannot
acquire intrinsic or reserved-`fz`-ABI declaration privilege.

Intrinsic callsites enforce the validated semantic contract at the shared
semantic boundary. Provably incompatible input lanes diagnose before backend
lowering; intrinsic declarations do not inherit genuine externs' contract
enforcement exemption. A numeric domain failure during evaluation remains
`IntrinsicFault::Domain`, not an implicit lane conversion.

Unknown arguments retain their observed activation types and tagged transport
lanes. Every intrinsic execution checks the descriptor's `Domain::runtime_kinds`
before reading a scalar payload or performing the operation. Native lowering
uses the existing value-kind tests and branches to `Domain` on a mismatch;
the interpreter asks the same admitted-kind table. Integer and float lanes are
exact, binary lanes accept every `ValueKind::BINARY_REPRS` representation, and
value lanes require no kind test. Known scalar inputs retain their raw ABI
lanes. Admission belongs to the intrinsic operation, so direct calls and
function references reach the same check without another dispatch wrapper.

## One descriptor, mechanical consumers

`runtime/src/intrinsic.rs` owns `Intrinsic`, `Descriptor`, and `IntrinsicFault`.
The descriptor names the operation, each input domain, the result domain, guard
admissibility, and effects. Numeric and comparison identities preserve operand
order. `DivII` truncates integers; `SlashII` takes integers and returns a float.
Widening equality and structural identity are distinct comparisons.

The interpreter consumes the descriptor directly. Native codegen emits typed
instructions or calls the existing runtime primitives. Ordering and equality
reuse the term comparator and its unboxed adapters. Floating remainder calls
the runtime's `fz_op_rem_ff`, because Cranelift has no remainder instruction.

The seven process operations are `Panic`, `SelfPid`, `Send`, `Spawn`, `SpawnOpt`,
`MakeRef`, and `MakeResource`. They consume the ordinary runtime context.
`Callable(0)` admits spawn inputs and `Callable(1)` admits resource destructors.
Admission tests closure kind before reading its source arity from the existing
closure header; native code uses `fz_closure_arity_ref`, the opaque-word adapter
to that same runtime accessor. These checks precede scheduler hooks and resource
registration. World still owns erased pid/cpointer types and payload/destructor
correlations; runtime admission does not re-prove them.
`SpawnOpt` takes an integer heap-size hint. `fz_panic` is also a real native
export, so the extern ABI table records its actual process-taking `Fz` ABI;
the intrinsic declaration itself carries no foreign ABI.

## Value or fault

Numeric evaluation returns `Result<NumericValue, IntrinsicFault>`. Checked
integer overflow, negating `i64::MIN`, division/remainder by zero, and a
nonfinite float result are faults. `i64::MIN / -1` and `i64::MIN % -1` both
fault. Native instructions branch to the same named fault categories before
publishing a result. Ordinary interpreter execution reports the fault through
its error boundary; compiled execution reaches the fatal runtime boundary.
Faults remain observable when a caller discards the result.
Typed comparisons retain an observable domain fault when the activation's
observed inputs are not proved inside the validated semantic parameters, even
when the result is discarded. Statically admitted comparisons remain pure;
equality's unrestricted value inputs need no admission failure. Descriptor
operation faults remain separate from this activation-specific admission fact,
so admitting arithmetic inputs does not erase overflow, zero-divisor, or
nonfinite-result faults.

`Descriptor::guard_admissible` marks arithmetic, negation, and comparisons.
Process effects are inadmissible. A fault is distinct from every language
value, including `false` and `nil`; this contract does not grant permission to
an arbitrary extern or to a same-spelled user function.

## Proof signals

`compiler2_every_intrinsic_reaches_native_as_identity_without_extern_metadata`
checks the complete descriptor set against production native artifacts, empty
intrinsic marshal metadata, and retained allocations on unchanged/unrelated
requests. `typed_intrinsics` exercises every returning identity on interpreter,
JIT, and AOT; `intrinsic_panic` covers the diverging identity. The adjacent
intrinsic fault fixtures pin the ordinary failure boundary.
`intrinsic_runtime_lanes` covers dynamic scalar success, a named function
reference, inline/shared binaries, and unrestricted value equality. The
adjacent runtime-domain and unused-comparison fixtures require `Domain` on
every execution door, before an unchecked unbox or term comparison can run.
`intrinsic_runtime_processes` passes callable values through an `any`-typed map
lookup before spawn and resource operations. The adjacent process-domain
fixtures reject non-callables and wrong source arities before invoking hooks.
`compiler2_intrinsic_domain_effects_follow_observed_inputs` checks comparison
effect precision and the retained raw-versus-tagged input ABI.
