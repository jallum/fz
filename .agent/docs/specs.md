# Specs

`src/specs` is no longer a spec semantic engine. It is the shared structural
shape model used by compiler2 while resolving source-level type syntax.

The retained API is intentionally small:

- `ResolvedTypeShape` mirrors source type structure: scalar leaves, literals,
  variables, named type applications, resources, lists, tuples, arrows, unions,
  and struct records.
- `ResolvedStructFieldShape` carries struct-record field names and field shapes.

Compiler2 owns the active contract path:

- `compiler2/type_expr.rs` parses type syntax without consulting the old
  `ModuleTypeEnv`.
- `compiler2/resolve.rs` resolves names against the namespace captured where a
  declaration appeared and returns hard compiler2 `Ty` values plus parallel
  `ResolvedTypeShape` values.
- `compiler2/contract.rs` and the compiler2 type/arrow-matching code consume the
  resolved contract data.
- `Types::close_bounds` is the shared addressed-`TypeVarId` resolver for `when`
  dependencies. It closes only ground acyclic RHS chains; unresolved and cyclic
  components remain symbolic. Contract matching and declared input domains both
  use this one interpretation.
- `FunctionContract` stores resolved protocol-domain marker obligations per
  arrow. The current obligation identity is the resolved opaque marker tag
  (`protocol::<Name>.t`) wrapped as a `ProtocolDomainObligation`; it is
  classified from explicit positive markers in hard `Ty` values plus the
  contract bounds sidecar, not from source refs, negative/complement clauses, or
  protocol impl registries. Protocol-domain arrows can still refine calls, but
  arrows with obligations are skipped for fatal
  `spec/violation` decisions until protocol-domain validation is implemented;
  concrete arrows in the same overload set remain enforceable.

The old `src/specs` operations were removed with the old-world compiler:
scheme matching, overload-set application, structural correspondence grouping,
and declared-vs-inferred coverage checking no longer live in this module. The
old files `apply.rs`, `match.rs`, `select.rs`, `validate.rs`, and
`specs_test.rs` are gone.

Current proof points:

```text
cargo test --lib compiler2::world_test::compiler2_resolve_spec_resolves_types_shapes_and_constraints_against_the_captured_namespace
cargo test --lib compiler2::types::arrow_match
cargo test --test fixture_matrix spec_ok
cargo test --test fixture_matrix spec_boundary
cargo test --test fixture_matrix spec_mixed_protocol_concrete_violation
```
