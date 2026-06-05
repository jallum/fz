use super::*;
use crate::frontend::resolve::flatten_modules;
use crate::ir_lower;
use crate::ir_planner::plan_module_with_role;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;

fn pipeline<T: Types<Ty = Ty> + ClosureTypes + RenderTypes>(t: &mut T, src: &str) -> (Program, Module, ModulePlan) {
    let toks = Lexer::with_source_name(src, "<test>")
        .tokenize(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("lex");
    let prog = Parser::new(toks)
        .parse_program(&crate::telemetry::ConfiguredTelemetry::new())
        .expect("parse");
    let prog = flatten_modules(t, prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("flatten");
    let ir = ir_lower::lower_program(t, &prog, &crate::telemetry::ConfiguredTelemetry::new()).expect("lower");
    let mt = plan_module_with_role(t, &ir, &crate::telemetry::ConfiguredTelemetry::new(), "test");
    (prog, ir, mt)
}

#[test]
fn spec_matching_inferred_passes() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
fn main(), do: dbg(M.add1(41))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(diags.is_empty(), "unexpected diags: {:?}", diags);
}

#[test]
fn spec_wider_than_inferred_passes_success_typing_style() {
    // Declared spec accepts `integer`; inferred is the narrower
    // `int_lit(41)`. int_lit(41) ⊆ integer, so this passes.
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
fn main(), do: dbg(M.add1(41))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        diags.is_empty(),
        "wider declared must accept narrower inferred; got: {:?}",
        diags
    );
}

#[test]
fn spec_disjoint_from_inferred_fails() {
    // Declared accepts `float`; inferred from callsite is int.
    // int ⊄ float, so this fails.
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @spec add1(float) :: float
  fn add1(n), do: n + 1
end
fn main(), do: dbg(M.add1(41))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(!diags.is_empty(), "disjoint spec must fail");
    let msg = format!("{:?}", diags[0].message);
    assert!(
        msg.contains("not a subtype"),
        "expected subtype-violation diag, got: {}",
        msg
    );
}

#[test]
fn multi_spec_overload_arrows_cover_each_inferred_shape() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @spec echo(integer) :: integer
  @spec echo(float) :: float
  fn echo(x :: integer), do: x
  fn echo(x :: float), do: x
end
fn main() do
  dbg(M.echo(1))
  dbg(M.echo(1.5))
end
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        diags.is_empty(),
        "each inferred shape should be covered by one declared arrow; got: {:?}",
        diags
    );
}

#[test]
fn multi_spec_validation_preserves_param_result_correlation() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @spec echo(integer) :: float
  @spec echo(float) :: integer
  fn echo(x :: integer), do: x
  fn echo(x :: float), do: x
end
fn main() do
  dbg(M.echo(1))
  dbg(M.echo(1.5))
end
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        !diags.is_empty(),
        "unioning inputs/results would pass this; correlated arrows must fail"
    );
    assert!(diags[0].message.contains("not a subtype"));
}

#[test]
fn spec_resolves_against_module_type_env() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @type id :: integer
  @spec lookup(id) :: id
  fn lookup(x), do: x
end
fn main(), do: dbg(M.lookup(7))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        diags.is_empty(),
        "alias-based spec should resolve and pass; got: {:?}",
        diags
    );
}

#[test]
fn protocol_domain_spec_accepts_known_impl_target() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defprotocol Enumerable do
  fn reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  fn reduce(list, acc, reducer), do: acc
end

defmodule M do
  @spec use(Enumerable.t(integer)) :: integer
  fn use(xs), do: 1
end
fn main(), do: dbg(M.use([1]))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        diags.is_empty(),
        "known protocol impl target should satisfy protocol domain; got: {:?}",
        diags
    );
}

#[test]
fn protocol_domain_spec_rejects_disjoint_target_without_impl() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defprotocol Enumerable do
  fn reduce(enumerable, acc, reducer)
end

defimpl Enumerable, for: List do
  fn reduce(list, acc, reducer), do: acc
end

defmodule M do
  @spec use(Enumerable.t(integer)) :: integer
  fn use(xs), do: 1
end
fn main(), do: dbg(M.use(1))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(!diags.is_empty(), "integer has no Enumerable impl");
    assert!(diags[0].message.contains("not a subtype"));
}

#[test]
fn spec_with_unknown_alias_fails_at_validation() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @spec one(unknown_thing) :: integer
  fn one(_), do: 1
end
fn main(), do: dbg(M.one(0))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(!diags.is_empty(), "unknown alias must surface a diag");
    let msg = format!("{:?}", diags[0].message);
    assert!(
        msg.contains("unknown type name"),
        "expected unknown-name diag, got: {}",
        msg
    );
}

#[test]
fn spec_validation_skips_any_key_specs() {
    // Validation must skip any-key specs when they exist (they have
    // `any()` on every param, which would clash with any
    // narrow declared @spec). Post-.29.12.6, fns with fully-typed
    // direct callsites have their any-key dropped — this test
    // covers both scenarios via a fn that *does* keep its any-key
    // because it's also reachable via a closure/cont path with a
    // narrow capture but `any` slot 0.
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
fn main(), do: dbg(M.add1(41))
"#,
    );
    // Validation passes — either the any-key was dropped (.29.12.6)
    // or it was kept and validation correctly skipped it.
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        diags.is_empty(),
        "validation must pass regardless of any-key presence; got: {:?}",
        diags
    );
}

#[test]
fn fn_without_spec_is_not_validated() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
defmodule M do
  fn double(x), do: x * 2
end
fn main(), do: dbg(M.double(7))
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        diags.is_empty(),
        "fn without @spec should produce no diags; got: {:?}",
        diags
    );
}

#[test]
fn spec_on_top_level_fn_uses_empty_env() {
    let mut ct = crate::types::new();
    let (prog, ir, mt) = pipeline(
        &mut ct,
        r#"
@spec one() :: integer
fn one(), do: 1
fn main(), do: dbg(one())
"#,
    );
    let diags = validate_specs(&mut ct, &prog, &ir, &mt);
    assert!(
        diags.is_empty(),
        "top-level @spec with builtin scalar must pass; got: {:?}",
        diags
    );
}
