use super::super::drive::Job;
use super::super::drive_harness::{Drive, Settled, module_name};
use super::super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission};
use crate::telemetry::{Capture, ConfiguredTelemetry};

fn run(source_name: &str, source: &str) -> (Result<i64, String>, Capture) {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some(source_name.to_string()),
        text: source.to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    (compiler.run_root_interp(root), diagnostics)
}

#[test]
fn quote_uses_raw_two_tuples_and_ast_nodes_for_every_other_tuple_arity() {
    let (result, diagnostics) = run(
        "quoted_tuple_arities.fz",
        concat!(
            "defmacro tuple_shapes() do\n",
            "  zero = quote do: {}\n",
            "  one = quote do: {:one}\n",
            "  two = quote do: {:one, :two}\n",
            "  three = quote do: {:one, :two, :three}\n",
            "  case {zero, one, two, three} do\n",
            "    {{:\"{}\", %{}, []}, {:\"{}\", %{}, [:one]}, {:one, :two}, {:\"{}\", %{}, [:one, :two, :three]}} -> quote do: identity(42)\n",
            "    _ -> quote do: identity(0)\n",
            "  end\n",
            "end\n",
            "def identity(value), do: value\n",
            "def main(), do: tuple_shapes()\n",
        ),
    );

    assert_eq!(result, Ok(42), "diagnostics: {:?}", diagnostics.events());
}

#[test]
fn quote_preserves_keyword_tuples_in_a_generated_function_definition() {
    let (result, diagnostics) = run(
        "quoted_generated_definition.fz",
        concat!(
            "defmacro make_answer() do\n",
            "  do_clause = quote do: {:do, 42}\n",
            "  source = {:def, %{}, [{:answer, %{}, []}, [do_clause]]}\n",
            "  quote do\n",
            "    Fz.Compiler.define(unquote(source), unquote(__CALLER__))\n",
            "  end\n",
            "end\n",
            "make_answer()\n",
            "def main(), do: answer()\n",
        ),
    );

    assert_eq!(
        result,
        Ok(42),
        "the quoted `[do: 42]` must contain a raw two-tuple so the generated function remains valid source; diagnostics: {:?}",
        diagnostics.events(),
    );
}

/// The atom literals a function's settled return type admits.
fn settled_return_atoms(settled: &Settled, name: &str) -> Vec<String> {
    let function = settled.function(name, 0);
    let return_ty = settled
        .return_types()
        .last_for_function(settled.root(), function)
        .return_ty;
    settled.compiler().types_for_test().atom_literals(&return_ty)
}

/// `alias Foo.Bar, as: B` makes `B` stand for the module it names, so its
/// value's type is exactly the singleton atom of that module's full name.
#[test]
fn an_alias_in_value_position_is_the_singleton_atom_of_its_target() {
    let settled = Drive::fixture(696).settle();
    assert_eq!(
        settled_return_atoms(&settled, "aliased"),
        vec!["Elixir.Foo.Bar".to_string()]
    );
}

/// A name no module defines is still its own atom, and naming it is not a
/// reason to define, or even ask about, a module of that name.
#[test]
fn a_name_no_module_defines_is_its_atom_and_starts_no_module_work() {
    let settled = Drive::fixture(700).settle();
    assert_eq!(
        settled_return_atoms(&settled, "never"),
        vec!["Elixir.Nope.Never".to_string()]
    );

    let never = module_name("Nope.Never");
    let world = settled.world();
    let module_work = settled.outputs().stops_matching(|job| match job {
        Job::DefineModule(module) | Job::DefineModuleInterface(module) => world.module_name(*module) == Some(&never),
        _ => false,
    });
    assert!(
        module_work.is_empty(),
        "no module job runs for Nope.Never: {module_work:?}"
    );
}
