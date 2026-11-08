use super::super::drive::Job;
use super::super::drive_harness::{Drive, Settled, module_name};
use super::super::{CodeSubmission, Compiler2, ExecutableNeed, RootSubmission, RunFailure};
use crate::telemetry::{Capture, ConfiguredTelemetry};

fn run(source_name: &str, source: &str) -> (Result<i64, RunFailure>, Capture) {
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

/// What a function's lowered body says about its `try`s: the nesting is
/// readable from the entries alone.
struct TryShape {
    tries: usize,
    handlers: usize,
    pops: usize,
    handler_tails_that_call: usize,
    atom_consts: std::collections::HashMap<String, usize>,
}

fn try_shape(fixture: u32, name: &str, arity: u64) -> TryShape {
    use super::super::body::{ControlEntryOrigin, LoweredBody, LoweredStep, LoweredTail};
    let settled = Drive::fixture(fixture).settle();
    let function = settled.function(name, arity);
    let body = settled.world().lowered_body(function);
    let LoweredBody::Clauses { entries, .. } = &*body;
    let mut shape = TryShape {
        tries: 0,
        handlers: 0,
        pops: 0,
        handler_tails_that_call: 0,
        atom_consts: Default::default(),
    };
    for entry in entries {
        shape.tries += usize::from(matches!(entry.tail, LoweredTail::Try { .. }));
        if entry.origin == ControlEntryOrigin::Handler {
            shape.handlers += 1;
            shape.handler_tails_that_call += usize::from(matches!(entry.tail, LoweredTail::DirectCall { .. }));
        }
        for step in &entry.steps {
            match step {
                LoweredStep::PopHandler => shape.pops += 1,
                LoweredStep::Const {
                    literal: crate::ground_value::GroundValue::Atom(atom),
                    ..
                } => *shape.atom_consts.entry(atom.clone()).or_default() += 1,
                _ => {}
            }
        }
    }
    shape
}

/// `after` alone is one handler whose only job is to run the after body and
/// re-raise: the after body is lowered once on the success path, right after
/// the pop, and once in the handler.
#[test]
fn an_after_is_one_handler_that_runs_the_after_body_and_re_raises() {
    let shape = try_shape(832, "main", 0);
    assert_eq!((shape.tries, shape.handlers, shape.pops), (1, 1, 1));
    assert_eq!(shape.handler_tails_that_call, 1, "the handler ends in the re-raise");
    assert_eq!(
        shape.atom_consts["after_value"], 2,
        "the after body appears on both ways out"
    );
    assert_eq!(shape.atom_consts["body_value"], 1, "the body is lowered once");
}

/// `rescue` and `after` together are two nested tries, `after` outermost: two
/// handlers, two pops, and still one after body on each way out.
#[test]
fn rescue_with_after_is_two_nested_tries() {
    let shape = try_shape(803, "attempt", 1);
    assert_eq!((shape.tries, shape.handlers, shape.pops), (2, 2, 2));
    assert_eq!(shape.atom_consts["after"], 2);
}

/// `else` adds no handler of its own: it is a case on the body's value inside
/// the rescue's try, after its pop.
#[test]
fn else_with_rescue_adds_a_case_after_the_pop_and_no_handler() {
    use super::super::body::{LoweredBody, LoweredStep, LoweredTail};
    let shape = try_shape(802, "main", 0);
    assert_eq!((shape.tries, shape.handlers, shape.pops), (1, 1, 1));

    let settled = Drive::fixture(802).settle();
    let body = settled.world().lowered_body(settled.function("main", 0));
    let LoweredBody::Clauses { entries, .. } = &*body;
    let protected = entries
        .iter()
        .find(|entry| {
            entry.steps.iter().any(|step| matches!(step, LoweredStep::PopHandler))
                && matches!(entry.tail, LoweredTail::Dispatch { .. })
        })
        .expect("the pop is followed by the else case in the try body");
    assert!(
        matches!(protected.steps.last(), Some(LoweredStep::PopHandler)),
        "nothing of the else case runs before the handler is popped"
    );
}

/// A `try` with only `else` protects nothing: it is a case with no handler.
#[test]
fn else_alone_is_a_case_with_no_handler() {
    let shape = try_shape(838, "main", 0);
    assert_eq!((shape.tries, shape.handlers, shape.pops), (0, 0, 0));
}
