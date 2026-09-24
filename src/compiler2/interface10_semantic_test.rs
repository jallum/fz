//! Source-boundary regressions recovered for fz-kdt.98.3.17.10.
//!
//! The discarded-call, sibling-route, and swapped-row sources come from
//! `drive_test.rs` on the preserved off-the-rails branch. The assertion's
//! intent comes from `jobs/source_equations_test.rs`; this version reaches it
//! through the ordinary compiler instead of the abandoned binding API.
//! Missing external evidence is not manufactured here: the old kernel's
//! unknown-sibling tests make a separate claim from these source witnesses.

use super::{
    CodeSubmission, Compiler2, ExecutableNeed, LoweredBody, LoweredStep, ModuleId, RootId, RootSubmission, Ty,
};
use crate::telemetry::ConfiguredTelemetry;
use std::time::Duration;

fn compile(source: &str, name: &str, arity: usize) -> (Compiler2<ConfiguredTelemetry>, RootId) {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.set_drive_timeout(Duration::from_secs(30));
    compiler.submit_code(CodeSubmission {
        name: Some(format!("interface10/{name}.fz")),
        text: source.into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity,
        need: ExecutableNeed::Value,
    });
    compiler
        .drive_root_to_dump_stage(root, super::dump::DumpStage::Backend)
        .unwrap_or_else(|error| panic!("{name} must reach the ordinary backend product: {error}"));
    (compiler, root)
}

fn assert_return(compiler: &Compiler2<ConfiguredTelemetry>, root: RootId, expected: Ty, reason: &str) {
    let world = compiler.world();
    let function = world.root_function(root);
    let returns = world
        .activation_keys()
        .into_iter()
        .filter(|key| key.root == root && key.function == function)
        .map(|key| world.activation_return(&key))
        .collect::<Vec<_>>();
    assert_eq!(
        returns,
        vec![Some(expected)],
        "{reason}; expected {}; observed {:?}",
        world.types().display(&expected),
        returns
            .iter()
            .map(|ty| ty.map(|ty| world.types().display(&ty)))
            .collect::<Vec<_>>(),
    );
}

#[test]
fn discarded_nonreturning_call_blocks_literal_suffix() {
    let (mut compiler, root) = compile(
        "def spin(), do: spin()\ndef main() do\n spin()\n :ok\nend\n",
        "discarded_nonreturning_call",
        0,
    );
    let none = compiler.world_mut().types_mut().none();
    assert_return(
        &compiler,
        root,
        none,
        "a discarded call must return before its suffix can execute",
    );
}

#[test]
fn discarded_returning_call_allows_literal_suffix() {
    let (mut compiler, root) = compile(
        "def returns(), do: :ready\ndef main() do\n returns()\n :ok\nend\n",
        "discarded_returning_call",
        0,
    );
    let ok = compiler.world_mut().types_mut().atom_lit("ok");
    assert_return(
        &compiler,
        root,
        ok,
        "the suffix supplies the return after its prerequisite completes",
    );
}

#[test]
fn nonreturning_argument_blocks_independent_callee_return() {
    let (mut compiler, root) = compile(
        "def spin(), do: spin()\ndef ignore(_value), do: :independent\ndef main(), do: ignore(spin())\n",
        "nonreturning_argument",
        0,
    );
    let none = compiler.world_mut().types_mut().none();
    assert_return(
        &compiler,
        root,
        none,
        "ignore cannot run before its nonreturning argument completes",
    );
}

fn projected_sibling_source(producer: &str) -> String {
    format!(
        "def produce(), do: {producer}\ndef main() do\n {{_sibling, selected}} = {{produce(), :ok}}\n selected\nend\n"
    )
}

fn assert_selected_field_projection(compiler: &Compiler2<ConfiguredTelemetry>, root: RootId) {
    let body = compiler.world().lowered_body(compiler.world().root_function(root));
    let LoweredBody::Clauses { entries, .. } = body.as_ref() else {
        panic!("the projection witness must lower to a source body");
    };
    assert!(
        entries
            .iter()
            .flat_map(|entry| &entry.steps)
            .any(|step| matches!(step, LoweredStep::TupleField { index: 1, .. })),
        "the witness must actually project the field beside its strict sibling",
    );
}

#[test]
fn projected_tuple_field_keeps_nonreturning_sibling_strict() {
    let (mut compiler, root) = compile(&projected_sibling_source("produce()"), "dead_tuple_sibling", 0);
    assert_selected_field_projection(&compiler, root);
    let none = compiler.world_mut().types_mut().none();
    assert_return(
        &compiler,
        root,
        none,
        "selecting :ok does not erase evaluation of its tuple sibling",
    );
}

#[test]
fn projected_tuple_field_allows_returning_sibling() {
    let (mut compiler, root) = compile(&projected_sibling_source(":ready"), "returning_tuple_sibling", 0);
    assert_selected_field_projection(&compiler, root);
    let ok = compiler.world_mut().types_mut().atom_lit("ok");
    assert_return(
        &compiler,
        root,
        ok,
        "the selected field returns when the complete tuple can be built",
    );
}

fn assert_zero_output_pin(compiler: &mut Compiler2<ConfiguredTelemetry>) {
    let same = compiler.world_mut().reference_function(ModuleId::GLOBAL, "same", 2);
    let body = compiler.world().lowered_body(same);
    let LoweredBody::Clauses { entries, .. } = body.as_ref() else {
        panic!("same/2 must have a lowered source body");
    };
    let assertion = entries
        .iter()
        .flat_map(|entry| &entry.steps)
        .find(|step| matches!(step, LoweredStep::AssertSame { .. }))
        .expect("the pin must actually reach the zero-output AssertSame operation");
    assert_eq!(
        super::body::step_defined_values(assertion).count(),
        0,
        "the execution prerequisite defines no new result value",
    );
}

#[test]
fn zero_output_pin_blocks_literal_after_disjoint_operands() {
    let (mut compiler, root) = compile(
        "def same(first, second) do\n ^first = second\n :ok\nend\ndef main(), do: same(1, :other)\n",
        "disjoint_pinned_operands",
        0,
    );
    assert_zero_output_pin(&mut compiler);
    let none = compiler.world_mut().types_mut().none();
    assert_return(
        &compiler,
        root,
        none,
        "a failed assertion blocks :ok although it defines no value",
    );
}

#[test]
fn zero_output_pin_allows_literal_after_overlapping_operands() {
    let (mut compiler, root) = compile(
        "def same(first, second) do\n ^first = second\n :ok\nend\ndef main(), do: same(1, 1)\n",
        "overlapping_pinned_operands",
        0,
    );
    assert_zero_output_pin(&mut compiler);
    let ok = compiler.world_mut().types_mut().atom_lit("ok");
    assert_return(&compiler, root, ok, "the matching pin permits the suffix");
}

#[test]
fn recursive_branch_cannot_borrow_sibling_return() {
    let (mut compiler, root) = compile(
        concat!(
            "def loop(x) do\n case x do\n",
            " :again -> {:bad, loop(x)}\n :ok -> :ok\n end\nend\n",
            "def main(x), do: loop(x)\n",
        ),
        "recursive_sibling_isolation",
        1,
    );
    let ok = compiler.world_mut().types_mut().atom_lit("ok");
    assert_return(
        &compiler,
        root,
        ok,
        "loop(:again) cannot borrow :ok to construct a finite {:bad, ...} return",
    );
}

#[test]
fn recursive_argument_swaps_preserve_whole_rows() {
    let (mut compiler, root) = compile(
        concat!(
            "def rotate(0, x, y), do: {x, y}\n",
            "def rotate(n, x, y), do: rotate(n - 1, y, x)\n",
            "def main(), do: rotate(1, 1, :tag)\n",
        ),
        "recursive_swapped_rows",
        0,
    );
    let types = compiler.world_mut().types_mut();
    let int = types.int();
    let tag = types.atom_lit("tag");
    let forward = types.tuple(&[int, tag]);
    let reverse = types.tuple(&[tag, int]);
    let expected = types.union(forward, reverse);
    assert_return(
        &compiler,
        root,
        expected,
        "integer abstraction permits either parity, never crossed columns",
    );
}

#[test]
fn nine_correlated_call_rows_do_not_invent_cross_pairs() {
    // Nine exceeds ActivationInputAlternatives' inherited budget of eight.
    // The source contract is independent of how many inference owners a
    // replacement uses: every admitted pair lies on the diagonal.
    let labels = ["a", "b", "c", "d", "e", "f", "g", "h", "i"];
    let arms = labels
        .iter()
        .map(|label| format!(" {{:{label}, :{label}}} -> :ok\n"))
        .collect::<String>();
    let calls = labels
        .iter()
        .map(|label| format!("same_row(:{label}, :{label})"))
        .collect::<Vec<_>>()
        .join(", ");
    let source = format!(
        "def same_row(x, y) do\n case {{x, y}} do\n{arms} _ -> :crossed\n end\nend\ndef main(), do: {{{calls}}}\n"
    );
    let (mut compiler, root) = compile(&source, "nine_correlated_rows", 0);
    let types = compiler.world_mut().types_mut();
    let ok = types.atom_lit("ok");
    let expected = types.tuple(&[ok; 9]);
    assert_return(
        &compiler,
        root,
        expected,
        "more than eight rows cannot make an uncalled off-diagonal pair reachable",
    );
}

const PARSER: &str = concat!(
    "defp val([:t | r]), do: {:ok, r}\n",
    "defp val([:open | r]), do: array(r)\n",
    "defp array([:close | _r]), do: :done\n",
    "defp array(b), do: item(val(b))\n",
    "defp item({:ok, r}), do: array(r)\n",
    "def main(), do: val([:open, :t, :close])\n",
);

fn assert_parser_return(compiler: &mut Compiler2<ConfiguredTelemetry>, root: RootId) {
    // The uniform token-list abstraction also admits val's :t branch; the
    // exact runtime :done result is not an exact static return-type claim.
    let types = compiler.world_mut().types_mut();
    let done = types.atom_lit("done");
    let ok = types.atom_lit("ok");
    let open = types.atom_lit("open");
    let token = types.atom_lit("t");
    let close = types.atom_lit("close");
    let tokens = types.union(open, token);
    let tokens = types.union(tokens, close);
    let tail = types.list(tokens);
    let accepted = types.tuple(&[ok, tail]);
    let allowed = types.union(done, accepted);
    let world = compiler.world();
    let main = world.root_function(root);
    let keys = world
        .activation_keys()
        .into_iter()
        .filter(|key| key.root == root && key.function == main)
        .collect::<Vec<_>>();
    assert_eq!(keys.len(), 1, "the single root has a return to inspect");
    let observed = world
        .activation_return(&keys[0])
        .expect("the parser root return must settle");
    assert!(
        world.types().is_subtype(&done, &observed),
        "the recursive-result route must contribute :done, observed {}",
        world.types().display(&observed),
    );
    assert!(
        world.types().is_subtype(&observed, &allowed),
        "only :done or the :t branch's {{:ok, token_tail}} can return, observed {}",
        world.types().display(&observed),
    );
}

#[test]
fn parser_dispatch_on_recursive_result_settles() {
    // Exact source: diagnosis10-evidence/decode-reduce-14-minimal-shapes.fz.
    let (mut compiler, root) = compile(PARSER, "parser_recursive_result", 0);
    assert_parser_return(&mut compiler, root);
}

#[test]
fn parser_direct_discriminator_control_settles() {
    // The handoff's control replaces only array's fallback call operand.
    let source = PARSER.replace(
        "defp array(b), do: item(val(b))",
        "defp array(_b), do: item({:ok, [:close]})",
    );
    let (mut compiler, root) = compile(&source, "parser_direct_discriminator", 0);
    assert_parser_return(&mut compiler, root);
}

fn replacement_source(left: &str, right: &str) -> String {
    format!(
        "def shared(), do: 7\ndef replacement(), do: 11\ndef left() do\n f = &{left}/0\n f.()\nend\ndef right() do\n f = &{right}/0\n f.()\nend\ndef main(), do: left() + right()\n"
    )
}

#[test]
fn replacing_one_callable_target_preserves_another_consumers_claim() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    let name = "interface10/target_replacement.fz";
    compiler.submit_code(CodeSubmission {
        name: Some(name.into()),
        text: replacement_source("shared", "shared"),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(14));
    let shared = compiler.world_mut().reference_function(ModuleId::GLOBAL, "shared", 0);
    let replacement = compiler
        .world_mut()
        .reference_function(ModuleId::GLOBAL, "replacement", 0);

    compiler.submit_code(CodeSubmission {
        name: Some(name.into()),
        text: replacement_source("replacement", "shared"),
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(18),
        "left must use its new callback while right retains shared"
    );
    let program = compiler.retained_backend_program(root);
    assert!(
        program
            .executables()
            .iter()
            .any(|body| body.key.activation.function == shared)
    );
    assert!(
        program
            .executables()
            .iter()
            .any(|body| body.key.activation.function == replacement)
    );

    compiler.submit_code(CodeSubmission {
        name: Some(name.into()),
        text: replacement_source("replacement", "replacement"),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(22));
    assert!(
        compiler
            .retained_backend_program(root)
            .executables()
            .iter()
            .all(|body| body.key.activation.function != shared),
        "the old target leaves only after its final consumer changes",
    );
}
