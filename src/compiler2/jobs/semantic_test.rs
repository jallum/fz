use super::*;
use crate::compiler2::drive::ExecutionContext;
use crate::compiler2::{DriveOutcome, ExecutableNeed};
use crate::telemetry::ConfiguredTelemetry;

#[test]
fn analyze_activation_preserves_real_rows_without_publishing_their_cartesian_blend() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("correlated_callee_contributions.fz".to_string()),
        r#"
def sink(n, a, b), do: if n == 0, do: 0, else: sink(n - 1, a, b)
def relay(n, a, b), do: if n == 0, do: sink(n, a, b), else: relay(n - 1, a, b)
def main(), do: {relay(0, [1], [:left]), relay(0, [:right], [2])}
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));

    let int = world.types_mut().int();
    let left = world.types_mut().atom_lit("left");
    let right = world.types_mut().atom_lit("right");
    let ints = world.types_mut().non_empty_list(int);
    let lefts = world.types_mut().non_empty_list(left);
    let rights = world.types_mut().non_empty_list(right);
    let rows = [vec![int, ints, lefts], vec![int, rights, ints]];
    let relay = world.reference_function(ModuleId::GLOBAL, "relay", 3);
    let sink = world.reference_function(ModuleId::GLOBAL, "sink", 3);
    let relay_activation = world.activation_key(root, relay, &rows[0]);
    let sink_activation = world.activation_key(root, sink, &rows[0]);
    assert_eq!(relay_activation, world.activation_key(root, relay, &rows[1]));
    assert_eq!(sink_activation, world.activation_key(root, sink, &rows[1]));

    let effects = analyze_activation(&mut world, &tel, &relay_activation)
        .expect("the real relay analysis should conclude with both correlated rows");
    let sink_rows = effects
        .activation_input_contributions
        .iter()
        .filter(|(key, _)| key == &sink_activation)
        .map(|(_, inputs)| inputs.clone())
        .collect::<Vec<_>>();
    assert_eq!(
        sink_rows.len(),
        rows.len(),
        "a shared callee key must receive only the two walked rows, never their column-wise blend: {sink_rows:?}"
    );
    for row in &rows {
        assert!(sink_rows.contains(row), "every real caller row must survive coalescing");
    }
    world.complete_job(Job::AnalyzeActivation(relay_activation), effects);
    let published = world
        .activation_input_alternatives(&sink_activation)
        .expect("the conclusion should publish the callee's real evidence");
    assert_eq!(published.rows().len(), rows.len());
    for row in &rows {
        assert!(published.rows().iter().any(|published| published.columns() == row));
    }
}

#[test]
fn analyze_activation_emits_each_exact_callee_input_once_per_publisher() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("activation_contribution_owners.fz".to_string()),
        r#"
def sink(value), do: if value == :recur, do: sink(value), else: 0
def other(_value), do: 0

def first() do
  sink([1])
  sink([1])
  other([1])
  sink([:ok])
end

def second(), do: sink([1])

def main() do
  first()
  second()
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(
        matches!(ExecutionContext::new(&mut world, &tel).drive(), DriveOutcome::Resolved),
        "the production semantic pipeline should settle the ownership fixture",
    );

    let int = world.types_mut().int();
    let atom = world.types_mut().atom_lit("ok");
    let int_list = world.types_mut().non_empty_list(int);
    let atom_list = world.types_mut().non_empty_list(atom);
    let first = world.reference_function(ModuleId::GLOBAL, "first", 0);
    let second = world.reference_function(ModuleId::GLOBAL, "second", 0);
    let sink = world.reference_function(ModuleId::GLOBAL, "sink", 1);
    let other = world.reference_function(ModuleId::GLOBAL, "other", 1);
    let first_activation = world.activation_key(root, first, &[]);
    let second_activation = world.activation_key(root, second, &[]);
    let sink_activation = world.activation_key(root, sink, &[int_list]);
    let other_activation = world.activation_key(root, other, &[int_list]);
    // `sink` forwards its argument into `==`, which asks whether an operand
    // is a number, so the two element types stay apart in `sink`'s key.
    let sink_atom_activation = world.activation_key(root, sink, &[atom_list]);

    let first_effects = analyze_activation(&mut world, &tel, &first_activation)
        .expect("the actual AnalyzeActivation job should conclude");
    assert_eq!(
        first_effects.activation_input_contributions,
        vec![
            (sink_activation.clone(), vec![int_list]),
            (other_activation, vec![int_list]),
            (sink_atom_activation, vec![atom_list]),
        ],
        "the emission boundary should remove only the repeated key+row and preserve first-observed order",
    );

    let first_job = Job::AnalyzeActivation(first_activation.clone());
    let second_job = Job::AnalyzeActivation(second_activation.clone());
    world.complete_job(first_job.clone(), first_effects);
    let LoweredBody::Clauses {
        clauses,
        entries,
        generated,
        ..
    } = (*world.lowered_body(first)).clone()
    else {
        panic!("the source fixture should lower first/0 to clauses");
    };
    let withdrawn = entries
        .into_iter()
        .map(|entry| LoweredEntry {
            steps: Vec::new(),
            tail: LoweredTail::Halt {
                atom: "withdrawn".to_string(),
            },
            ..entry
        })
        .collect();
    let replacement = LoweredBody::clauses(clauses, withdrawn, generated);
    assert!(world.define_lowered_body(first, replacement));
    world.complete_job(
        Job::LowerFunction(first),
        JobEffects {
            outputs: vec![FactKey::LoweredBody(first)],
            changed: vec![FactKey::LoweredBody(first)],
            ..JobEffects::default()
        },
    );
    assert!(
        world.work_graph.rebased(&first_job),
        "a shifted body should rebase its AnalyzeActivation publisher",
    );
    let withdrawn_effects = analyze_activation(&mut world, &tel, &first_activation)
        .expect("the rebased AnalyzeActivation job should conclude from its replacement body");
    assert!(
        withdrawn_effects.activation_input_contributions.is_empty(),
        "the replacement body reaches no callee contributions",
    );
    world.complete_job(first_job.clone(), withdrawn_effects);

    let second_effects = analyze_activation(&mut world, &tel, &second_activation)
        .expect("the second actual AnalyzeActivation job should conclude after the first rebases");
    assert_eq!(
        second_effects.activation_input_contributions,
        vec![(sink_activation.clone(), vec![int_list])],
        "another AnalyzeActivation publisher must retain ownership of the same exact contribution",
    );
    world.complete_job(second_job.clone(), second_effects);

    let shared_activation = FactKey::Activation(sink_activation.clone());
    let shared_inputs = FactKey::ActivationInputs(sink_activation);
    assert!(
        !world.job_outputs(&first_job).contains(&shared_activation)
            && world.job_outputs(&second_job).contains(&shared_activation)
            && world.job_outputs(&second_job).contains(&shared_inputs),
        "with the rebased publisher withdrawn, the second publisher should independently keep the shared activation and its input contribution",
    );
    assert!(world.has_fact(&shared_activation) && world.has_fact(&shared_inputs));
}

/// The three answers a closure callee can give, and why they are three and
/// not two.
///
/// A call is dead when nothing can arrive in its callee slot. The empty type
/// has no members; a bare type variable has no runtime representation, so an
/// activation keyed with one there is a specialization for an argument no
/// caller can ever supply. Both are *evidence* — the call never happens, so
/// its result is the empty type.
///
/// A callable that merely carries a variable is the third answer and must
/// stay distinct: `(int) -> a` is a perfectly representable value whose
/// analysis is simply pending. Widening the death test to "has variables"
/// would declare live calls dead. Widening it the other way — back to `any`
/// — is the fz-f98.17 defect (fz-f98.18).
#[test]
fn only_an_uninhabitable_callee_makes_a_call_dead() {
    let mut types = Types::new();
    let never = types.none();
    let int = types.int();
    let alpha = types.param_alpha(0);
    let carries_a_var = types.arrow(&[int], alpha);

    assert!(
        callee_has_no_inhabitants(&types, never),
        "no value inhabits the empty type, so the call never happens",
    );
    assert!(
        callee_has_no_inhabitants(&types, alpha),
        "a bare type variable has no runtime representation, so nothing can be passed in that slot",
    );
    assert!(
        !callee_has_no_inhabitants(&types, carries_a_var),
        "a callable carrying an un-instantiated result is still a real pointer: absence of \
             analysis, not absence of values",
    );
}
