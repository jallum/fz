use super::*;
use crate::compiler2::drive::ExecutionContext;
use crate::compiler2::dump::DumpStage;
use crate::compiler2::types::TypeVarId;
use crate::compiler2::{CodeSubmission, Compiler2, ExecutableKey, ExecutableNeed, RootSubmission};
use crate::dispatch_matrix::pattern::PatternDispatchPlan;
use crate::fast_hash::HashSet;
use crate::telemetry::ConfiguredTelemetry;
use fz_engine::DriveOutcome;
use std::cell::RefCell;
use std::rc::Rc;

/// Every `Job::AnalyzeActivation` span started during a drive, recorded
/// through the same production telemetry the scheduler itself emits.
struct JobStarts(Rc<RefCell<Vec<Job>>>);

impl JobStarts {
    fn install(tel: &ConfiguredTelemetry) -> Self {
        let starts = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&starts);
        tel.attach_raw_span1_0::<Job, _, _, _>(
            &["fz", "compiler2", "job"],
            move |_, _, _, job| sink.borrow_mut().push(job.clone()),
            |_, _, _, _| {},
            |_, _, _, _| {},
        );
        Self(starts)
    }

    /// How many times any activation of `function` was analysed. A
    /// zero-arity function has exactly one activation, so counting by
    /// function identity here is the same as counting by activation key.
    fn count_function(&self, function: FunctionId) -> usize {
        self.0
            .borrow()
            .iter()
            .filter(|job| matches!(job, Job::AnalyzeActivation(key) if key.function == function))
            .count()
    }

    /// Every activation of `function` this drive ever started analysing,
    /// found by job identity rather than by guessing the function's
    /// argument types.
    fn activations(&self, function: FunctionId) -> HashSet<ActivationKey> {
        self.0
            .borrow()
            .iter()
            .filter_map(|job| match job {
                Job::AnalyzeActivation(key) if key.function == function => Some(key.clone()),
                _ => None,
            })
            .collect()
    }
}

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
    } = (*world.lowered_body(first)).clone();

    let withdrawn = entries
        .into_iter()
        .map(|entry| LoweredEntry {
            steps: Vec::new(),
            tail: LoweredTail::Unreachable,
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

/// `LoweredStep::FieldAccess` asks the shared field lookup for `.value` on a
/// resource the same way it asks for any map field. The lookup must answer
/// the resource's payload type rather than falling back to `any`.
#[test]
fn field_access_on_a_resource_types_as_its_payload() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("resource_value_field_access.fz".to_string()),
        r#"
extern "C" defp opaque_handle() :: resource(c_pointer)

def main() do
  r = opaque_handle()
  r.value
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));

    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let main_activation = world.activation_key(root, main, &[]);
    let c_pointer = world.types_mut().c_pointer();
    assert_eq!(
        world.activation_return_evidence(&main_activation),
        Some(c_pointer),
        "opaque_handle() is resource(c_pointer), so r.value should type as c_pointer, not any",
    );
}

/// `Enumerable.slice(map)` returns `{:ok, n, slicer}` where `slicer` is an
/// uncalled closure: its surface still carries a free variable for its
/// argument and its result. `@spec slice(t(a)) :: {:ok, integer, any} | ...`
/// bounds the third field with `any`, so this is the shape
/// `observed_is_unconstrained`'s dead `has_vars(observed)` disjunct used to
/// see. The disjunct is gone; the calculator alone must still read the
/// closure through, rather than collapsing it to `any`.
#[test]
fn refine_observed_return_keeps_a_var_carrying_closure_out_of_a_protocol_return() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("map_enumerable_slice.fz".to_string()),
        r#"
def main() do
  map = %{1 => :one, 2 => :two}
  Enumerable.slice(map)
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));

    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let main_activation = world.activation_key(root, main, &[]);
    let returned = world
        .activation_return_evidence(&main_activation)
        .expect("main should settle to a return type");

    let tag = world.types_mut().tuple_field_type(&returned, 0);
    let count = world.types_mut().tuple_field_type(&returned, 1);
    let slicer = world.types_mut().tuple_field_type(&returned, 2);
    let ok = world.types_mut().atom_lit("ok");
    let int = world.types_mut().int();
    let any = world.types_mut().any();

    assert!(
        world.types().is_equivalent(&tag, &ok),
        "the tuple's first field should still tag the result :ok",
    );
    assert!(
        world.types().is_equivalent(&count, &int),
        "the tuple's second field should still type as the map's entry count",
    );
    assert!(
        world.types().has_vars(&slicer),
        "the slicer closure is never called here, so its surface still carries a free variable",
    );
    assert!(
        !world.types().is_equivalent(&slicer, &any),
        "the calculator should read the var-carrying closure through, not widen it to any",
    );
}

/// `main/0` reads each callee's return once it concludes rather than on
/// every revision, so reaching every call site, reading the concluded
/// returns, and publishing the join costs exactly three analyses however
/// many independent callees it has.
#[test]
fn independent_literal_callees_settle_main_in_three_analyses() {
    for callee_count in [2usize, 4, 8] {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new();
        let mut source = String::new();
        for i in 0..callee_count {
            source.push_str(&format!("def callee_{i}(), do: {i}\n"));
        }
        source.push_str("def main() do\n");
        for i in 0..callee_count {
            source.push_str(&format!("  callee_{i}()\n"));
        }
        source.push_str("  :done\nend\n");
        world.submit_code(Some(format!("independent_{callee_count}.fz")), source);
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let starts = JobStarts::install(&tel);

        assert!(
            matches!(ExecutionContext::new(&mut world, &tel).drive(), DriveOutcome::Resolved),
            "{callee_count} independent callees should settle",
        );
        let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
        let main_activation = world.activation_key(root, main, &[]);
        let done = world.types_mut().atom_lit("done");
        assert_eq!(world.activation_return_evidence(&main_activation), Some(done));
        assert_eq!(
            starts.count_function(main),
            3,
            "{callee_count} independent callees must still cost main/0 exactly three analyses",
        );
    }
}

/// `a/1`'s return climbs through many revisions as it recurses, but
/// `main/0` waits for it to conclude and reads it exactly once, so
/// main/0's analysis count stays at three regardless of how many
/// revisions a/1's return takes to settle.
#[test]
fn recursive_callee_still_settles_main_in_three_analyses() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("recursive_callee_return.fz".to_string()),
        r#"
def a(0), do: :end
def a(n), do: {n, a(n - 1)}
def main() do
  a(3)
  :done
end
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let starts = JobStarts::install(&tel);

    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));
    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let main_activation = world.activation_key(root, main, &[]);
    let done = world.types_mut().atom_lit("done");
    assert_eq!(world.activation_return_evidence(&main_activation), Some(done));
    assert_eq!(
        starts.count_function(main),
        3,
        "a/1's climb must not re-run main/0 once for every one of its revisions",
    );
}

/// `spin/1` only ever calls itself, so its return is a bottom that never
/// rises, and nothing can ever arrive at the call that follows it. `g/1`
/// sequences a call to `spin/1` and then one to `h/0`, so h/0 can never
/// run and the compiled program must carry no executable for it.
#[test]
fn a_call_that_never_returns_strands_the_call_that_follows_it() {
    let mut compiler = Compiler2::new(ConfiguredTelemetry::new());
    compiler.submit_code(CodeSubmission {
        name: Some("call_that_never_returns.fz".to_string()),
        text: r#"
def spin(x), do: spin(x)
def h(), do: :reached
def g(x) do
  spin(x)
  h()
end
def main(), do: g(0)
"#
        .to_string(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    let (program, _) = compiler
        .drive_root_to_dump_stage(root, DumpStage::Backend)
        .unwrap_or_else(|error| panic!("the backend product should settle: {error}"));

    let h = compiler.world_mut().reference_function(ModuleId::GLOBAL, "h", 0);
    assert!(
        !program
            .executables()
            .iter()
            .any(|executable| executable.key.activation.function == h),
        "a call that follows a call that never returns can never run, so h/0 must not reach the backend",
    );
}

/// `ping/1` and `pong/1` hand off to each other on every non-base call, so
/// each reads the other's return as a partner — its current value, not a
/// one-time concluded read. The fixpoint this reaches is small (`:done`
/// however many hand-offs it takes), and reaching it at all is the point:
/// a partner cycle must still settle, not stall as a standing wait on
/// itself.
#[test]
fn mutual_recursion_still_climbs_as_partners() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("ping_pong_partners.fz".to_string()),
        r#"
def ping(n), do: if n == 0, do: :done, else: pong(n - 1)
def pong(n), do: if n == 0, do: :done, else: ping(n - 1)
def main(), do: ping(5)
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(
        matches!(ExecutionContext::new(&mut world, &tel).drive(), DriveOutcome::Resolved),
        "two functions reading each other's return as partners must still reach a fixpoint",
    );

    let main = world.reference_function(ModuleId::GLOBAL, "main", 0);
    let main_activation = world.activation_key(root, main, &[]);
    let done = world.types_mut().atom_lit("done");
    assert_eq!(
        world.activation_return_evidence(&main_activation),
        Some(done),
        "ping and pong only ever hand off to :done, however many times they call each other",
    );
}

/// `val/1`'s first clause calls `arr/2`, whose call back into `val/1` has
/// not settled the first time around, so an unknown absorbs the return:
/// val/1 must publish nothing while any of its call sites still waits,
/// never the answer from its other, already-settled clauses.
#[test]
fn a_return_is_never_published_from_a_subset_of_call_sites_while_others_wait() {
    let tel = ConfiguredTelemetry::new();
    let mut world = World::new();
    world.submit_code(
        Some("s3.fz".to_string()),
        r#"
def val(<<"[", r :: binary>>), do: arr(r, [])
def val(<<"{", r :: binary>>), do: {:ok, Map.put(%{}, "k", 1), r}
def val(<<"t", r :: binary>>), do: {:ok, true, r}
def val(b), do: {:error, b}
def arr(<<"]", r :: binary>>, acc), do: {:ok, acc, r}
def arr(b, acc), do: item(val(b), acc)
def item({:ok, v, r}, acc), do: arr(r, [v | acc])
def item(other, _acc), do: other
def main() do
  dbg(val("[t,[t]]"))
end
"#
        .to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    let starts = JobStarts::install(&tel);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));

    let val = world.reference_function(ModuleId::GLOBAL, "val", 1);
    let val_activations = starts.activations(val);
    assert!(
        !val_activations.is_empty(),
        "val/1 should have been analysed at least once"
    );
    for activation in val_activations {
        assert_eq!(
            world.fact_revision(&FactKey::ReturnType(activation)),
            Some(3),
            "val/1 publishes its return at its measured revisions -- the typed map union is \
             climbed to its fixed point -- never from a subset of its clauses while arr/2's \
             call back into it is still pending",
        );
    }
}

/// The plan each `case` an activation reached is left with, beside the plan it
/// started as: how many questions it still asks, whether it can still miss,
/// and whether it is the shared plan itself.
fn case_plans(world: &mut World, starts: &JobStarts, name: &str, arity: usize) -> Vec<(usize, bool, bool)> {
    let function = world.reference_function(ModuleId::GLOBAL, name, arity);
    let lowered = world.lowered_body(function);
    let LoweredBody::Clauses { entries, .. } = &*lowered;
    let mut plans = Vec::new();
    for activation in starts.activations(function) {
        let analysis = world
            .activation_analysis(&activation)
            .unwrap_or_else(|| panic!("{name}/{arity} should have a settled analysis"));
        for (entry, trimmed) in &analysis.trimmed.cases {
            let LoweredTail::Dispatch { dispatch, .. } = &entries[entry.as_u32() as usize].tail else {
                panic!("a trimmed case plan names a dispatch entry");
            };
            plans.push((
                trimmed.graph.test_count(),
                trimmed.can_fail(),
                Rc::ptr_eq(trimmed, &dispatch.plan),
            ));
        }
    }
    plans
}

fn driven_cases(source: &str) -> (World, JobStarts) {
    let tel = ConfiguredTelemetry::new();
    let starts = JobStarts::install(&tel);
    let mut world = World::new();
    world.submit_code(Some("trimmed_plans.fz".to_string()), source.to_string());
    world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));
    (world, starts)
}

/// `and`, `or` and `not` lower to a `case` on a boolean, and the hand-written
/// exhaustive `case` is the same shape. A boolean-typed subject leaves one
/// question for runtime -- is it `true` -- and answers the other, so the plan
/// it runs asks one question and cannot fail. A subject that might be anything
/// keeps the plan it was given.
#[test]
fn a_boolean_subject_leaves_one_question_and_no_miss() {
    let (mut world, starts) = driven_cases(
        r#"
def either(a), do: a == 1 or a == 2
def both(a), do: a == 1 and a == 2
def negated(a), do: not (a == 1)
def exhaustive(a) do
  case a == 1 do
    true -> false
    false -> true
  end
end
def undecided(a) do
  case a do
    true -> 1
    false -> 2
  end
end
def main() do
  {either(Enum.at([1, 2], 0)), both(Enum.at([1, 2], 0)), negated(Enum.at([1, 2], 0)),
   exhaustive(Enum.at([1, 2], 0)), undecided(receive do m -> m end)}
end
"#,
    );
    for name in ["either", "both", "negated", "exhaustive"] {
        assert_eq!(
            case_plans(&mut world, &starts, name, 1),
            [(1, false, false)],
            "{name}/1: of a boolean's two tests `equal(true)` is still asked and `equal(false)` is answered, \
             so the plan it runs cannot miss"
        );
    }
    assert_eq!(
        case_plans(&mut world, &starts, "undecided", 1),
        [(2, true, true)],
        "a subject that might be anything keeps both tests and its miss, as the very plan it was lowered to"
    );
}

/// The entry plan an activation runs, with the questions it still asks
/// listed root first, and whether it can still end with no clause.
fn entry_plan_of(world: &mut World, starts: &JobStarts, name: &str, arity: usize) -> Rc<PatternDispatchPlan<Ty>> {
    let function = world.reference_function(ModuleId::GLOBAL, name, arity);
    let activations = starts.activations(function);
    assert_eq!(activations.len(), 1, "{name}/{arity} is analysed at one activation");
    let activation = activations.into_iter().next().expect("one activation");
    world
        .activation_analysis(&activation)
        .unwrap_or_else(|| panic!("{name}/{arity} should have a settled analysis"))
        .trimmed
        .entry
        .clone()
        .expect("a function with a body has an entry plan")
}

/// A tuple parameter whose second field is told apart by `false` and `true`
/// is three questions: is it a pair, is the field `false`, is it `true`. A
/// caller that passes a pair whose second field is a boolean answers the first
/// and last, and the clause selection is left asking `false` alone, with
/// nothing to fall to.
#[test]
fn a_function_clause_plan_keeps_only_the_questions_its_inputs_leave() {
    use crate::dispatch_matrix::{ComparisonValue, DispatchNode, Region};

    let (mut world, starts) = driven_cases(
        r#"
def unwrap({v, false}), do: v
def unwrap({v, true}), do: v + 1
def main(), do: unwrap({length([1, 2]), Enum.at([1, 2], 0) == 1})
"#,
    );
    let plan = entry_plan_of(&mut world, &starts, "unwrap", 1);

    assert_eq!(plan.graph.test_count(), 1, "only the field's `false` remains to ask");
    assert!(
        !plan.can_fail(),
        "a boolean field is `false` or `true`: no clause is missed"
    );
    let Some(DispatchNode::Test {
        predicate,
        on_match,
        on_miss,
    }) = plan.graph.node(plan.graph.root)
    else {
        panic!("the root is the one question left");
    };
    assert!(
        matches!(&predicate.region, Region::Equal(ComparisonValue::Const(value)) if *value == crate::ground_value::GroundValue::Bool(false)),
        "the question left is whether the field is `false`: {:?}",
        predicate.region
    );
    let outcome = |node| match plan.graph.node(node) {
        Some(DispatchNode::Outcome { outcome, .. }) => outcome.0,
        other => panic!("a kept child is a clause: {other:?}"),
    };
    assert_eq!(
        (outcome(on_match.target), outcome(on_miss.target)),
        (0, 1),
        "`false` selects the first clause and anything else the second"
    );
}

/// `[]` and `[h | t]` are two questions about one list. A list known to have
/// an element answers both, so no question is left and the clause is chosen
/// by the call alone.
#[test]
fn a_list_known_to_have_a_head_selects_its_clause_without_asking() {
    let (mut world, starts) = driven_cases(
        r#"
def first([]), do: 0
def first([h | _]), do: h
def main(), do: first([Enum.at([1, 2], 0)])
"#,
    );
    let plan = entry_plan_of(&mut world, &starts, "first", 1);

    assert!(
        plan.is_direct_outcome(),
        "a non-empty list needs no question to find its clause"
    );
    assert!(!plan.can_fail());
}

const SPEC_NARROWS_NOTHING: &str = r#"
@spec f(integer) :: integer
@spec f(float) :: integer
def f(x :: integer), do: x + 1
def f(x :: float), do: 0
"#;

/// The one activation of `f/1` the program reached, as its input types.
fn only_activation_inputs(world: &mut World, starts: &JobStarts) -> Vec<Ty> {
    let function = world.reference_function(ModuleId::GLOBAL, "f", 1);
    let activations = starts.activations(function);
    assert_eq!(activations.len(), 1, "f/1 is analysed at one activation");
    let activation = activations.into_iter().next().expect("one activation");
    activation.inputs(world.types()).to_vec()
}

/// A spec describes what a callee accepts; it does not tell the callee what
/// its caller holds. A caller that holds `any` keys the callee under `any`,
/// so the callee keeps the arm of last resort that a value outside the spec
/// reaches.
#[test]
fn a_spec_does_not_narrow_the_any_a_caller_holds_into_its_callees_key() {
    let (mut world, starts) = driven_cases(&format!(
        "{SPEC_NARROWS_NOTHING}\ndef main(), do: f(receive do m -> m end)\n"
    ));
    let any = world.types_mut().any();
    let inputs = only_activation_inputs(&mut world, &starts);
    assert!(
        inputs.len() == 1 && world.types().is_equivalent(&inputs[0], &any),
        "f/1 is keyed on what the caller holds (any), not on the spec's domain: {inputs:?}"
    );
    let plan = entry_plan_of(&mut world, &starts, "f", 1);
    assert!(plan.can_fail(), "a callee keyed on any keeps its arm of last resort");
}

/// The arm of last resort is still trimmed where the caller's own types prove
/// no clause is missed: the spec changed nothing for a caller that knows what
/// it holds.
#[test]
fn a_caller_that_knows_its_argument_still_trims_the_callees_arm_of_last_resort() {
    let (mut world, starts) = driven_cases(&format!("{SPEC_NARROWS_NOTHING}\ndef main(), do: f(length([1, 2]))\n"));
    let int = world.types_mut().int();
    let inputs = only_activation_inputs(&mut world, &starts);
    assert!(
        inputs.len() == 1 && world.types().is_equivalent(&inputs[0], &int),
        "f/1 is keyed on the integer the caller holds: {inputs:?}"
    );
    let plan = entry_plan_of(&mut world, &starts, "f", 1);
    assert!(!plan.can_fail(), "an integer argument cannot miss a clause");
}

/// A list whose elements are closures is a runtime shape. The closure arrow
/// variables belong to each closure, so a contract whose parameter is
/// `list(a)` has nothing to refine the column with, and the observed list
/// keeps its elements. Meeting the closure with the spec variable `a` is the
/// empty type, which is what once collapsed the column to the empty list.
#[test]
fn instantiate_open_inputs_keeps_a_list_of_closures() {
    let mut world = World::new();
    let closure = world.types_mut().closure_lit(ClosureTarget(7), vec![], 1);
    let observed = world.types_mut().list(closure);
    let spec_var = world.types_mut().type_var(TypeVarId(0));
    let surface = world.types_mut().list(spec_var);

    let refined = instantiate_open_inputs(&mut world, vec![observed], [[surface].as_slice()].into_iter());

    assert_eq!(refined, vec![observed]);
}

/// A callable column is the one open column a contract refines: the lambda
/// passed to `make_resource(42, fn x -> ... end)` takes its parameter type from
/// the contract's arrow.
#[test]
fn instantiate_open_inputs_refines_a_callable_column_by_the_contract_arrow() {
    let mut world = World::new();
    let int = world.types_mut().int();
    let nil = world.types_mut().nil();
    let closure = world.types_mut().closure_lit(ClosureTarget(7), vec![], 1);
    let surface = world.types_mut().arrow(&[int], nil);

    let refined = instantiate_open_inputs(&mut world, vec![closure], [[surface].as_slice()].into_iter());

    assert_ne!(
        refined,
        vec![closure],
        "the callable column takes the contract's parameter types"
    );
    let clause = world
        .types_mut()
        .callable_clauses(&refined[0])
        .expect("a refined callable column is still callable")
        .remove(0);
    assert!(world.types().is_integer(&clause.args[0]));
}

/// A protocol call whose receiver is `any` could reach any implementation, so
/// the callsite waits on every overlapping implementation's definition before
/// it resolves, including when an arm it already matches (the stream's) is
/// defined. A `Map.put` result is typed `any` by its spec, and reducing it
/// through a stream must still compile the `Map` implementation the runtime
/// value needs.
#[test]
fn an_any_receiver_waits_on_every_overlapping_impl_provider_even_when_an_arm_matches() {
    use crate::compiler2::drive::DependencyKey;
    use crate::compiler2::world::JobCompletion;
    use crate::modules::identity::ModuleName;

    let tel = ConfiguredTelemetry::new();
    let awaited: Rc<RefCell<HashSet<ModuleId>>> = Rc::default();
    let observed = Rc::clone(&awaited);
    tel.attach_raw_event2::<World, JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _world, completion| {
            if !matches!(completion.job, Job::AnalyzeActivation(_)) {
                return;
            }
            for blocked in &completion.step.blocked {
                if let DependencyKey::Fact(FactKey::ModuleDefined(module)) = blocked.fact() {
                    observed.borrow_mut().insert(*module);
                }
            }
        },
    );

    let mut world = World::new();
    world.submit_code(
        Some("wide_receiver.fz".to_string()),
        "def main(), do: Enum.to_list(Stream.map(Map.put(%{}, 1, 1), &(&1)))\n".to_string(),
    );
    world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));

    let enumerable = world.reference_module(ModuleName::parse_dotted("Enumerable").unwrap());
    let providers = world.protocol_impl_providers(enumerable);
    let awaited = awaited.borrow();
    for target_name in ["Map", "List", "Range"] {
        let provider = providers
            .iter()
            .find(|(target, _)| {
                world
                    .module_name(*target)
                    .is_some_and(|name| name.to_string() == target_name)
            })
            .unwrap_or_else(|| panic!("Enumerable has a provider for {target_name}"))
            .1;
        assert!(
            awaited.contains(&provider),
            "the callsite never waited on the Enumerable.{target_name} implementation's definition"
        );
    }
}

/// The values a protocol call's receiver allows beyond its implementations are
/// what it raises for: none for a receiver the implementations cover, some for
/// one they do not.
#[test]
fn a_receiver_reaches_beyond_the_implementations_only_where_they_leave_values_over() {
    let mut types = Types::new();
    let (int, float, any) = (types.int(), types.float(), types.any());
    let int_or_float = types.union(int, float);

    assert!(
        !reaches_beyond(&mut types, int, int),
        "an exact implementation covers it"
    );
    assert!(
        !reaches_beyond(&mut types, int, int_or_float),
        "a wider implementation covers it"
    );
    assert!(!reaches_beyond(&mut types, int_or_float, int_or_float));
    assert!(reaches_beyond(&mut types, int_or_float, int), "floats are left over");
    assert!(
        reaches_beyond(&mut types, any, int_or_float),
        "anything else is left over"
    );
}

fn executables_of(
    settled: &mut crate::compiler2::drive_harness::Settled,
    name: &str,
    arity: u64,
) -> Vec<ExecutableKey> {
    let function = settled.function(name, arity);
    let root = settled.root();
    settled
        .compiler_mut()
        .product_executable_inventory(root)
        .expect("the program settles")
        .into_iter()
        .filter(|executable| executable.activation.function == function)
        .collect()
}

#[test]
fn a_cycle_is_compiled_as_one_activation_per_member_and_the_non_entry_member_names_its_entry() {
    let mut settled = crate::compiler2::drive_harness::Drive::fixture(1350).settle();
    let entry = settled.function("cont", 3);

    let cont = executables_of(&mut settled, "cont", 3);
    let step = executables_of(&mut settled, "step", 3);

    assert_eq!(
        cont.len(),
        1,
        "the entry's calls back into it stay on its own key: {cont:?}"
    );
    assert_eq!(
        cont[0].activation.entry, None,
        "an entry activation is not entered by another"
    );
    assert_eq!(step.len(), 1, "the member the entry calls is one activation: {step:?}");
    assert_eq!(
        step[0].activation.entry.map(|(function, _)| function),
        Some(entry),
        "the member the entry calls carries the activation that entered the cycle"
    );
    assert_eq!(
        step[0].activation.entry.map(|(_, arrow)| arrow),
        Some(cont[0].activation.arrow)
    );
}

#[test]
fn two_entries_into_one_cycle_keep_their_activations_apart() {
    let mut settled = crate::compiler2::drive_harness::Drive::fixture(1348).settle();

    let steps = executables_of(&mut settled, "reduce_step", 3);
    let entries: HashSet<_> = steps.iter().map(|step| step.activation.entry).collect();

    assert!(
        steps.len() > 1 && entries.len() == steps.len(),
        "three seeds of three shapes enter the reduce cycle three times, and each chain is keyed by its own entry: {steps:?}"
    );
}

/// A closure argument does not hide a wrong argument beside it. The closure's
/// own arrow variables are what the contract instantiates, so the row is
/// still judged; an `any` or a bare unsolved variable is a value nobody
/// knows, and the row is not.
#[test]
fn a_closure_column_does_not_stop_a_spec_violation_from_being_diagnosed() {
    let mut world = World::new();
    let types = world.types_mut();
    let atom = types.atom();
    let int = types.int();
    let alpha = types.param_alpha(0);
    let closure = types.arrow(&[alpha], alpha);
    let any = types.any();

    assert!(
        spec_violation_is_actionable(&mut world, &[atom, closure]),
        "an atom beside a closure is a known row the spec can refuse",
    );
    assert!(
        !spec_violation_is_actionable(&mut world, &[any, closure]),
        "an `any` column is unknown, closure or not",
    );
    assert!(
        !spec_violation_is_actionable(&mut world, &[alpha, int]),
        "a bare unsolved variable is an unknown column",
    );
}

/// One activation `caller` with a callee function and two activations of it,
/// the previous answers of its callsites stored in the world.
struct SupersessionFixture {
    world: World,
    caller: ActivationKey,
    old: ActivationKey,
    new: ActivationKey,
}

impl SupersessionFixture {
    fn new() -> Self {
        let mut world = World::new();
        let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
        let callee = world.reference_function(ModuleId::GLOBAL, "callee", 1);
        let int = world.types_mut().int();
        let float = world.types_mut().float();
        let caller = ActivationKey::from_inputs(root, world.root_function(root), &[], world.types_mut());
        let old = ActivationKey::from_inputs(root, callee, &[int], world.types_mut());
        let new = ActivationKey::from_inputs(root, callee, &[float], world.types_mut());
        Self {
            world,
            caller,
            old,
            new,
        }
    }

    fn callsite(&self, id: u32) -> CallSiteKey {
        CallSiteKey {
            activation: self.caller.clone(),
            callsite: crate::compiler2::body::CallSiteId::from_u32(id),
        }
    }

    fn naming(&self, target: &ActivationKey) -> CallSiteResolution<CallSiteSummary> {
        CallSiteResolution::Resolved(CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: crate::compiler2::semantic::SelectedCallee::Function(target.function),
                selector: None,
                surface_inputs: Vec::new(),
                activation: Some(target.clone()),
                activation_inputs: None,
                extern_params: None,
                return_ty: None,
            }],
            return_ty: None,
            last_resort: None,
        })
    }

    /// The previous analysis answered callsite `id` with `target`.
    fn previously(&mut self, id: u32, target: &ActivationKey) {
        let resolution = self.naming(target);
        self.world.define_callsite_summary(self.callsite(id), resolution);
    }

    /// The previous analysis resolved exactly these callsites.
    fn previously_resolved(&mut self, ids: &[u32]) {
        self.world.define_activation_analysis(
            &self.caller,
            ActivationAnalysis {
                input_rows: Vec::new(),
                entry_reachability: crate::compiler2::semantic::EntryReachability::new(Vec::new()),
                trimmed: Default::default(),
                reachable_entries: Vec::new(),
                callsites: ids
                    .iter()
                    .map(|id| crate::compiler2::body::CallSiteId::from_u32(*id))
                    .collect(),
                value_types: Default::default(),
            },
        );
    }

    fn emission(&self, id: u32, resolution: CallSiteResolution<CallSiteSummary>) -> CallEmission {
        CallEmission {
            key: self.callsite(id),
            resolution,
            activations: Vec::new(),
        }
    }

    fn superseded(&self, calls: &[CallEmission]) -> Vec<ActivationKey> {
        superseded_activations(&self.world, &self.caller, calls)
    }
}

/// A callsite the walk still reaches and now resolves to another activation
/// has stopped calling the old one: that is knowledge, so the old one is
/// superseded.
#[test]
fn a_resolved_callsite_that_now_names_another_activation_supersedes_the_old_one() {
    let mut fixture = SupersessionFixture::new();
    fixture.previously(1, &fixture.old.clone());
    fixture.previously_resolved(&[1]);
    let now = fixture.emission(1, fixture.naming(&fixture.new));

    assert_eq!(fixture.superseded(&[now]), vec![fixture.old.clone()]);
}

/// Unresolved is the lattice bottom: it says "not nameable yet", not "calls
/// nothing", so the callee the callsite last named stands.
#[test]
fn an_unresolved_callsite_supersedes_nothing() {
    let mut fixture = SupersessionFixture::new();
    fixture.previously(1, &fixture.old.clone());
    fixture.previously_resolved(&[1]);
    let now = fixture.emission(1, CallSiteResolution::Unresolved);

    assert_eq!(fixture.superseded(&[now]), Vec::<ActivationKey>::new());
}

/// A callsite the walk no longer reaches says nothing, and its silence covers
/// the callee another callsite has just stopped naming.
#[test]
fn a_callee_a_silent_callsite_last_named_is_not_superseded() {
    let mut fixture = SupersessionFixture::new();
    fixture.previously(1, &fixture.old.clone());
    fixture.previously(2, &fixture.old.clone());
    fixture.previously_resolved(&[1, 2]);
    let now = fixture.emission(1, fixture.naming(&fixture.new));

    assert_eq!(fixture.superseded(&[now]), Vec::<ActivationKey>::new());
}

/// A callee another reached callsite still names is not superseded by the one
/// that moved away from it.
#[test]
fn a_callee_a_resolved_callsite_still_names_is_not_superseded() {
    let mut fixture = SupersessionFixture::new();
    fixture.previously(1, &fixture.old.clone());
    fixture.previously(2, &fixture.old.clone());
    fixture.previously_resolved(&[1, 2]);
    let moved = fixture.emission(1, fixture.naming(&fixture.new));
    let stayed = fixture.emission(2, fixture.naming(&fixture.old));

    assert_eq!(fixture.superseded(&[moved, stayed]), Vec::<ActivationKey>::new());
}

/// An activation whose last caller stops calling it is retired, not run: its
/// job concludes without reading its body, no derivation or read is charged to
/// it, the contribution it made to its own callee leaves with it, and the
/// callee, now unclaimed in turn, is retired the same way.
#[test]
fn an_activation_that_loses_its_last_claimant_is_retired_without_running() {
    let tel = ConfiguredTelemetry::new();
    let retirements = Rc::new(RefCell::new(Vec::new()));
    let seen = Rc::clone(&retirements);
    tel.attach_raw_event2::<World, crate::compiler2::JobRetirement, _>(
        &["fz", "compiler2", "job", "retired"],
        move |_, _, _, _, retirement| {
            seen.borrow_mut()
                .push((retirement.job.clone(), retirement.ground.name()))
        },
    );
    let mut world = World::new();
    world.submit_code(
        Some("retired_chain.fz".to_string()),
        r#"
def leaf(_value), do: 0
def middle(value), do: leaf(value)
def top(), do: middle([1])
def main(), do: top()
"#
        .to_string(),
    );
    let root = world.submit_root(None, "main".to_string(), 0, ExecutableNeed::Value);
    assert!(matches!(
        ExecutionContext::new(&mut world, &tel).drive(),
        DriveOutcome::Resolved
    ));
    let int = world.types_mut().int();
    let int_list = world.types_mut().non_empty_list(int);
    let [top, middle, leaf] = ["top", "middle", "leaf"].map(|name| {
        let arity = usize::from(name != "top");
        world.reference_function(ModuleId::GLOBAL, name, arity)
    });
    let top_activation = world.activation_key(root, top, &[]);
    let middle_activation = world.activation_key(root, middle, &[int_list]);
    let leaf_activation = world.activation_key(root, leaf, &[int_list]);
    for activation in [&middle_activation, &leaf_activation] {
        assert!(
            world.has_fact(&FactKey::Activation(activation.clone())),
            "{activation:?} is claimed while its caller still calls it",
        );
    }

    // `top` is re-analysed against a body that calls nothing.
    let LoweredBody::Clauses {
        clauses,
        entries,
        generated,
        ..
    } = (*world.lowered_body(top)).clone();
    let silent = entries
        .into_iter()
        .map(|entry| LoweredEntry {
            steps: Vec::new(),
            tail: LoweredTail::Unreachable,
            ..entry
        })
        .collect();
    assert!(world.define_lowered_body(top, LoweredBody::clauses(clauses, silent, generated)));
    world.complete_job(
        Job::LowerFunction(top),
        JobEffects {
            outputs: vec![FactKey::LoweredBody(top)],
            changed: vec![FactKey::LoweredBody(top)],
            ..JobEffects::default()
        },
    );
    let top_effects = analyze_activation(&mut world, &tel, &top_activation).expect("top concludes on its new body");
    ExecutionContext::new(&mut world, &tel).complete_job(Job::AnalyzeActivation(top_activation), top_effects);
    assert!(
        !world.has_fact(&FactKey::Activation(middle_activation.clone())),
        "nothing calls middle any more",
    );
    assert!(retirements.borrow().is_empty(), "no job has been retired yet");

    let retire = |world: &mut World, activation: &ActivationKey| {
        let job = Job::AnalyzeActivation(activation.clone());
        let effects = crate::compiler2::jobs::run(&mut ExecutionContext::new(world, &tel), &job)
            .expect("an unclaimed activation concludes");
        assert!(effects.retired, "{job:?} concludes without running its body");
        ExecutionContext::new(world, &tel).complete_job(job, effects)
    };
    let middle_completion = retire(&mut world, &middle_activation);
    assert_eq!(
        (middle_completion.derivations, middle_completion.reads_handed),
        (0, 0),
        "a retirement is neither a derivation nor a read served to a body",
    );
    assert!(
        !world.has_fact(&FactKey::ActivationInputs(leaf_activation.clone()))
            && !world.has_fact(&FactKey::Activation(leaf_activation.clone())),
        "the row middle fed leaf leaves with middle, and with it the claim on leaf",
    );
    let leaf_completion = retire(&mut world, &leaf_activation);
    assert_eq!((leaf_completion.derivations, leaf_completion.reads_handed), (0, 0));
    assert_eq!(
        *retirements.borrow(),
        vec![
            (Job::AnalyzeActivation(middle_activation), "unclaimed_activation"),
            (Job::AnalyzeActivation(leaf_activation), "unclaimed_activation"),
        ],
        "each retirement is reported once, with its ground",
    );
}
