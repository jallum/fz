use super::*;
use crate::compiler2::drive::ExecutionContext;
use crate::compiler2::dump::DumpStage;
use crate::compiler2::{CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, RootSubmission};
use crate::telemetry::ConfiguredTelemetry;
use std::cell::RefCell;
use std::collections::HashSet;
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
            Some(1),
            "val/1 must publish its return exactly once, never from a subset of its clauses \
             while arr/2's call back into it is still pending",
        );
    }
}
