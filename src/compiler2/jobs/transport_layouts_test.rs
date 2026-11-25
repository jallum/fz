//! The executable-scoped transport facts: what a job reads, when its fact
//! reports a change, and which side of a recursion cuts.

use std::cell::RefCell;
use std::rc::Rc;

use crate::compiler2::identity::ExecutableNeed;
use crate::compiler2::jobs::transport::return_edge_is_cut;
use crate::compiler2::world::{JobCompletion, World};
use crate::compiler2::{CodeSubmission, Compiler2, FactKey, Job, RootSubmission};
use crate::fast_hash::HashSet;
use crate::telemetry::ConfiguredTelemetry;

/// One job run as the work graph recorded it: what the run stood on.
#[derive(Clone)]
struct Run {
    job: Job,
    reads: HashSet<FactKey>,
}

struct Observed {
    compiler: Compiler2<ConfiguredTelemetry>,
    runs: Rc<RefCell<Vec<Run>>>,
}

impl Observed {
    fn new(text: &str) -> (Self, crate::compiler2::RootId) {
        let tel = ConfiguredTelemetry::new();
        let runs = Rc::new(RefCell::new(Vec::new()));
        let sink = Rc::clone(&runs);
        tel.attach_raw_event2::<World, JobCompletion, _>(
            &["fz", "compiler2", "work_graph", "applied"],
            move |_, _, _, world, completion| {
                let reads = world
                    .job_reads(&completion.job)
                    .iter()
                    .map(|read| read.fact().clone())
                    .collect();
                sink.borrow_mut().push(Run {
                    job: completion.job.clone(),
                    reads,
                });
            },
        );
        let mut compiler = Compiler2::new(tel);
        compiler.submit_code(CodeSubmission {
            name: Some("transport_layouts.fz".to_string()),
            text: text.to_string(),
        });
        let root = compiler.submit_root(RootSubmission {
            module_name: None,
            name: "main".to_string(),
            arity: 0,
            need: ExecutableNeed::Value,
        });
        (Self { compiler, runs }, root)
    }

    fn runs(&self) -> Vec<Run> {
        self.runs.borrow().clone()
    }
}

/// The last run of every job `select` names, in job order of first appearance.
fn last_runs(runs: &[Run], select: impl Fn(&Job) -> bool) -> Vec<Run> {
    let mut last: Vec<Run> = Vec::new();
    for run in runs.iter().filter(|run| select(&run.job)) {
        match last.iter_mut().find(|known| known.job == run.job) {
            Some(known) => *known = run.clone(),
            None => last.push(run.clone()),
        }
    }
    last
}

/// Another executable's input or return is one read of that executable's
/// interface fact, and a body is never read from outside its executable: no
/// job stands on a foreign body, and a body job reads foreign interfaces only.
#[test]
fn a_foreign_input_or_return_is_one_read_of_the_interface() {
    let (mut observed, root) =
        Observed::new("def a(x), do: x + 1\ndef b(x), do: {x, x}\ndef main(), do: {a(1), b(2), a(1)}\n");
    let main = observed.compiler.root_function(root);
    observed.compiler.compile_root_jit(root).expect("compiles");
    let runs = observed.runs();

    let main_interface = last_runs(
        &runs,
        |job| matches!(job, Job::DeriveTransportInterface(executable) if executable.activation.function == main),
    );
    assert_eq!(main_interface.len(), 1, "main has one interface job");
    let foreign_interfaces = main_interface[0]
        .reads
        .iter()
        .filter(|fact| matches!(fact, FactKey::TransportInterface(read) if read.activation.function != main))
        .count();
    assert_eq!(
        foreign_interfaces, 2,
        "main's return stands on the interfaces of `a` and of `b`, one read each, however often it calls them"
    );

    for run in last_runs(&runs, |job| {
        matches!(job, Job::DeriveTransportInterface(_) | Job::DeriveTransportBody(_))
    }) {
        let owner = match &run.job {
            Job::DeriveTransportInterface(executable) | Job::DeriveTransportBody(executable) => executable,
            other => unreachable!("selected only transport jobs: {other:?}"),
        };
        let foreign_bodies = run
            .reads
            .iter()
            .filter(|fact| matches!(fact, FactKey::TransportBody(read) if read != owner))
            .collect::<Vec<_>>();
        assert!(
            foreign_bodies.is_empty(),
            "{:?} stands on another executable's body: {foreign_bodies:?}",
            run.job
        );
    }
}

/// An interface fact reports a change only when a layout differs, so what
/// reads it is woken only by a layout that moved: republishing the layouts it
/// already holds changes nothing, and a different layout does.
#[test]
fn an_interface_reports_a_change_only_when_a_layout_differs() {
    use crate::compiler2::artifact::TransportLayouts;
    use crate::compiler2::identity::{ModuleId, RootId};
    use crate::compiler2::transport::{ExecutableSymbol, LaneDescr, ShapeDescr, TransportClass, TransportPosition};
    use crate::compiler2::{ActivationKey, ExecutableKey};
    use std::rc::Rc;

    let mut world = World::new();
    let int = world.types_mut().int();
    let atom = world.types_mut().atom();
    let function = world.reference_function(ModuleId::GLOBAL, "callee", 1);
    let activation = ActivationKey::from_inputs(RootId::for_test(1), function, &[int], world.types_mut());
    let executable = ExecutableKey {
        activation,
        need: ExecutableNeed::Value,
    };
    let position = TransportPosition::ExecutableReturn {
        executable: ExecutableSymbol::new(&executable),
    };
    let mut layout_of = |ty| {
        let lane = world.intern_lane(LaneDescr {
            ty,
            class: TransportClass::Value,
        });
        crate::compiler2::pull::TransportLayout::structural(world.intern_shape(ShapeDescr::Lane(lane)))
    };
    let (as_int, as_atom) = (layout_of(int), layout_of(atom));
    let publish = |world: &mut World, layout| {
        world.define_transport_interface(
            executable.clone(),
            Rc::new(TransportLayouts::from_iter([(position.clone(), layout)])),
        )
    };

    assert!(publish(&mut world, as_int), "the first publication is a change");
    assert!(
        !publish(&mut world, as_int),
        "republishing the layouts already held reports nothing changed"
    );
    assert!(publish(&mut world, as_atom), "a different layout is a change");
}

/// In a recursion the two returns do not wait on each other: the side the typed
/// origin order names cuts its edge and does not read the other's interface,
/// and the other side reads it.
#[test]
fn the_return_edge_of_a_recursion_is_cut_on_the_side_typed_origin_names() {
    use crate::compiler2::identity::ModuleId;
    let (mut observed, root) = Observed::new(
        "def even(n), do: if n == 0, do: true, else: odd(n - 1)\n\
         def odd(n), do: if n == 0, do: false, else: even(n - 1)\n\
         def main(), do: even(4)\n",
    );
    let main = observed.compiler.root_function(root);
    observed.compiler.compile_root_jit(root).expect("compiles");
    let runs = observed.runs();

    let interfaces = last_runs(
        &runs,
        |job| matches!(job, Job::DeriveTransportInterface(executable) if executable.activation.function != main),
    );
    let function_of = |run: &Run| match &run.job {
        Job::DeriveTransportInterface(executable) => executable.activation.function,
        other => unreachable!("selected only interface jobs: {other:?}"),
    };
    let world = observed.compiler.world_mut();
    let (first, second) = (
        world.reference_function(ModuleId::GLOBAL, "even", 1),
        world.reference_function(ModuleId::GLOBAL, "odd", 1),
    );
    let reads = |owner, callee| {
        interfaces.iter().filter(|run| function_of(run) == owner).any(|run| {
            run.reads
                .iter()
                .any(|read| matches!(read, FactKey::TransportInterface(read) if read.activation.function == callee))
        })
    };
    let types = observed.compiler.world().types();
    for (owner, callee) in [(first, second), (second, first)] {
        assert_eq!(
            reads(owner, callee),
            !return_edge_is_cut(types, callee, owner),
            "{owner:?} reads {callee:?}'s interface exactly when typed origin keeps the edge"
        );
    }
    assert_ne!(
        reads(first, second),
        reads(second, first),
        "exactly one side of the recursion reads the other; the other side cuts its edge"
    );
}

/// The interfaces a run of `Job::DeriveTransportInterface` read, by function.
fn interface_edges(runs: &[Run]) -> Vec<(crate::compiler2::FunctionId, crate::compiler2::FunctionId)> {
    last_runs(runs, |job| matches!(job, Job::DeriveTransportInterface(_)))
        .iter()
        .flat_map(|run| {
            let Job::DeriveTransportInterface(owner) = &run.job else {
                unreachable!("selected only interface jobs")
            };
            run.reads
                .iter()
                .filter_map(|read| match read {
                    FactKey::TransportInterface(callee) if callee != owner => {
                        Some((owner.activation.function, callee.activation.function))
                    }
                    _ => None,
                })
                .collect::<Vec<_>>()
        })
        .collect()
}

/// Two lambdas that capture one another's calls wait on each other's
/// interfaces; the cycle settles and the program compiles.
#[test]
fn lambdas_capturing_each_others_calls_settle_though_their_interfaces_wait_on_each_other() {
    let (mut observed, root) = Observed::new(
        "def swap(0, a, _b), do: a\n\
         def swap(n, a, b), do: swap(n - 1, fn x -> b.(x) end, fn y -> a.(y) end)\n\
         def main(), do: swap(3, fn x -> x end, fn y -> y + 1 end).(1)\n",
    );
    observed
        .compiler
        .compile_root_jit(root)
        .expect("a capture cycle settles");
    let edges = interface_edges(&observed.runs());
    assert!(
        edges.iter().any(|(a, b)| a != b && edges.contains(&(*b, *a))),
        "two interfaces read one another: {edges:?}"
    );
}

/// The shape of a layout with every world-local id erased: what two worlds
/// that made the same decision agree on.
fn layout_skeleton(world: &World, layout: crate::compiler2::pull::TransportLayout) -> String {
    use crate::compiler2::transport::{ShapeDescr, TransportCarrier};
    let shape = match world.shape(layout.structural) {
        ShapeDescr::Nothing => "nothing".to_string(),
        ShapeDescr::Lane(lane) => format!("lane:{:?}", world.lane(*lane).class),
        ShapeDescr::Tuple(fields) => {
            let fields: Vec<_> = fields.iter().map(|field| layout_skeleton(world, *field)).collect();
            format!("tuple({})", fields.join(","))
        }
        ShapeDescr::Callable(callable) => {
            let captures: Vec<_> = world
                .callable(*callable)
                .capture_layouts
                .iter()
                .map(|capture| layout_skeleton(world, *capture))
                .collect();
            format!("callable({})", captures.join(","))
        }
        ShapeDescr::Cursor { .. } => "cursor".to_string(),
    };
    match layout.carrier {
        TransportCarrier::Absent => shape,
        TransportCarrier::ValueRef(_) => format!("{shape}@ref"),
    }
}

/// Every interface a run settled, by function name and position kind.
fn interface_skeletons(observed: &mut Observed, named: &[(&str, usize)]) -> Vec<String> {
    use crate::compiler2::identity::ModuleId;
    let functions: Vec<_> = named
        .iter()
        .map(|(name, arity)| {
            (
                observed
                    .compiler
                    .world_mut()
                    .reference_function(ModuleId::GLOBAL, *name, *arity),
                *name,
            )
        })
        .collect();
    let world = observed.compiler.world();
    let mut lines = Vec::new();
    for run in last_runs(&observed.runs(), |job| matches!(job, Job::DeriveTransportInterface(_))) {
        let Job::DeriveTransportInterface(executable) = &run.job else {
            continue;
        };
        let Some((_, name)) = functions
            .iter()
            .find(|(function, _)| *function == executable.activation.function)
        else {
            continue;
        };
        let layouts = world
            .transport_interface(executable)
            .expect("a run interface is settled");
        let mut per_position: Vec<String> = layouts
            .iter()
            .map(|(position, layout)| {
                let kind = match position {
                    crate::compiler2::transport::TransportPosition::ExecutableInput { semantic_index, .. } => {
                        format!("in{semantic_index}")
                    }
                    crate::compiler2::transport::TransportPosition::ExecutableReturn { .. } => "ret".to_string(),
                    other => format!("{other:?}"),
                };
                format!("{kind}={}", layout_skeleton(world, layout))
            })
            .collect();
        per_position.sort();
        lines.push(format!("{name}: {}", per_position.join(" ")));
    }
    lines.sort();
    lines
}

/// The interface layouts do not depend on the order the work is discovered
/// in: the same functions defined in the opposite order, so the jobs run in
/// the opposite order, settle the same layouts.
#[test]
fn interfaces_settle_the_same_layouts_whatever_order_the_work_is_discovered_in() {
    let functions = [
        "def even(n), do: if n == 0, do: true, else: odd(n - 1)\n",
        "def odd(n), do: if n == 0, do: false, else: even(n - 1)\n",
        "def swap(0, a, _b), do: a\ndef swap(n, a, b), do: swap(n - 1, fn x -> b.(x) end, fn y -> a.(y) end)\n",
        "def pair(x), do: {x, fn y -> x + y end}\n",
    ];
    let main = "def main(), do: {even(4), swap(3, fn x -> x end, fn y -> y + 1 end).(1), pair(2)}\n";
    let mut forward = functions.join("");
    forward.push_str(main);
    let mut reversed = functions.iter().rev().copied().collect::<String>();
    reversed.push_str(main);

    let skeletons = |text: &str| {
        let (mut observed, root) = Observed::new(text);
        observed.compiler.compile_root_jit(root).expect("compiles");
        interface_skeletons(
            &mut observed,
            &[("even", 1), ("odd", 1), ("swap", 3), ("pair", 1), ("main", 0)],
        )
    };
    let (forward, reversed) = (skeletons(&forward), skeletons(&reversed));
    assert!(
        forward.len() >= 5,
        "the program has interfaces to compare: {forward:#?}"
    );
    assert_eq!(forward, reversed);
}

/// Two recursive functions that share a callee: whichever of them the typed
/// origin order names cuts its edge to the other, and the shared function's
/// interface is read by both.
#[test]
fn recursive_executables_sharing_a_function_cut_one_edge_and_settle() {
    use crate::compiler2::FunctionId;
    use crate::compiler2::identity::ModuleId;
    let (mut observed, root) = Observed::new(
        "def twice(x), do: {x, x}\n\
         def even(n), do: if n == 0, do: twice(true), else: odd(n - 1)\n\
         def odd(n), do: if n == 0, do: twice(false), else: even(n - 1)\n\
         def main(), do: {even(4), odd(3)}\n",
    );
    observed.compiler.compile_root_jit(root).expect("compiles");
    let edges = interface_edges(&observed.runs());
    let world = observed.compiler.world_mut();
    let mut function = |name: &str| world.reference_function(ModuleId::GLOBAL, name, 1);
    let (twice, even, odd) = (function("twice"), function("even"), function("odd"));
    let reading = |callee: FunctionId| {
        edges
            .iter()
            .filter(|(_, read)| *read == callee)
            .map(|(owner, _)| *owner)
            .collect::<std::collections::BTreeSet<_>>()
            .len()
    };
    assert_eq!(
        reading(twice),
        2,
        "both recursive functions read the shared function's interface"
    );
    let (even, odd) = (reading(even), reading(odd));
    assert_eq!(
        even + odd,
        3,
        "main reads each of the pair, and exactly one of them reads the other besides: {edges:?}"
    );
}
