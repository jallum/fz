use super::{CodeState, CodeSubmission, Compiler2, FactKey, FunctionId, FunctionState, NamespaceSymbol, World};
use crate::telemetry::{Capture, ConfiguredTelemetry};

#[test]
fn compiler2_index_code_defines_owned_functions_without_lowering_or_activating_bodies() {
    let tel = ConfiguredTelemetry::new();
    let capture = Capture::new();
    tel.attach(&[], capture.handler());

    let mut compiler = Compiler2::new();
    let mut world = World::new();
    let source = format!(
        "{}\nfn foo(), do: 42\n",
        include_str!("../../fixtures/quicksort/input.fz")
    );

    let submitted = compiler
        .submit_code(
            &mut world,
            CodeSubmission {
                name: Some("fixtures/quicksort_plus_foo.fz".to_string()),
                text: source,
            },
            &tel,
        )
        .expect("indexing quicksort plus foo should succeed");

    let code = world.code().get(submitted.code_id).expect("indexed code");
    let function_ids = match code.state() {
        CodeState::Indexed { modules, functions } => {
            assert!(modules.is_empty(), "quicksort plus foo is a top-level program");
            functions.clone()
        }
        other => panic!("submitted code should be indexed, got {other:?}"),
    };
    assert_eq!(function_ids.len(), 5, "quicksort plus foo should define five functions");

    let mut names = function_ids
        .iter()
        .map(|function_id| {
            let function_ref = world
                .functions()
                .reference_for(*function_id)
                .expect("indexed function ref");
            (
                function_ref.name.clone(),
                function_ref.arity,
                function_ref.module,
                *function_id,
            )
        })
        .collect::<Vec<_>>();
    names.sort_by(|left, right| left.0.cmp(&right.0).then(left.1.cmp(&right.1)));
    assert_eq!(
        names
            .iter()
            .map(|(name, arity, module, _)| (name.as_str(), *arity, *module))
            .collect::<Vec<_>>(),
        vec![
            ("append", 2, None),
            ("foo", 0, None),
            ("main", 0, None),
            ("partition", 4, None),
            ("qsort", 1, None),
        ],
        "indexing should define the expected top-level functions without introducing modules"
    );

    let qsort_id = find_function(&names, "qsort", 1);
    let foo_id = find_function(&names, "foo", 0);
    let main_id = find_function(&names, "main", 0);
    for function_id in &function_ids {
        let function = world.functions().get(*function_id).expect("defined function");
        match function.state() {
            FunctionState::Defined { def } => {
                assert_eq!(
                    def.code(),
                    submitted.code_id,
                    "indexed functions should point back to the contributing code"
                );
            }
            other => panic!("indexed function should be defined, got {other:?}"),
        }
        assert_eq!(
            world.scheduler().facts().get(&FactKey::FunctionDefined(*function_id)),
            Some(&function.revision()),
            "indexing should publish a FunctionDefined fact for each function"
        );
        assert_eq!(
            world.scheduler().facts().get(&FactKey::LoweredBody(*function_id)),
            None,
            "indexing should not lower bodies"
        );
        assert_eq!(
            world.scheduler().facts().get(&FactKey::Activation(*function_id)),
            None,
            "indexing should not create activations"
        );
        assert_eq!(
            world.scheduler().facts().get(&FactKey::Executable(*function_id)),
            None,
            "indexing should not create executables"
        );
    }

    let main = world.functions().get(main_id).expect("main function");
    let main_namespace = match main.state() {
        FunctionState::Defined { def } => def.namespace(),
        other => panic!("main should be defined, got {other:?}"),
    };
    assert_eq!(
        world.namespaces().lookup(main_namespace, "qsort"),
        Some(&NamespaceSymbol::Functions(vec![qsort_id])),
        "main should capture a namespace head that can resolve qsort"
    );
    assert_eq!(
        world.namespaces().lookup(main_namespace, "foo"),
        Some(&NamespaceSymbol::Functions(vec![foo_id])),
        "main should capture a namespace head that can resolve the newly added foo/0"
    );

    assert_eq!(
        capture.count(&["fz", "compiler2", "code", "indexed"]),
        1,
        "indexing should emit one indexed event"
    );
    assert_eq!(
        capture.count(&["fz", "frontend", "lowered"]),
        0,
        "indexing should stay above lowering"
    );
}

fn find_function(
    names: &[(String, usize, Option<super::ModuleId>, FunctionId)],
    name: &str,
    arity: usize,
) -> FunctionId {
    names
        .iter()
        .find(|(candidate, candidate_arity, _, _)| candidate == name && *candidate_arity == arity)
        .map(|(_, _, _, id)| *id)
        .unwrap_or_else(|| panic!("missing indexed function {name}/{arity}"))
}
