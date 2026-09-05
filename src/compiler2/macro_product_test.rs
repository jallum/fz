//! Macro source consumers read the same retained product authority as runtime roots.

use std::cell::RefCell;
use std::rc::Rc;

use crate::telemetry::ConfiguredTelemetry;

use super::pull::{ProductKey, ProductRequestId, PullOutcome};
use super::{CodeSubmission, Compiler2, ExecutableNeed, Job, ModuleId, RootSubmission, World};

#[test]
fn replacing_a_macro_with_an_ordinary_function_rejects_its_captured_macro_use() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_before_replacement.fz".into()),
        text: "defmacro answer() do\n quote do: 40 + 1\nend\nfn main(), do: answer()\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(41));
    let replacement = compiler.submit_code(CodeSubmission {
        name: Some("ordinary_replacement.fz".into()),
        text: "fn answer(), do: 42\n".into(),
    });
    assert!(compiler.run_root_interp(root).is_err());
    let events = diagnostics.events();
    let diagnostic = events.iter().find_map(|event| event.diagnostic.as_ref()).unwrap();
    assert_eq!(diagnostic.code, crate::diag::codes::LOWER_UNSUPPORTED);
    assert!(diagnostic.message.contains("not a macro"), "{}", diagnostic.message);
    assert_eq!(super::CodeId::from_source(diagnostic.primary.span.code_id), replacement);
    assert_eq!((diagnostic.primary.span.start, diagnostic.primary.span.end), (0, 19));
}

#[test]
fn failed_macro_product_remains_demanded_after_retirement_and_source_repair() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let mut compiler = Compiler2::new(tel);
    let failed_code = compiler.submit_code(CodeSubmission {
        name: Some("macro_product_missing_remote.fz".into()),
        text: "defmacro answer() do\n quote do: unquote(Missing.value())\nend\nfn main(), do: answer()\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert!(
        compiler.run_root_interp(root).is_err(),
        "an absent macro dependency cannot certify expanded source"
    );
    let events = diagnostics.events();
    let diagnostic = events.iter().find_map(|event| event.diagnostic.as_ref()).unwrap();
    assert_eq!(diagnostic.code, crate::diag::codes::LOWER_UNBOUND);
    assert_eq!(super::CodeId::from_source(diagnostic.primary.span.code_id), failed_code);
    assert_eq!((diagnostic.primary.span.start, diagnostic.primary.span.end), (40, 53));
    let function = compiler.world_mut().reference_function(ModuleId::GLOBAL, "answer", 0);
    let macro_root = compiler.world_mut().macro_root(function);
    assert_eq!(
        compiler.retained_product_generation(macro_root, &ProductKey::RootBackendProduct(macro_root)),
        None
    );
    assert!(compiler.retire_root_products(macro_root));
    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_repaired.fz".into()),
        text: "defmacro answer() do\n quote do: 40 + 2\nend\n".into(),
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "the exact failed product demand must survive until its dependency can be produced: {:?}",
        diagnostics.events()
    );
    assert_eq!(
        compiler.retained_product_generation(macro_root, &ProductKey::RootBackendProduct(macro_root)),
        Some(1)
    );
}

#[test]
fn macro_content_movement_reexecutes_only_source_consumers_of_changed_content() {
    let tel = ConfiguredTelemetry::new();
    let diagnostics = crate::telemetry::Capture::new();
    diagnostics.install(&tel, &["fz", "diag"]);
    let jobs = Rc::new(RefCell::new(Vec::<Job>::new()));
    let evaluations = Rc::new(RefCell::new(Vec::<ProductKey>::new()));
    let observed = Rc::clone(&jobs);
    tel.attach_raw_event2::<World, super::JobCompletion, _>(
        &["fz", "compiler2", "work_graph", "applied"],
        move |_, _, _, _, completion| observed.borrow_mut().push(completion.job.clone()),
    );
    let observed = Rc::clone(&evaluations);
    tel.attach_raw_event3::<ProductKey, ProductRequestId, PullOutcome, _>(
        &["fz", "compiler2", "pull", "product", "evaluated"],
        move |_, _, _, key, _, _| observed.borrow_mut().push(key.clone()),
    );
    let mut compiler = Compiler2::new(tel);
    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_initial.fz".into()),
        text: "fn offset(), do: 1\ndefmacro inc(x) do\n quote do: unquote(x) + unquote(offset())\nend\nfn main(), do: inc(40)\nfn control_offset(), do: 3\ndefmacro control_inc(x) do\n quote do: unquote(x) + unquote(control_offset())\nend\nfn control(), do: control_inc(40)\n".into(),
    });
    let root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(root), Ok(41), "{:?}", diagnostics.events());
    let main = compiler.root_function(root);
    let function = compiler.world_mut().reference_function(ModuleId::GLOBAL, "inc", 1);
    let macro_root = compiler.world_mut().macro_root(function);
    let content = ProductKey::RootBackendProduct(macro_root);
    let generation = compiler.retained_product_generation(macro_root, &content);
    assert_eq!(generation, Some(1));
    let program = compiler.retained_backend_program(macro_root);
    let source_consumer = Job::ExpandFunctionSource(main);
    let control_root = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "control".into(),
        arity: 0,
        need: ExecutableNeed::Value,
    });
    assert_eq!(compiler.run_root_interp(control_root), Ok(43));
    let control_consumer = Job::ExpandFunctionSource(compiler.root_function(control_root));
    let control_function = compiler
        .world_mut()
        .reference_function(ModuleId::GLOBAL, "control_inc", 1);
    let control_macro_root = compiler.world_mut().macro_root(control_function);
    let control_content = ProductKey::RootBackendProduct(control_macro_root);
    let control_generation = compiler.retained_product_generation(control_macro_root, &control_content);
    let control_program = compiler.retained_backend_program(control_macro_root);

    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    assert_eq!(compiler.run_root_interp(root), Ok(41));
    assert!(
        evaluations.borrow().is_empty(),
        "unchanged macro calls reuse the settled root without compiler evaluation"
    );
    assert!(jobs.borrow().is_empty());

    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_unrelated.fz".into()),
        text: "fn unrelated(), do: 99\n".into(),
    });
    assert_eq!(compiler.run_root_interp(root), Ok(41));
    assert!(
        evaluations.borrow().is_empty(),
        "unrelated source cannot dirty the macro root"
    );
    assert!(!jobs.borrow().contains(&source_consumer));

    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    compiler.reproduce_job_for_test(Job::SeedRoot(macro_root), vec![super::FactKey::RootEntry(macro_root)]);
    assert_eq!(compiler.run_root_interp(root), Ok(41), "{:?}", diagnostics.events());
    assert!(
        evaluations
            .borrow()
            .contains(&ProductKey::RootBackendProduct(macro_root)),
        "invalidating the exact root prerequisite must reproduce backend content from the same source snapshot"
    );
    assert_eq!(compiler.retained_product_generation(macro_root, &content), generation);
    assert!(Rc::ptr_eq(&program, &compiler.retained_backend_program(macro_root)));
    assert!(
        !jobs.borrow().contains(&source_consumer),
        "equal backend reproduction must restore source finality without executing its consumer"
    );

    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    compiler.submit_code(CodeSubmission {
        name: Some("macro_product_changed.fz".into()),
        text: "fn offset(), do: 2\n".into(),
    });
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "changed compile-time content must invalidate the exact source reader before runtime consumption"
    );
    assert_eq!(compiler.retained_product_generation(macro_root, &content), Some(2));
    assert_eq!(jobs.borrow().iter().filter(|job| **job == source_consumer).count(), 1);
    assert!(evaluations.borrow().contains(&content));
    assert!(!jobs.borrow().contains(&control_consumer));
    assert!(!evaluations.borrow().contains(&control_content));
    assert_eq!(
        compiler.retained_product_generation(control_macro_root, &control_content),
        control_generation
    );
    assert!(Rc::ptr_eq(
        &control_program,
        &compiler.retained_backend_program(control_macro_root)
    ));
    jobs.borrow_mut().clear();
    evaluations.borrow_mut().clear();
    assert_eq!(compiler.run_root_interp(control_root), Ok(43));
    assert!(jobs.borrow().is_empty());
    assert!(evaluations.borrow().is_empty());

    let retained = compiler.retained_backend_program(macro_root);
    let released = Rc::downgrade(&retained);
    drop(retained);
    assert!(compiler.retire_root_products(macro_root));
    assert!(
        released.upgrade().is_none(),
        "no World mirror may keep a retired macro backend alive"
    );
    assert_eq!(
        compiler.run_root_interp(root),
        Ok(42),
        "retiring a consumed macro product withdraws its dependency and a later request reproduces it"
    );
}
