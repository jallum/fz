//! Independent census of the native handoff's references and executable closure.

use std::collections::{HashMap, HashSet};

use super::artifact::{NativeBodyOrigin, NativeProgram, ir_control_fn_ids};
use crate::fz_ir::{FnId, Prim, Stmt};

pub(super) fn unreachable_native_functions(program: &NativeProgram) -> Vec<FnId> {
    let functions: HashSet<_> = program.module.fns.iter().map(|function| function.id).collect();
    assert_eq!(
        functions.len(),
        program.module.fns.len(),
        "duplicate native function identity"
    );
    assert_eq!(
        program.module.fn_idx.len(),
        functions.len(),
        "native function index cardinality"
    );
    for (index, function) in program.module.fns.iter().enumerate() {
        assert_eq!(
            program.module.fn_idx.get(&function.id),
            Some(&index),
            "native function index disagrees"
        );
    }
    let bodies: HashSet<_> = program.bodies.iter().map(|body| body.fn_id).collect();
    assert_eq!(bodies.len(), program.bodies.len(), "duplicate native body identity");
    assert_eq!(bodies, functions, "native bodies and functions must form a bijection");
    let require_function = |id: FnId| {
        assert!(functions.contains(&id), "dangling native function reference: {id:?}");
    };
    for body in &program.bodies {
        if let NativeBodyOrigin::Continuation { owner } = body.origin {
            assert!(
                functions.contains(&owner),
                "dangling native continuation owner: {owner:?}"
            );
        }
    }
    let mut roots = vec![program.entry];
    roots.extend(program.executable_entries.iter().map(|entry| entry.fn_id));
    let mut identities = HashMap::new();
    for boundary in &program.callable_boundaries {
        assert!(
            identities.insert(boundary.identity_fn, boundary.wrapper_fn).is_none(),
            "duplicate native callable identity"
        );
        roots.push(boundary.wrapper_fn);
        roots.extend(boundary.members.iter().map(|member| member.target_fn));
    }
    let construction_target = |id: FnId| {
        *identities
            .get(&id)
            .unwrap_or_else(|| panic!("unpublished native construction identity: {id:?}"))
    };
    let mut control = HashMap::new();
    for function in &program.module.fns {
        let targets = ir_control_fn_ids(function);
        targets.iter().copied().for_each(&require_function);
        control.insert(function.id, targets);
        for block in &function.blocks {
            for Stmt::Let(_, prim) in &block.stmts {
                match prim {
                    Prim::MakeFnRef(_, id) | Prim::MakeClosure(_, id, _) => roots.push(construction_target(*id)),
                    Prim::ClosureCapture { constructions, .. } => {
                        roots.extend(constructions.iter().copied().map(&construction_target))
                    }
                    _ => {}
                }
            }
        }
    }
    roots.iter().copied().for_each(require_function);
    let mut reached = HashSet::new();
    while let Some(id) = roots.pop() {
        if reached.insert(id) {
            roots.extend(control[&id].iter().copied());
        }
    }
    let mut unreachable: Vec<_> = functions.difference(&reached).copied().collect();
    unreachable.sort_by_key(|id| id.0);
    unreachable
}

fn inventory_fixture(count: u32) -> NativeProgram {
    use super::artifact::{EffectSummary, NativeBody, NativeEntryAbi};
    use crate::fz_ir::{Block, BlockId, FnCategory, FnIr, Module, Term, Var};

    let ty = super::Types::new().int();
    let mut module = Module::default();
    let mut bodies = Vec::new();
    for id in 0..count {
        let fn_id = FnId(id);
        module.fn_idx.insert(fn_id, module.fns.len());
        module.fns.push(FnIr {
            id: fn_id,
            name: format!("inventory_{id}"),
            frame_schema_id: 0,
            blocks: vec![Block {
                id: BlockId(0),
                params: vec![Var(0)],
                stmts: Vec::new(),
                terminator: Term::Return(Var(0)),
            }],
            entry: BlockId(0),
            category: FnCategory::User,
            owner_module: String::new(),
            ignored_entry_params: Vec::new(),
            physical_entry_params: Vec::new(),
            physical_capabilities: Vec::new(),
        });
        bodies.push(NativeBody {
            fn_id,
            origin: NativeBodyOrigin::CallableWrapper { identity: id },
            entry_abi: NativeEntryAbi::Direct,
            param_reprs: Vec::new(),
            return_ty: ty,
            return_reprs: Vec::new(),
            return_tuple_arity: None,
            block_param_reprs: HashMap::new(),
            value_types: HashMap::new(),
            extern_marshals: HashMap::new(),
            effects: EffectSummary::default(),
        });
    }
    NativeProgram {
        entry: FnId(0),
        module,
        executable_entries: Vec::new(),
        bodies,
        callable_boundaries: Vec::new(),
    }
}

fn inventory_boundary(identity: u32, wrapper: u32) -> super::artifact::NativeCallableBoundary {
    use super::artifact::{BackendCallableReturn, NativeCallableBoundary, NativeCallableBoundaryId};
    NativeCallableBoundary {
        id: NativeCallableBoundaryId(identity),
        identity_fn: FnId(identity),
        callable: super::transport::CallableId::for_test(identity),
        shape: None,
        wrapper_fn: FnId(wrapper),
        captures: Box::default(),
        capture_reprs: Box::default(),
        call_arity: 0,
        return_form: BackendCallableReturn::Absent,
        task_halt_repr: None,
        members: Box::default(),
        selection: None,
    }
}

#[test]
fn native_inventory_resolves_published_identity_words_to_wrapper_bodies() {
    let mut program = inventory_fixture(3);
    program.callable_boundaries.push(inventory_boundary(100, 1));
    assert_eq!(unreachable_native_functions(&program), vec![FnId(2)]);
    let mut duplicate = program.clone();
    duplicate.callable_boundaries.push(inventory_boundary(100, 2));
    assert!(std::panic::catch_unwind(|| unreachable_native_functions(&duplicate)).is_err());
    program.callable_boundaries[0].wrapper_fn = FnId(99);
    assert!(std::panic::catch_unwind(|| unreachable_native_functions(&program)).is_err());
}

#[test]
fn native_inventory_roots_semantic_entries_and_callable_members() {
    use super::artifact::{BackendReturnLayout, BackendValueLayout, NativeConstructionMember, NativeExecutableEntry};
    use super::transport::{BoundaryId, ShapeId, TransportCarrier};
    let mut types = super::Types::new();
    let key = super::ExecutableKey {
        activation: super::ActivationKey::from_inputs(
            super::RootId::for_test(0),
            super::FunctionId::for_test(0),
            &[],
            &mut types,
        ),
        need: super::ExecutableNeed::Value,
    };
    let mut program = inventory_fixture(4);
    program.executable_entries.push(NativeExecutableEntry {
        key: key.clone(),
        fn_id: FnId(1),
    });
    let mut boundary = inventory_boundary(100, 2);
    boundary.members = Box::new([NativeConstructionMember {
        boundary: BoundaryId::for_test(0),
        target_fn: FnId(3),
        target: key,
        surface_inputs: Box::default(),
        capture_semantic_inputs: Box::default(),
        surface_semantic_inputs: Box::default(),
        target_inputs: Box::default(),
        target_return: BackendReturnLayout {
            layout: BackendValueLayout {
                structural: ShapeId::for_test(0),
                carrier: TransportCarrier::Absent,
                tys: Box::default(),
                reprs: Box::default(),
            },
            diverges: false,
        },
    }]);
    program.callable_boundaries.push(boundary);
    assert!(unreachable_native_functions(&program).is_empty());
    let mut dangling_entry = program.clone();
    dangling_entry.executable_entries[0].fn_id = FnId(99);
    assert!(std::panic::catch_unwind(|| unreachable_native_functions(&dangling_entry)).is_err());
    program.callable_boundaries[0].members[0].target_fn = FnId(99);
    assert!(std::panic::catch_unwind(|| unreachable_native_functions(&program)).is_err());
}

#[test]
fn native_inventory_distinguishes_ownership_from_executable_reachability() {
    let mut program = inventory_fixture(4);
    program.bodies[1].origin = NativeBodyOrigin::Continuation { owner: FnId(0) };
    assert_eq!(unreachable_native_functions(&program), vec![FnId(1), FnId(2), FnId(3)]);
}

#[test]
fn native_inventory_checks_bijections_and_owners_even_in_unreachable_bodies() {
    let mutations: &[fn(&mut NativeProgram)] = &[
        |program| program.module.fns.push(program.module.fns[0].clone()),
        |program| {
            program.module.fn_idx.remove(&FnId(1));
        },
        |program| {
            program.module.fn_idx.insert(FnId(1), 0);
        },
        |program| program.bodies.push(program.bodies[0].clone()),
        |program| {
            program.bodies.pop();
        },
        |program| program.bodies[1].fn_id = FnId(99),
        |program| program.bodies[1].origin = NativeBodyOrigin::Continuation { owner: FnId(99) },
        |program| program.entry = FnId(99),
    ];
    for (case, mutate) in mutations.iter().enumerate() {
        let mut program = inventory_fixture(2);
        mutate(&mut program);
        assert!(
            std::panic::catch_unwind(|| unreachable_native_functions(&program)).is_err(),
            "invalid inventory case {case} was accepted"
        );
    }
}

#[test]
fn native_inventory_roots_every_construction_word_even_in_unreachable_bodies() {
    use crate::fz_ir::{CallsiteIdent, Var};
    let mut program = inventory_fixture(6);
    program.callable_boundaries = (1..=4).map(|id| inventory_boundary(id + 100, id)).collect();
    program.module.fns[5].blocks[0].stmts = vec![
        Stmt::Let(Var(1), Prim::MakeFnRef(CallsiteIdent::synthetic(), FnId(101))),
        Stmt::Let(
            Var(2),
            Prim::MakeClosure(CallsiteIdent::synthetic(), FnId(102), Vec::new()),
        ),
        Stmt::Let(
            Var(3),
            Prim::ClosureCapture {
                closure: Var(2),
                constructions: Box::new([FnId(103), FnId(104)]),
                index: 0,
            },
        ),
    ];
    assert_eq!(unreachable_native_functions(&program), vec![FnId(5)]);
    for slot in 0..3 {
        let mut dangling = program.clone();
        let Stmt::Let(_, prim) = &mut dangling.module.fns[5].blocks[0].stmts[slot];
        match prim {
            Prim::MakeFnRef(_, id) | Prim::MakeClosure(_, id, _) => *id = FnId(99),
            Prim::ClosureCapture { constructions, .. } => constructions[0] = FnId(99),
            _ => unreachable!(),
        }
        assert!(std::panic::catch_unwind(|| unreachable_native_functions(&dangling)).is_err());
    }
}

#[test]
fn native_inventory_closes_calls_continuations_and_receive_outcomes_transitively() {
    use crate::dispatch_matrix::pattern::{SourcePatternRows, pattern_dispatch_from_source};
    use crate::fz_ir::{CallsiteIdent, Cont, DirectCallTarget, ReceiveAfter, ReceiveClause, Term, Var};
    use crate::source::Span;
    let mut program = inventory_fixture(8);
    program.module.fns[0].blocks[0].terminator = Term::Call {
        ident: CallsiteIdent::synthetic(),
        callee: DirectCallTarget::Local(FnId(1)),
        args: Vec::new(),
        continuation: Cont {
            fn_id: FnId(2),
            captured: Vec::new(),
        },
    };
    program.module.fns[1].blocks[0].terminator = Term::TailCall {
        ident: CallsiteIdent::synthetic(),
        callee: DirectCallTarget::Local(FnId(3)),
        args: Vec::new(),
        is_back_edge: false,
    };
    program.module.fns[2].blocks[0].terminator = Term::CallClosure {
        ident: CallsiteIdent::synthetic(),
        closure: Var(0),
        args: Vec::new(),
        continuation: Cont {
            fn_id: FnId(4),
            captured: Vec::new(),
        },
    };
    program.module.fns[3].blocks[0].terminator = Term::ReceiveMatched {
        ident: CallsiteIdent::synthetic(),
        clauses: vec![ReceiveClause {
            ident: CallsiteIdent::synthetic(),
            bound_names: Vec::new(),
            guard: Some(FnId(5)),
            body: FnId(6),
            span: Span::DUMMY,
        }],
        dispatch: std::sync::Arc::new(
            pattern_dispatch_from_source(SourcePatternRows {
                input_count: 1,
                rows: Vec::new(),
            })
            .unwrap(),
        ),
        after: Some(ReceiveAfter {
            ident: CallsiteIdent::synthetic(),
            timeout: Var(0),
            body: FnId(7),
            span: Span::DUMMY,
        }),
        pinned: Vec::new(),
        captures: Vec::new(),
    };
    assert!(unreachable_native_functions(&program).is_empty());
    // A control reference is invalid even when its containing function is dead.
    program.entry = FnId(7);
    program.module.fns[1].blocks[0].terminator = Term::TailCall {
        ident: CallsiteIdent::synthetic(),
        callee: DirectCallTarget::Local(FnId(99)),
        args: Vec::new(),
        is_back_edge: false,
    };
    assert!(std::panic::catch_unwind(|| unreachable_native_functions(&program)).is_err());
}
