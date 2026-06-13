use std::collections::HashMap;

use super::identity::{FunctionMap, ModuleId, RootEntry, RootKind, RootMap};
use super::{AbiValueRepr, ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, ReturnAbi, RootId, Types};
use crate::compiler2::artifact::{
    EffectSummary, NativeBody, NativeBodyOrigin, NativeCallableBoundary, NativeCallableBoundaryId, NativeEntryAbi,
    NativeProgram,
};
use crate::fz_ir::{
    Block, BlockId, ExternDecl, ExternId, ExternMarshalSite, ExternTy, FnCategory, FnId, FnIr, Module, Term, Var,
};
use crate::type_expr::ResolvedSpecDecl;
use crate::types::Types as _;

fn stub_activation_key(_types: &mut Types, input: Vec<super::types::Ty>) -> (RootId, FunctionId, ActivationKey) {
    let mut functions = FunctionMap::new();
    let function = functions.reference(ModuleId::GLOBAL, "main", 0);
    let mut roots = RootMap::new();
    let root = roots.define(RootEntry {
        function,
        input: input.clone(),
        need: ExecutableNeed::Value,
        kind: RootKind::Runtime,
    });
    let activation = ActivationKey { root, function, input };
    (root, function, activation)
}

#[test]
fn compiler2_native_program_contract_keeps_codegen_facts_on_body_records() {
    let mut types = Types::new();
    let int = types.int();
    let (_, _, activation) = stub_activation_key(&mut types, vec![int]);
    let executable = ExecutableKey {
        activation,
        need: ExecutableNeed::Value,
    };
    let entry_fn = FnId(0);
    let identity_fn = FnId(1);

    let mut module = Module::default();
    module.fns.push(FnIr {
        id: entry_fn,
        name: "main".to_string(),
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
        ignored_entry_params: vec![false],
        physical_entry_params: Vec::new(),
        physical_capabilities: Vec::new(),
    });
    module.fn_idx.insert(entry_fn, 0);

    let marshals = HashMap::from([(
        ExternMarshalSite {
            block: BlockId(0),
            stmt_idx: 0,
            arg_idx: 0,
        },
        ExternTy::I64,
    )]);
    let program = NativeProgram {
        backend_revision: 7,
        entry: entry_fn,
        module,
        bodies: vec![NativeBody {
            fn_id: entry_fn,
            origin: NativeBodyOrigin::Executable(executable.clone()),
            entry_abi: NativeEntryAbi::Direct,
            param_reprs: vec![AbiValueRepr::RawInt],
            return_ty: int,
            return_abi: ReturnAbi::Value(AbiValueRepr::RawInt),
            value_types: HashMap::from([(Var(0), int)]),
            callable_value_boundaries: HashMap::from([(Var(0), vec![NativeCallableBoundaryId(entry_fn)])]),
            extern_marshals: marshals.clone(),
            effects: EffectSummary::default(),
        }],
        callable_boundaries: vec![NativeCallableBoundary {
            identity_fn,
            target_fn: entry_fn,
            target: executable.clone(),
            capture_count: 0,
            arg_reprs: vec![AbiValueRepr::RawInt],
            return_ty: int,
            return_abi: ReturnAbi::Value(AbiValueRepr::RawInt),
        }],
    };

    assert_eq!(
        program.entry, entry_fn,
        "the native handoff should name one CPS/native entry body"
    );
    assert_eq!(
        program.bodies[0].origin,
        NativeBodyOrigin::Executable(executable.clone()),
        "the body contract should keep executable identity on the body record instead of an external planner shell",
    );
    assert_eq!(
        program.bodies[0].entry_abi,
        NativeEntryAbi::Direct,
        "the body contract should say whether a body is a direct entry or a continuation entry",
    );
    assert_eq!(
        program.bodies[0].callable_value_boundaries.get(&Var(0)),
        Some(&vec![NativeCallableBoundaryId(entry_fn)]),
        "closure-producing vars should point at the closed callable-boundary inventory instead of hiding that resolution in codegen",
    );
    assert_eq!(
        program.bodies[0].extern_marshals, marshals,
        "the body contract should carry concrete extern marshal classes inline for native codegen",
    );
    assert_eq!(
        program.callable_boundaries[0].identity_fn, identity_fn,
        "callable boundaries should carry a callable identity for closure construction sites",
    );
    assert_eq!(
        program.callable_boundaries[0].target, executable,
        "callable boundaries should point straight at the executable they expose",
    );
}

#[test]
fn compiler2_native_program_contract_maps_old_native_inputs_to_local_facts() {
    let mut types = Types::new();
    let int = types.int();
    let (_, _, activation) = stub_activation_key(&mut types, vec![int]);
    let executable = ExecutableKey {
        activation,
        need: ExecutableNeed::Value,
    };
    let entry_fn = FnId(0);
    let cont_fn = FnId(1);
    let identity_fn = FnId(2);

    let mut legacy_types = crate::types::new();
    let mut module = Module::default();
    module.externs.push(ExternDecl {
        id: ExternId(0),
        fz_name: "libc::open".to_string(),
        symbol: "open".to_string(),
        params: vec![ExternTy::CString, ExternTy::I64],
        variadic: true,
        ret: ExternTy::I64,
        ret_descr: legacy_types.any(),
        semantic_contract: ResolvedSpecDecl {
            params: vec![legacy_types.any(), legacy_types.any()],
            result: legacy_types.any(),
            constraints: HashMap::new(),
        },
    });
    module.extern_idx.insert(ExternId(0), 0);
    module.fns.push(FnIr {
        id: entry_fn,
        name: "main".to_string(),
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
        ignored_entry_params: vec![false],
        physical_entry_params: Vec::new(),
        physical_capabilities: Vec::new(),
    });
    module.fn_idx.insert(entry_fn, 0);
    module.fns.push(FnIr {
        id: cont_fn,
        name: "main__k0".to_string(),
        frame_schema_id: 0,
        blocks: vec![Block {
            id: BlockId(1),
            params: vec![Var(1)],
            stmts: Vec::new(),
            terminator: Term::Return(Var(1)),
        }],
        entry: BlockId(1),
        category: FnCategory::CpsCont,
        owner_module: String::new(),
        ignored_entry_params: vec![false],
        physical_entry_params: Vec::new(),
        physical_capabilities: Vec::new(),
    });
    module.fn_idx.insert(cont_fn, 1);

    let extern_site = ExternMarshalSite {
        block: BlockId(0),
        stmt_idx: 0,
        arg_idx: 0,
    };
    let program = NativeProgram {
        backend_revision: 7,
        entry: entry_fn,
        module,
        bodies: vec![
            NativeBody {
                fn_id: entry_fn,
                origin: NativeBodyOrigin::Executable(executable.clone()),
                entry_abi: NativeEntryAbi::Direct,
                param_reprs: vec![AbiValueRepr::RawInt],
                return_ty: int,
                return_abi: ReturnAbi::Value(AbiValueRepr::RawInt),
                value_types: HashMap::from([(Var(0), int)]),
                callable_value_boundaries: HashMap::from([(Var(0), vec![NativeCallableBoundaryId(entry_fn)])]),
                extern_marshals: HashMap::from([(extern_site, ExternTy::CString)]),
                effects: EffectSummary::default(),
            },
            NativeBody {
                fn_id: cont_fn,
                origin: NativeBodyOrigin::Continuation {
                    owner: entry_fn,
                    index: 0,
                },
                entry_abi: NativeEntryAbi::Continuation { extra_params: 1 },
                param_reprs: vec![AbiValueRepr::ValueRef],
                return_ty: int,
                return_abi: ReturnAbi::Value(AbiValueRepr::ValueRef),
                value_types: HashMap::from([(Var(1), int)]),
                callable_value_boundaries: HashMap::new(),
                extern_marshals: HashMap::new(),
                effects: EffectSummary::default(),
            },
        ],
        callable_boundaries: vec![NativeCallableBoundary {
            identity_fn,
            target_fn: entry_fn,
            target: executable.clone(),
            capture_count: 0,
            arg_reprs: vec![AbiValueRepr::RawInt],
            return_ty: int,
            return_abi: ReturnAbi::Value(AbiValueRepr::RawInt),
        }],
    };

    assert_eq!(
        program.entry, entry_fn,
        "native codegen should read the root entry directly from NativeProgram instead of SpecRegistry or reachable-spec tables",
    );
    assert_eq!(
        program.module.fns.len(),
        2,
        "native codegen should read the prepared CPS/native body inventory directly from NativeProgram.module instead of a rebuilt prepared Module shell",
    );
    assert_eq!(
        program.bodies[0].return_ty, int,
        "native codegen should read effective return types from NativeBody.return_ty instead of ModulePlan.effective_returns",
    );
    assert_eq!(
        program.bodies[0].return_abi,
        ReturnAbi::Value(AbiValueRepr::RawInt),
        "native codegen should read return-lane contracts from NativeBody.return_abi instead of re-deriving them through planner state",
    );
    assert_eq!(
        program.bodies[0].value_types.get(&Var(0)),
        Some(&int),
        "native codegen should read per-value type answers from NativeBody.value_types instead of SpecPlan.vars",
    );
    assert_eq!(
        program.bodies[0].callable_value_boundaries.get(&Var(0)),
        Some(&vec![NativeCallableBoundaryId(entry_fn)]),
        "native codegen should read callable-boundary obligations from NativeBody.callable_value_boundaries instead of planner-side callable lookup",
    );
    assert_eq!(
        program.callable_boundaries[0].target, executable,
        "native codegen should read callable-boundary inventory from NativeProgram.callable_boundaries instead of PlannedProgram.callable_entries",
    );
    assert_eq!(
        program.module.externs[0].symbol, "open",
        "native codegen should read extern declarations from NativeProgram.module instead of a rebuilt prepared Module input",
    );
    assert_eq!(
        program.bodies[0].extern_marshals.get(&extern_site),
        Some(&ExternTy::CString),
        "native codegen should read concrete extern wire classes from NativeBody.extern_marshals instead of AbiFacts or planner recomputation",
    );
    assert_eq!(
        program.bodies[1].entry_abi,
        NativeEntryAbi::Continuation { extra_params: 1 },
        "native codegen should classify continuation entries from NativeBody.entry_abi instead of cont_fns or cont_extras_count side tables",
    );
    assert_eq!(
        program.bodies[1].origin,
        NativeBodyOrigin::Continuation {
            owner: entry_fn,
            index: 0
        },
        "native codegen should recover helper ownership from NativeBody.origin instead of planner reachability metadata",
    );
}

#[test]
fn compiler2_native_program_contract_treats_old_extern_semantics_as_cleanup_not_authority() {
    let mut types = Types::new();
    let int = types.int();
    let (_, _, stub_activation) = stub_activation_key(&mut types, vec![int]);
    let entry_fn = FnId(0);

    let mut legacy_types = crate::types::new();
    let mut module = Module::default();
    module.externs.push(ExternDecl {
        id: ExternId(0),
        fz_name: "libc::puts".to_string(),
        symbol: "puts".to_string(),
        params: vec![ExternTy::CString],
        variadic: false,
        ret: ExternTy::I64,
        ret_descr: legacy_types.any(),
        semantic_contract: ResolvedSpecDecl {
            params: vec![legacy_types.any()],
            result: legacy_types.any(),
            constraints: HashMap::new(),
        },
    });
    module.extern_idx.insert(ExternId(0), 0);
    module.fns.push(FnIr {
        id: entry_fn,
        name: "main".to_string(),
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
        ignored_entry_params: vec![false],
        physical_entry_params: Vec::new(),
        physical_capabilities: Vec::new(),
    });
    module.fn_idx.insert(entry_fn, 0);

    let marshal_site = ExternMarshalSite {
        block: BlockId(0),
        stmt_idx: 0,
        arg_idx: 0,
    };
    let program = NativeProgram {
        backend_revision: 7,
        entry: entry_fn,
        module,
        bodies: vec![NativeBody {
            fn_id: entry_fn,
            origin: NativeBodyOrigin::Executable(ExecutableKey {
                activation: stub_activation,
                need: ExecutableNeed::Value,
            }),
            entry_abi: NativeEntryAbi::Direct,
            param_reprs: vec![AbiValueRepr::RawInt],
            return_ty: int,
            return_abi: ReturnAbi::Value(AbiValueRepr::RawInt),
            value_types: HashMap::from([(Var(0), int)]),
            callable_value_boundaries: HashMap::new(),
            extern_marshals: HashMap::from([(marshal_site, ExternTy::CString)]),
            effects: EffectSummary::default(),
        }],
        callable_boundaries: Vec::new(),
    };

    assert_eq!(
        program.module.externs[0].semantic_contract.result,
        legacy_types.any(),
        "shared fz-IR still carries old extern semantic payloads during the fork",
    );
    assert_eq!(
        program.bodies[0].extern_marshals.get(&marshal_site),
        Some(&ExternTy::CString),
        "compiler2-native codegen must treat NativeBody.extern_marshals as authority and old ExternDecl semantics as cleanup-only baggage",
    );
}
