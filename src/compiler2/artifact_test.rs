use std::collections::HashMap;

use super::{AbiValueRepr, ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, ReturnAbi, RootId, Types};
use crate::compiler2::artifact::{EffectSummary, NativeBody, NativeBodyOrigin, NativeCallableEntry, NativeProgram};
use crate::fz_ir::{Block, BlockId, ExternMarshalSite, ExternTy, FnCategory, FnId, FnIr, Module, Term, Var};

#[test]
fn compiler2_native_program_contract_keeps_codegen_facts_on_body_records() {
    let mut types = Types::new();
    let int = types.int();
    let executable = ExecutableKey {
        activation: ActivationKey {
            root: RootId::from_u32(0),
            function: FunctionId::from_u32(0),
            input: vec![int],
        },
        need: ExecutableNeed::Value,
    };
    let entry_fn = FnId(0);
    let wrapper_fn = FnId(1);

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
            param_reprs: vec![AbiValueRepr::RawInt],
            return_ty: int,
            return_abi: ReturnAbi::Value(AbiValueRepr::RawInt),
            value_types: HashMap::from([(Var(0), int)]),
            extern_marshals: marshals.clone(),
            effects: EffectSummary::default(),
        }],
        callable_entries: vec![NativeCallableEntry {
            wrapper_fn,
            target_fn: entry_fn,
            target: executable.clone(),
            capture_count: 0,
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
        program.bodies[0].extern_marshals, marshals,
        "the body contract should carry concrete extern marshal classes inline for native codegen",
    );
    assert_eq!(
        program.callable_entries[0].target, executable,
        "callable-entry wrappers should point straight at the executable they expose",
    );
}
