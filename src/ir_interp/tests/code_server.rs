use crate::ast::ModuleName;
use crate::fz_ir::{
    BlockId, Const, ExportId, ExportKey, FnBuilder, FnId, Module, ModuleBuilder, ModuleExport,
    Prim, Term,
};
use crate::ir_interp::IrInterpRuntime;

fn module_name() -> ModuleName {
    ModuleName::from_segments(vec!["M".to_string()])
}

fn export_key() -> ExportKey {
    ExportKey {
        module: module_name(),
        name: "val".to_string(),
        arity: 0,
    }
}

fn versioned_module(value: i64) -> (Module, FnId) {
    let val_id = FnId(0);
    let caller_id = FnId(1);

    let mut val = FnBuilder::new(val_id, "M.val");
    let val_entry = val.block(vec![]);
    let const_v = val.let_(val_entry, Prim::Const(Const::Int(value)));
    val.set_terminator(val_entry, Term::Return(const_v));

    let mut caller = FnBuilder::new(caller_id, "M.call_export");
    let caller_entry: BlockId = caller.block(vec![]);
    caller.set_terminator(
        caller_entry,
        Term::ExportTailCall {
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            export: ExportId(0),
            args: vec![],
        },
    );

    let mut mb = ModuleBuilder::new();
    mb.add_fn(val.build());
    mb.add_fn(caller.build());
    let mut module = mb.build();
    module.exports.push(ModuleExport {
        id: ExportId(0),
        key: export_key(),
        local_fn: val_id,
    });
    module.export_idx.insert(ExportId(0), 0);
    (module, caller_id)
}

#[test]
fn exported_tail_call_enters_current_code_server_image() {
    let (v1, _) = versioned_module(1);
    let (v2, caller_id) = versioned_module(2);
    let mut runtime = IrInterpRuntime::fresh_with_root(&v1);

    runtime
        .enqueue_entry(&v2, 1, caller_id, vec![])
        .expect("enqueue caller");
    let completions = runtime
        .drive_until_idle(&crate::telemetry::NullTelemetry, Some(1))
        .expect("drive");
    let value = completions
        .into_iter()
        .find_map(|(pid, value)| (pid == 1).then_some(value))
        .expect("pid 1 completion");
    assert!(matches!(value, crate::ir_interp::AnyValue::Int(2)));
}
