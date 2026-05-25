use crate::ast::ModuleName;
use crate::fz_ir::{
    BlockId, Const, ExportId, ExportKey, FnBuilder, FnId, Module, ModuleBuilder, ModuleExport,
    Prim, Term,
};
use crate::ir_interp::{AnyValue, IrInterpRuntime};
use crate::lexer::Lexer;
use crate::parser::Parser;

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

fn lower_src(src: &str) -> Module {
    let toks = Lexer::new(src).tokenize().expect("lex");
    let prog = Parser::new(toks).parse_program().expect("parse");
    let mut ct = crate::types::ConcreteTypes;
    let prog = crate::resolve::flatten_modules(&mut ct, prog).expect("resolve");
    crate::ir_lower::lower_program(&mut ct, &prog).expect("lower")
}

fn drive_completion_i64(done: &[(u32, AnyValue)], pid: u32) -> Option<i64> {
    done.iter()
        .rev()
        .find_map(|(done_pid, value)| (*done_pid == pid).then(|| value.as_i64()).flatten())
}

fn route_tail_calls_to_export(module: &mut Module, export_key: ExportKey) {
    let export = module
        .exports
        .iter()
        .find(|export| export.key == export_key)
        .cloned()
        .expect("export");
    for function in &mut module.fns {
        for block in &mut function.blocks {
            if let Term::TailCall {
                ident,
                callee,
                args,
                ..
            } = &block.terminator
                && *callee == export.local_fn
            {
                block.terminator = Term::ExportTailCall {
                    ident: ident.clone(),
                    export: export.id,
                    args: args.clone(),
                };
            }
        }
    }
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

#[test]
fn blocked_local_call_resumes_in_original_code_image_after_replacement() {
    let v1 = lower_src(
        r#"
        fn helper(), do: 1

        fn wait_then_local() do
          receive()
          helper()
        end

        fn start_waiter() do
          spawn(fn () -> wait_then_local())
        end

        fn send_go(pid), do: send(pid, :go)
    "#,
    );
    let v2 = lower_src(
        r#"
        fn helper(), do: 2

        fn wait_then_local() do
          receive()
          helper()
        end

        fn start_waiter() do
          spawn(fn () -> wait_then_local())
        end

        fn send_go(pid), do: send(pid, :go)
    "#,
    );
    let start_waiter = v1.fn_by_name("start_waiter").expect("start_waiter").id;
    let send_go = v2.fn_by_name("send_go").expect("send_go").id;
    let mut runtime = IrInterpRuntime::fresh_with_root(&v1);

    runtime
        .enqueue_entry(&v1, 1, start_waiter, vec![])
        .expect("enqueue start_waiter");
    let blocked = runtime
        .drive_until_idle(&crate::telemetry::NullTelemetry, Some(1))
        .expect("drive blocked waiter");
    assert_eq!(drive_completion_i64(&blocked, 1), Some(2));

    runtime
        .enqueue_entry(&v2, 1, send_go, vec![AnyValue::Int(2)])
        .expect("enqueue sender from replacement image");
    let completions = runtime
        .drive_until_idle(&crate::telemetry::NullTelemetry, Some(1))
        .expect("drive sender and resumed waiter");

    assert_eq!(drive_completion_i64(&completions, 2), Some(1));
}

#[test]
fn blocked_exported_self_call_resolves_current_image_after_replacement() {
    let mut v1 = lower_src(
        r#"
        defmodule M do
          fn value(), do: 1
        end

        fn wait_then_export() do
          receive()
          M.value()
        end

        fn start_waiter() do
          spawn(fn () -> wait_then_export())
        end

        fn send_go(pid), do: send(pid, :go)
    "#,
    );
    let mut v2 = lower_src(
        r#"
        defmodule M do
          fn value(), do: 2
        end

        fn wait_then_export() do
          receive()
          M.value()
        end

        fn start_waiter() do
          spawn(fn () -> wait_then_export())
        end

        fn send_go(pid), do: send(pid, :go)
    "#,
    );
    let key = ExportKey {
        module: ModuleName::from_segments(vec!["M".to_string()]),
        name: "value".to_string(),
        arity: 0,
    };
    route_tail_calls_to_export(&mut v1, key.clone());
    route_tail_calls_to_export(&mut v2, key);
    let start_waiter = v1.fn_by_name("start_waiter").expect("start_waiter").id;
    let send_go = v2.fn_by_name("send_go").expect("send_go").id;
    let mut runtime = IrInterpRuntime::fresh_with_root(&v1);

    runtime
        .enqueue_entry(&v1, 1, start_waiter, vec![])
        .expect("enqueue start_waiter");
    let blocked = runtime
        .drive_until_idle(&crate::telemetry::NullTelemetry, Some(1))
        .expect("drive blocked waiter");
    assert_eq!(drive_completion_i64(&blocked, 1), Some(2));

    runtime
        .enqueue_entry(&v2, 1, send_go, vec![AnyValue::Int(2)])
        .expect("enqueue sender from replacement image");
    let completions = runtime
        .drive_until_idle(&crate::telemetry::NullTelemetry, Some(1))
        .expect("drive sender and resumed waiter");

    assert_eq!(drive_completion_i64(&completions, 2), Some(2));
}
