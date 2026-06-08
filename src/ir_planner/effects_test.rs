use super::*;
use crate::fz_ir::{CallsiteIdent, ExternArg, ExternDecl, ExternId, ExternTy, Var};
use crate::type_expr::ResolvedSpecDecl;
use crate::types::Types;

fn module_with_extern(symbol: &str, ret: ExternTy) -> Module {
    let mut module = Module::new();
    module.extern_idx.insert(ExternId(0), 0);
    let mut types = crate::types::new();
    module.externs.push(ExternDecl {
        id: ExternId(0),
        fz_name: symbol.to_owned(),
        symbol: symbol.to_owned(),
        params: vec![ExternTy::Any],
        variadic: false,
        ret,
        ret_descr: types.any(),
        semantic_contract: ResolvedSpecDecl {
            params: vec![types.any()],
            result: types.any(),
            constraints: std::collections::HashMap::new(),
        },
    });
    module
}

#[test]
fn externs_are_observable_without_scheduler_effects_by_default() {
    let module = module_with_extern("user_extern", ExternTy::Any);
    let effects = prim_effects(
        &module,
        &Prim::Extern(
            CallsiteIdent::synthetic(),
            ExternId(0),
            vec![ExternArg::fixed(Var(0), ExternTy::Any)],
        ),
    );

    assert!(effects.observable);
    assert!(!effects.scheduler_visible);
}

#[test]
fn send_is_scheduler_visible() {
    let module = module_with_extern("fz_send", ExternTy::Unit);
    let effects = prim_effects(
        &module,
        &Prim::Extern(
            CallsiteIdent::synthetic(),
            ExternId(0),
            vec![ExternArg::fixed(Var(0), ExternTy::Any)],
        ),
    );

    assert!(effects.scheduler_visible);
    assert!(effects.observable);
}

#[test]
fn heap_stats_observes_allocation() {
    let module = module_with_extern("fz_process_heap_alloc_stats", ExternTy::Any);
    let effects = prim_effects(&module, &Prim::Extern(CallsiteIdent::synthetic(), ExternId(0), vec![]));

    assert!(effects.reads_allocation_stats);
    assert!(effects.observable);
}
