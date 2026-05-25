use super::*;
use crate::ast::FnClause;
use crate::fz_ir::{
    BlockId, Var,
};

/// fz-ty1.9 — Emit TypeTest guards for `fn f(x :: T)` parameter annotations.
/// For each param that has a type annotation, emit a `TypeTest(pv, descr)`
/// stmt and branch: pass → continue to next block, fail → `on_fail` block.
pub(crate) fn emit_param_type_guards<T: crate::types::Types<Ty = crate::types::Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    clause: &FnClause,
    param_vars: &[Var],
    on_fail: BlockId,
) -> Result<(), LowerError> {
    debug_assert_eq!(
        param_vars.len(),
        clause.param_annotations.len(),
        "param/annotation length mismatch"
    );
    for (pv, type_toks_opt) in param_vars.iter().zip(&clause.param_annotations) {
        let toks = match type_toks_opt {
            Some(tt) => &tt.0,
            None => continue,
        };
        let ty = match crate::type_expr::parse_type_expr(t, toks, &ctx.combined_type_env) {
            Ok((ty, _)) => ty,
            Err(_) => continue,
        };
        let tt_var = ctx.let_(crate::fz_ir::Prim::TypeTest(*pv, Box::new(ty)));
        let pass_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(tt_var, pass_b, on_fail);
        ctx.cur_block = Some(pass_b);
        ctx.terminated = false;
    }
    Ok(())
}
