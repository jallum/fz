use super::fn_types::EffectSummary;
use crate::fz_ir::{Module, Prim, Term};

pub(crate) fn prim_effect_summary(m: &Module, prim: &Prim) -> EffectSummary {
    crate::ir_effects::prim_effects(m, prim).into()
}

pub(crate) fn term_local_effect_summary(term: &Term) -> EffectSummary {
    crate::ir_effects::term_effects(term).into()
}
