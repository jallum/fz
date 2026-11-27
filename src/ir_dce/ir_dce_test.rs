use super::*;
use crate::fz_ir::{Const, FnBuilder, FnId, Prim};

/// Intent: a value that only travels through block parameters nothing reads is
/// dead, however many blocks it passes through, and one a later block reads is
/// live all the way back to where it was made.
#[test]
fn a_value_forwarded_only_to_unread_block_parameters_is_dead() {
    let mut b = FnBuilder::new(FnId(0), "forwards");
    let entry = b.block(vec![]);
    let (read_param, dropped_param) = (b.fresh_var(), b.fresh_var());
    let join = b.block(vec![read_param, dropped_param]);
    let (kept, forgotten) = (
        b.let_(entry, Prim::Const(Const::Int(1))),
        b.let_(entry, Prim::Const(Const::Int(2))),
    );
    b.set_terminator(entry, crate::fz_ir::Term::Goto(join, vec![kept, forgotten]));
    b.set_terminator(join, crate::fz_ir::Term::Return(read_param));
    let f = b.build();

    let live = live_vars(&f);
    assert!(live.contains(&kept), "read through its parameter");
    assert!(!live.contains(&forgotten), "forwarded to a parameter nothing reads");
    assert!(
        classify_var_uses(&f).1.contains(&forgotten),
        "the argument list alone counts it as used, which is why liveness is its own question"
    );
}

/// Intent: a chain of forwards is followed to its end, in either order the
/// blocks were made in.
#[test]
fn liveness_follows_a_chain_of_forwards_to_the_read() {
    let mut b = FnBuilder::new(FnId(0), "chain");
    let entry = b.block(vec![]);
    let (last_param, middle_param) = (b.fresh_var(), b.fresh_var());
    let last = b.block(vec![last_param]);
    let middle = b.block(vec![middle_param]);
    let made = b.let_(entry, Prim::Const(Const::Int(1)));
    b.set_terminator(entry, crate::fz_ir::Term::Goto(middle, vec![made]));
    b.set_terminator(middle, crate::fz_ir::Term::Goto(last, vec![middle_param]));
    b.set_terminator(last, crate::fz_ir::Term::Return(last_param));
    let live = live_vars(&b.build());
    assert!(live.contains(&made) && live.contains(&middle_param));
}
