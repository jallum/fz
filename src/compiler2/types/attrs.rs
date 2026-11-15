//! The context-free facts about a type, computed once when it is interned.
//!
//! A [`Ty`] never changes meaning and its children are interned before it, so
//! a fact that follows from the children's facts and the descriptor alone is
//! settled the moment the descriptor is stored. Walkers read it through
//! [`TyCtx`](super::TyCtx) in one byte read where a recursion would revisit
//! every shared child once per parent.
//!
//! An attribute is a function of the descriptor and its children's attributes
//! only. Nothing mutable, such as which closures the world has registered, may
//! feed one: it would go stale where the descriptor does not.

use super::children::ChildRole;
use super::descr::Descr;

#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub(super) struct TyAttrs(u8);

/// A type variable occurs somewhere, a closure literal's own arrow included.
const HAS_VARS: u8 = 1;
/// A type variable that evidence still has to solve occurs somewhere: every
/// variable except those in a closure literal's own arrow.
const HAS_OPEN_VARS: u8 = 2;
/// A closure literal occurs somewhere.
const MENTIONS_CLOSURE_LITERAL: u8 = 4;
/// A list, callable or variable occurs somewhere: the leaves a structural
/// address can be minted at.
const HAS_ADDRESS_LEAF: u8 = 8;
/// A finite atom set that is neither empty nor all atoms occurs somewhere a
/// value can sit.
const NAMES_A_LITERAL: u8 = 16;

impl TyAttrs {
    /// Whether any type variable occurs at any depth.
    pub(super) fn has_vars(self) -> bool {
        self.0 & HAS_VARS != 0
    }

    /// Whether a type variable evidence still has to solve occurs at any depth.
    /// A closure literal's own arrow binds its variables; its captures do not.
    pub(super) fn has_open_vars(self) -> bool {
        self.0 & HAS_OPEN_VARS != 0
    }

    /// Whether a closure literal occurs at any depth.
    pub(super) fn mentions_closure_literal(self) -> bool {
        self.0 & MENTIONS_CLOSURE_LITERAL != 0
    }

    /// Whether the type has no list, callable or variable at any depth, so no
    /// structural address is ever minted below it.
    pub(super) fn path_free(self) -> bool {
        self.0 & HAS_ADDRESS_LEAF == 0
    }

    /// Whether no specific atom occurs at any depth a value can sit in. A
    /// callable's arguments and result are its surface, not a value.
    pub(super) fn literal_blind(self) -> bool {
        self.0 & NAMES_A_LITERAL == 0
    }
}

/// The attributes of a descriptor whose children are all interned, `attrs`
/// indexed by their handles.
pub(super) fn attrs_of(attrs: &[TyAttrs], d: &Descr) -> TyAttrs {
    let mut bits = 0;
    if !d.vars.values.is_empty() {
        bits |= HAS_VARS | HAS_OPEN_VARS;
    }
    if !d.vars.is_none() || !d.lists.is_empty() || !d.funcs.is_empty() {
        bits |= HAS_ADDRESS_LEAF;
    }
    let empty = d.looks_empty();
    if !empty && !d.atoms.is_none() && !d.atoms.is_any() {
        bits |= NAMES_A_LITERAL;
    }
    for (child, role) in d.children() {
        let child = attrs[child.0 as usize].0;
        bits |= child & (HAS_VARS | MENTIONS_CLOSURE_LITERAL | HAS_ADDRESS_LEAF);
        if role != ChildRole::LiteralSurface {
            bits |= child & HAS_OPEN_VARS;
        }
        if role == ChildRole::LiteralSurface {
            bits |= MENTIONS_CLOSURE_LITERAL;
        }
        let holds_a_value = matches!(
            role,
            ChildRole::Value | ChildRole::StructModule | ChildRole::Capture { .. }
        );
        if holds_a_value && !empty {
            bits |= child & NAMES_A_LITERAL;
        }
    }
    TyAttrs(bits)
}
