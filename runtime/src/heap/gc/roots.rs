//! The references a collection forwards where they live.

use super::forward::Tracer;
use crate::any_value::AnyValueRef;

/// Moves the references a collection's roots hold: each is forwarded in place,
/// so a root holds its forwarded value as soon as `forward` returns.
pub struct RootForwarder<'t, 'a> {
    tracer: &'t mut Tracer<'a>,
}

impl<'t, 'a> RootForwarder<'t, 'a> {
    pub(in super::super) fn new(tracer: &'t mut Tracer<'a>) -> Self {
        Self { tracer }
    }

    /// Forward `root`. A root that is not a pointer into the from-space (a
    /// scalar immediate, the empty list, a static closure or halt continuation,
    /// a pointer into an old block a minor collection leaves) is left as it
    /// was.
    pub fn forward(&mut self, root: &mut AnyValueRef) {
        self.tracer.forward_root(root);
    }
}

/// Everything a holder keeps into a heap, which a collection forwards in
/// place: the holder hands each reference it owns to the forwarder, in a fixed
/// order, and no list of them is made.
pub trait Roots {
    fn forward_into(&mut self, forwarder: &mut RootForwarder<'_, '_>);
}

impl Roots for [AnyValueRef] {
    fn forward_into(&mut self, forwarder: &mut RootForwarder<'_, '_>) {
        for root in self {
            forwarder.forward(root);
        }
    }
}

impl<const N: usize> Roots for [AnyValueRef; N] {
    fn forward_into(&mut self, forwarder: &mut RootForwarder<'_, '_>) {
        self.as_mut_slice().forward_into(forwarder);
    }
}

impl Roots for Vec<AnyValueRef> {
    fn forward_into(&mut self, forwarder: &mut RootForwarder<'_, '_>) {
        self.as_mut_slice().forward_into(forwarder);
    }
}
