//! The one traversal of a descriptor's child types.
//!
//! A descriptor names its children on five axes: tuple fields, list elements,
//! resource payloads, record values, and an arrow's arguments, result and
//! closure captures. Every walk over interned types asks this module for them,
//! so no walker restates which positions a descriptor has.

use crate::fz_ir::FnId;

use super::descr::Descr;
use super::sigs::ArrowSig;
use super::{CallableValueKind, Ty, is_struct_module_key};

/// What a child type is to the descriptor that names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ChildRole {
    /// A value the descriptor holds: a tuple field, list element, resource
    /// payload or record value.
    Value,
    /// The record value under the struct-module key: a module name, not data.
    StructModule,
    /// An argument or result of an ordinary arrow: the surface of a callable.
    Surface,
    /// An argument or result of a closure literal's arrow. Its variables belong
    /// to the closure.
    LiteralSurface,
    /// A value a closure literal captured, with the closure that holds it.
    Capture {
        kind: CallableValueKind,
        fn_id: Option<FnId>,
    },
}

impl Descr {
    /// Every child type, each with its role.
    pub(super) fn children(&self) -> impl Iterator<Item = (Ty, ChildRole)> + '_ {
        let tuples = self
            .tuples
            .iter()
            .flat_map(|c| c.sigs())
            .flat_map(|sig| sig.elems.iter().map(|ty| (*ty, ChildRole::Value)));
        let lists = self
            .lists
            .iter()
            .flat_map(|c| c.sigs())
            .filter_map(|sig| sig.elem.map(|ty| (ty, ChildRole::Value)));
        let resources = self
            .resources
            .iter()
            .flat_map(|c| c.sigs())
            .map(|sig| (sig.payload, ChildRole::Value));
        let maps = self.maps.iter().flat_map(|c| c.sigs()).flat_map(|sig| {
            sig.fields.iter().map(|(key, ty)| {
                let role = if is_struct_module_key(key) {
                    ChildRole::StructModule
                } else {
                    ChildRole::Value
                };
                (*ty, role)
            })
        });
        let funcs = self.funcs.iter().flat_map(|c| c.sigs()).flat_map(|sig| {
            let surface = surface_role(sig);
            let captures = sig.lit.iter().flat_map(|lit| {
                lit.captures.iter().map(move |ty| {
                    (
                        *ty,
                        ChildRole::Capture {
                            kind: lit.kind,
                            fn_id: lit.fn_id,
                        },
                    )
                })
            });
            sig.args
                .iter()
                .chain(std::iter::once(&sig.ret))
                .map(move |ty| (*ty, surface))
                .chain(captures)
        });
        tuples.chain(lists).chain(resources).chain(maps).chain(funcs)
    }

    /// Replace every child type by what `f` makes of it, in place.
    pub(super) fn map_children(&mut self, f: &mut impl FnMut(Ty, ChildRole) -> Ty) {
        for sig in self.tuples.iter_mut().flat_map(|c| c.sigs_mut()) {
            sig.elems.iter_mut().for_each(|ty| *ty = f(*ty, ChildRole::Value));
        }
        for sig in self.lists.iter_mut().flat_map(|c| c.sigs_mut()) {
            if let Some(ty) = &mut sig.elem {
                *ty = f(*ty, ChildRole::Value);
            }
        }
        for sig in self.resources.iter_mut().flat_map(|c| c.sigs_mut()) {
            sig.payload = f(sig.payload, ChildRole::Value);
        }
        for sig in self.maps.iter_mut().flat_map(|c| c.sigs_mut()) {
            for (key, ty) in sig.fields.iter_mut() {
                let role = if is_struct_module_key(key) {
                    ChildRole::StructModule
                } else {
                    ChildRole::Value
                };
                *ty = f(*ty, role);
            }
        }
        for sig in self.funcs.iter_mut().flat_map(|c| c.sigs_mut()) {
            let surface = surface_role(sig);
            sig.args.iter_mut().for_each(|ty| *ty = f(*ty, surface));
            sig.ret = f(sig.ret, surface);
            if let Some(lit) = &mut sig.lit {
                let role = ChildRole::Capture {
                    kind: lit.kind,
                    fn_id: lit.fn_id,
                };
                lit.captures.iter_mut().for_each(|ty| *ty = f(*ty, role));
            }
        }
    }
}

fn surface_role(sig: &ArrowSig) -> ChildRole {
    if sig.lit.is_some() {
        ChildRole::LiteralSurface
    } else {
        ChildRole::Surface
    }
}
