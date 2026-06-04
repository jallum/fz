use std::mem;

use crate::types::Types;

use super::{InternedConcreteTypes, InternedTy};

#[test]
fn ty_is_an_integer_handle() {
    assert_eq!(mem::size_of::<InternedTy>(), mem::size_of::<u32>());
}

#[test]
fn factory_interns_equal_descriptors() {
    let mut t = InternedConcreteTypes::new();
    assert_eq!(t.int(), t.int());
    let a = t.int();
    let lhs = t.tuple(&[a]);
    let rhs = t.tuple(&[a]);
    assert_eq!(lhs, rhs);
}

#[test]
fn structural_children_are_interned_handles() {
    let mut t = InternedConcreteTypes::new();
    let elem = t.int();
    let tuple = t.tuple(&[elem]);
    let d = t.descr(&tuple);
    assert_eq!(d.tuples[0].pos[0].elems, vec![elem]);
}
