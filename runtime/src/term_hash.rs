//! The hash of a published term, which agrees with the map key equality:
//! `TermComparator::compare(a, b, NumericMode::Strict) == Equal` implies
//! `hash(a) == hash(b)`.
//!
//! Equal terms hash equal whatever their representation. An inline bitstring,
//! a ProcBin and a ProcBin view over a longer buffer hash by bit length and
//! content, with the bits past the length left out. A tuple hashes by arity
//! and fields, never by its schema id. A map hashes by its entries as a set,
//! so a map built in any order, a trie and a named struct spelling the same
//! entries hash alike. An integer and a float never compare equal under strict
//! numbers, so they hash under different tags; a float hashes by its bits,
//! which strict comparison tells apart exactly.
//!
//! The hash is a function of the term and nothing the run chose. An atom
//! hashes by the hash of its name, which the atom table kept when the atom was
//! interned, and a closure by the hash of its source denotation, which the
//! node kept when it registered it. Neither depends on an id, so a map that
//! enumerates in hash order enumerates alike under the interpreter, `run` and
//! `build`, and from one run to the next.
//!
//! A comparator stops at two identical pointers; a hash cannot. A key built by
//! sharing substructure (each level of a tuple holding the one level below
//! twice) is a few objects that read as exponentially many, so a hash that
//! walked it as a tree would take exponential time. After `SHARED_WALK_BUDGET`
//! containers in one hash, the hasher remembers each container's hash by
//! address, and a container reached again costs a lookup.

use crate::any_value::{
    AnyValue, ListCons, ValueKind, closure_capture_value, closure_captured_count, closure_denotation,
    map_for_each_entry, struct_schema_id,
};
use crate::heap::{SchemaIdentity, SchemaRegistry};
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
use crate::process::Node;
use crate::resource::ResourceStub;
use crate::term::{Category, MapTerm, TermComparator, address, field_value};
use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::slice::from_raw_parts;

/// Containers one hash may walk before it starts remembering them.
const SHARED_WALK_BUDGET: u32 = 256;

const SALT_INT: u64 = 0x9e37_79b9_7f4a_7c15;
const SALT_ATOM: u64 = 0xc2b2_ae3d_27d4_eb4f;
const SALT_FLOAT: u64 = 0x1656_67b1_9e37_79f9;
const SALT_WORD: u64 = 0x2545_f491_4f6c_dd1d;
const SALT_TUPLE: u64 = 0x7001_e5a1_7000_0001;
const SALT_LIST: u64 = 0x1157_0000_0000_0001;
const SALT_MAP: u64 = 0x3a90_0000_0000_0001;
const SALT_CLOSURE: u64 = 0xc105_0000_0000_0001;
const SALT_RESOURCE: u64 = 0x7e57_0000_0000_0001;
const MULTIPLIER_A: u64 = 0x87c3_7b91_1142_53d5;
const MULTIPLIER_B: u64 = 0x4cf5_ad43_2745_937f;

/// MurmurHash3's 64-bit finalizer: a bijection with full avalanche.
#[inline(always)]
fn finalize(mut x: u64) -> u64 {
    x ^= x >> 33;
    x = x.wrapping_mul(0xff51_afd7_ed55_8ccd);
    x ^= x >> 33;
    x = x.wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    x ^ (x >> 33)
}

/// Fold `next` into the running hash, so the order of the parts matters.
#[inline(always)]
fn combine(hash: u64, next: u64) -> u64 {
    finalize(hash.rotate_left(27).wrapping_mul(5).wrapping_add(next ^ SALT_WORD))
}

/// A hash of `bytes`, eight at a time, in the manner of MurmurHash3's body.
fn bytes_hash(bytes: &[u8], seed: u64) -> u64 {
    let mut hash = seed ^ (bytes.len() as u64).wrapping_mul(MULTIPLIER_A);
    let (chunks, tail) = bytes.as_chunks::<8>();
    for chunk in chunks {
        let word = u64::from_le_bytes(*chunk);
        hash ^= word
            .wrapping_mul(MULTIPLIER_A)
            .rotate_left(31)
            .wrapping_mul(MULTIPLIER_B);
        hash = hash.rotate_left(27).wrapping_mul(5).wrapping_add(0x52dc_e729);
    }
    if !tail.is_empty() {
        let mut padded = [0u8; 8];
        padded[..tail.len()].copy_from_slice(tail);
        hash ^= u64::from_le_bytes(padded)
            .wrapping_mul(MULTIPLIER_A)
            .rotate_left(31)
            .wrapping_mul(MULTIPLIER_B);
    }
    finalize(hash)
}

/// The hash of a name: what the atom table keeps for an atom, and what a
/// closure's denotation hashes its label with.
pub fn name_hash(name: &str) -> u64 {
    bytes_hash(name.as_bytes(), SALT_ATOM)
}

/// One hash walk: the budget it has spent and, once it is spent, the
/// containers it has already hashed.
#[derive(Default)]
struct Walk {
    walked: Cell<u32>,
    remembered: RefCell<HashMap<usize, u64>>,
}

pub struct TermHasher<'a> {
    comparator: TermComparator<'a>,
    node: &'a Node,
    schemas: &'a SchemaRegistry,
}

impl<'a> TermHasher<'a> {
    pub fn new(node: &'a Node, schemas: &'a SchemaRegistry) -> Self {
        Self {
            comparator: TermComparator::new(node, schemas),
            node,
            schemas,
        }
    }

    /// The hash of `value`, a published language value.
    pub fn hash(&self, value: AnyValue) -> u64 {
        self.hash_in(value, &Walk::default())
    }

    #[inline]
    fn hash_in(&self, value: AnyValue, walk: &Walk) -> u64 {
        match value {
            AnyValue::Int(i) => finalize(i as u64 ^ SALT_INT),
            AnyValue::Atom(id) => finalize(self.node.atom_name_hash(id) ^ SALT_ATOM),
            AnyValue::Float(bits) => finalize(bits ^ SALT_FLOAT),
            AnyValue::Opaque(kind, word) => finalize(word ^ u64::from(kind.tag()).wrapping_mul(SALT_INT)),
            AnyValue::EmptyList => self.hash_list(std::ptr::null(), walk),
            _ => self.hash_container(value, walk),
        }
    }

    fn hash_container(&self, value: AnyValue, walk: &Walk) -> u64 {
        assert_ne!(value.kind(), ValueKind::NULL, "absent carrier is not a language value");
        if let Some(hash) = self.remembered(value, walk) {
            return hash;
        }
        let hash = match self.comparator.category(value) {
            Category::Tuple => self.hash_tuple(address(value), walk),
            Category::Bitstring => hash_bitstring(value.heap_object_word().expect("bitstring")),
            Category::List => self.hash_list(address(value), walk),
            Category::Map => self.hash_map(value, walk),
            Category::Closure => self.hash_closure(address(value), walk),
            Category::Resource => {
                let id = unsafe { ResourceStub::from_raw(address(value)) }.id();
                finalize(id.word() ^ SALT_RESOURCE)
            }
            Category::Number | Category::Atom | Category::Reference | Category::Pid => {
                unreachable!("scalars are hashed without a container walk")
            }
        };
        self.remember(value, hash, walk);
        hash
    }

    /// The hash an earlier part of this walk gave `value`, once the budget is
    /// spent.
    fn remembered(&self, value: AnyValue, walk: &Walk) -> Option<u64> {
        let walked = walk.walked.get();
        if walked < SHARED_WALK_BUDGET {
            walk.walked.set(walked + 1);
            return None;
        }
        walk.remembered.borrow().get(&(address(value) as usize)).copied()
    }

    fn remember(&self, value: AnyValue, hash: u64, walk: &Walk) {
        if walk.walked.get() >= SHARED_WALK_BUDGET {
            walk.remembered.borrow_mut().insert(address(value) as usize, hash);
        }
    }

    fn hash_tuple(&self, object: *const u8, walk: &Walk) -> u64 {
        let schema = self.schemas.get(unsafe { struct_schema_id(object) });
        let &SchemaIdentity::Tuple(arity) = &schema.identity else {
            panic!("internal storage schema is not a language value");
        };
        (0..arity).fold(finalize(arity as u64 ^ SALT_TUPLE), |hash, index| {
            combine(hash, self.hash_in(field_value(schema, object, index), walk))
        })
    }

    fn hash_list(&self, mut cell: *const u8, walk: &Walk) -> u64 {
        let mut hash = SALT_LIST;
        let mut length = 0u64;
        while !cell.is_null() {
            let cons = unsafe { &*cell.cast::<ListCons>() };
            hash = combine(hash, self.hash_in(cons.head_value(), walk));
            length += 1;
            cell = cons.tail_addr() as *const u8;
        }
        combine(hash, length)
    }

    /// A sum over the entries, so the order they are visited in does not
    /// matter: a map's entries are a set, and a flat map, a trie and a struct
    /// can spell the same one.
    fn hash_map(&self, value: AnyValue, walk: &Walk) -> u64 {
        let map = self.comparator.map_term(value);
        let count = self.comparator.map_count(map);
        let mut sum = 0u64;
        let mut add_entry = |key: AnyValue, value: AnyValue| {
            let entry = finalize(
                self.hash_in(key, walk) ^ self.hash_in(value, walk).rotate_left(23).wrapping_mul(MULTIPLIER_A),
            );
            sum = sum.wrapping_add(entry);
        };
        match map {
            MapTerm::Entries(addr) => unsafe { map_for_each_entry(addr, &mut add_entry) },
            MapTerm::Struct { .. } => {
                for index in 0..count {
                    add_entry(
                        self.comparator.map_key(map, index),
                        self.comparator.map_value(map, index),
                    );
                }
            }
        }
        combine(finalize(count as u64 ^ SALT_MAP), sum)
    }

    /// Equal closures have equal source denotations, whichever ids name them,
    /// and equal captures.
    fn hash_closure(&self, closure: *const u8, walk: &Walk) -> u64 {
        let denotation = self
            .node
            .closure_denotation_hash(unsafe { closure_denotation(closure) });
        let count = unsafe { closure_captured_count(closure) };
        let hash = (0..count).fold(combine(SALT_CLOSURE, denotation), |hash, index| {
            combine(
                hash,
                self.hash_in(unsafe { closure_capture_value(closure, index) }, walk),
            )
        });
        combine(hash, count as u64)
    }
}

/// By bit length and content; the bits of a last partial byte past the length
/// are not content.
fn hash_bitstring(word: u64) -> u64 {
    let bits = unsafe { bitstring_bit_len(word) } as usize;
    let bytes = unsafe { from_raw_parts(bitstring_byte_ptr(word), bits.div_ceil(8)) };
    let whole = bits / 8;
    let hash = bytes_hash(&bytes[..whole], bits as u64);
    if bits.is_multiple_of(8) {
        return hash;
    }
    let kept = u8::MAX << (8 - bits % 8);
    combine(hash, u64::from(bytes[whole] & kept))
}

#[cfg(test)]
#[path = "term_hash_test.rs"]
mod term_hash_test;
