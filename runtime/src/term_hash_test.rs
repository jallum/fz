use super::*;
use crate::any_value::{
    AnyValueRef, ClosureDenotationId, ValueKind, closure_addr_from_tagged, closure_capture_set, map_header_is_trie,
};
use crate::function_denotation::FunctionDenotation;
use crate::heap::{Heap, Schema};
use crate::module_name::ModuleName;
use crate::procbin::{SharedBinHandle, alloc_procbin};
use crate::term::NumericMode;
use std::cmp::Ordering;
use std::rc::Rc;
use std::sync::Arc;

/// A deterministic stream of numbers: the same seed makes the same terms.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

struct World {
    heap: Heap,
    node: Rc<Node>,
    tuples: Vec<u32>,
    point: u32,
}

/// A heap with tuples of arity 0..4, `%Pt{x, y}`, and closure denotations
/// `f0..f2` each registered under two ids (`k` and `100 + k`).
fn world() -> World {
    let schemas = Rc::new(std::cell::RefCell::new(SchemaRegistry::new()));
    let node = Rc::new(Node::empty());
    let heap = Heap::with_node(4096, schemas, Rc::clone(&node));
    let tuples = (0..4)
        .map(|arity| heap.register_schema(Schema::tuple_of_arity(arity)))
        .collect();
    let point = heap.register_schema(Schema::named_struct(
        ModuleName::from_segments(vec!["Pt".to_string()]),
        ["x".to_string(), "y".to_string()],
    ));
    for k in 0..3u32 {
        for id in [k, 100 + k] {
            node.register_closure_denotation(
                ClosureDenotationId::user(id),
                Arc::new(FunctionDenotation::named(None, format!("f{k}"), 0)),
            );
        }
    }
    World {
        heap,
        node,
        tuples,
        point,
    }
}

fn heap_value(bits: u64) -> AnyValue {
    AnyValue::decode_tagged_heap_bits(bits).expect("a heap value")
}

impl World {
    fn atom(&self, name: &str) -> AnyValue {
        AnyValue::atom(self.node.intern_atom(name))
    }

    fn hash(&self, value: AnyValue) -> u64 {
        let schemas = self.heap.schemas.borrow();
        TermHasher::new(&self.node, &schemas).hash(value)
    }

    fn compare(&self, a: AnyValue, b: AnyValue) -> Ordering {
        let schemas = self.heap.schemas.borrow();
        TermComparator::new(&self.node, &schemas).compare(a, b, NumericMode::Strict)
    }

    fn tuple(&mut self, fields: &[AnyValue]) -> AnyValue {
        let object = self.heap.alloc_struct(self.tuples[fields.len()]);
        for (i, field) in fields.iter().enumerate() {
            unsafe { self.heap.write_field_slot(object, (i * 8) as u32, *field) };
        }
        AnyValue::heap_ptr(object, ValueKind::STRUCT)
    }

    /// A random term. `variant` changes only how equal terms are represented,
    /// so one seed with either variant yields terms that compare equal.
    fn term(&mut self, rng: &mut Rng, depth: u32, variant: bool) -> AnyValue {
        match rng.below(if depth == 0 { 4 } else { 10 }) {
            0 => AnyValue::int(rng.below(8) as i64 - 4),
            1 => AnyValue::float([0.0, -0.0, 1.0, 2.5][rng.below(4) as usize]),
            2 => self.atom(&format!("a{}", rng.below(6))),
            3 => self.binary(rng, variant),
            4 => {
                let fields: Vec<_> = (0..rng.below(4)).map(|_| self.term(rng, depth - 1, variant)).collect();
                self.tuple(&fields)
            }
            5 => self.list(rng, depth, variant),
            6 => self.map(rng, depth, variant),
            7 => self.point_or_its_map(rng, variant),
            8 => self.closure(rng, depth, variant),
            _ => {
                let word = rng.below(4);
                let kind = if rng.below(2) == 0 {
                    ValueKind::PID
                } else {
                    ValueKind::REF
                };
                AnyValue::Opaque(kind, word)
            }
        }
    }

    fn list(&mut self, rng: &mut Rng, depth: u32, variant: bool) -> AnyValue {
        let mut list = crate::any_value::EMPTY_LIST_BITS;
        for _ in 0..rng.below(4) {
            let head = self.term(rng, depth - 1, variant);
            list = self.heap.alloc_list_cons_slot(head, list);
        }
        if list == crate::any_value::EMPTY_LIST_BITS {
            AnyValue::EmptyList
        } else {
            heap_value(list)
        }
    }

    /// A map of up to a few entries, rarely one big enough to be a trie. The
    /// variant lists the entries in the opposite order.
    fn map(&mut self, rng: &mut Rng, depth: u32, variant: bool) -> AnyValue {
        let count = if rng.below(8) == 0 {
            33 + rng.below(8)
        } else {
            rng.below(5)
        };
        let mut entries: Vec<(AnyValue, AnyValue)> = Vec::new();
        for _ in 0..count {
            let (key, value) = (self.term(rng, depth - 1, variant), self.term(rng, depth - 1, variant));
            if entries
                .iter()
                .all(|&(seen, _)| self.compare(seen, key) != Ordering::Equal)
            {
                entries.push((key, value));
            }
        }
        if variant {
            entries.reverse();
        }
        heap_value(self.heap.alloc_map_slots(&entries))
    }

    /// `%Pt{x: x, y: y}` as a struct, or as the map spelling the same entries.
    fn point_or_its_map(&mut self, rng: &mut Rng, variant: bool) -> AnyValue {
        let (x, y) = (rng.below(3) as i64, rng.below(3) as i64);
        if variant {
            let entries = [
                (self.atom("y"), AnyValue::int(y)),
                (self.atom("__struct__"), self.atom("Elixir.Pt")),
                (self.atom("x"), AnyValue::int(x)),
            ];
            return heap_value(self.heap.alloc_map_slots(&entries));
        }
        let object = self.heap.alloc_struct(self.point);
        unsafe {
            self.heap.write_field_slot(object, 0, AnyValue::int(x));
            self.heap.write_field_slot(object, 8, AnyValue::int(y));
        }
        AnyValue::heap_ptr(object, ValueKind::STRUCT)
    }

    /// A closure over denotation `f{k}`; the variant names it by another id.
    fn closure(&mut self, rng: &mut Rng, depth: u32, variant: bool) -> AnyValue {
        let k = rng.below(3) as u32;
        let id = ClosureDenotationId::user(if variant { 100 + k } else { k });
        let captured = rng.below(3) as usize;
        let bits = self.heap.alloc_closure_slots(id, 0, captured, 0);
        for i in 0..captured {
            let value = self.term(rng, depth - 1, variant);
            unsafe { closure_capture_set(closure_addr_from_tagged(bits).unwrap(), i, value) };
        }
        heap_value(bits)
    }

    /// Up to eleven bytes over a three-letter alphabet, sometimes with a last
    /// partial byte. The variant is a ProcBin, or a ProcBin view past a
    /// prefix, with ones in the bits beyond the length.
    fn binary(&mut self, rng: &mut Rng, variant: bool) -> AnyValue {
        let len = rng.below(12) as usize;
        let mut bytes: Vec<u8> = (0..len).map(|_| b'a' + rng.below(3) as u8).collect();
        let partial = if len > 0 && rng.below(3) == 0 {
            rng.below(7) + 1
        } else {
            0
        };
        let bit_len = (len as u64) * 8 - partial;
        let representation = rng.below(3);
        if !variant {
            if partial > 0 {
                *bytes.last_mut().unwrap() &= u8::MAX << partial;
            }
            return self.heap.alloc_bitstring(&bytes, bit_len);
        }
        if partial > 0 {
            *bytes.last_mut().unwrap() |= !(u8::MAX << partial);
        }
        match representation {
            0 => self.heap.alloc_bitstring(&bytes, bit_len),
            1 => {
                let handle = SharedBinHandle::from_bytes(&bytes, bit_len);
                AnyValue::heap_ptr(alloc_procbin(&mut self.heap, handle, 0).as_raw(), ValueKind::PROCBIN)
            }
            _ => {
                let mut padded = b"xyz".to_vec();
                padded.extend_from_slice(&bytes);
                let handle = SharedBinHandle::from_bytes(&padded, bit_len + 24);
                AnyValue::heap_ptr(alloc_procbin(&mut self.heap, handle, 3).as_raw(), ValueKind::PROCBIN)
            }
        }
    }
}

#[test]
fn equal_terms_hash_equal_in_every_representation() {
    let mut w = world();
    let mut pool = Vec::new();
    for seed in 0..1500u64 {
        pool.push(w.term(&mut Rng(seed), 3, false));
        pool.push(w.term(&mut Rng(seed), 3, true));
    }
    for pair in pool.chunks(2) {
        assert_eq!(
            w.compare(pair[0], pair[1]),
            Ordering::Equal,
            "the two variants of one seed are equal terms"
        );
    }
    let (mut equal_pairs, mut collisions) = (0u64, 0u64);
    for i in 0..pool.len() {
        for j in i + 1..pool.len() {
            let (hash_i, hash_j) = (w.hash(pool[i]), w.hash(pool[j]));
            if w.compare(pool[i], pool[j]) == Ordering::Equal {
                assert_eq!(hash_i, hash_j, "equal terms {i} and {j} hash equal");
                equal_pairs += 1;
            } else {
                collisions += u64::from(hash_i == hash_j);
            }
        }
    }
    assert!(equal_pairs >= 1500, "the pool holds equal pairs of every kind");
    assert_eq!(collisions, 0, "no two unequal terms of the pool share all 64 bits");
}

#[test]
fn an_integer_and_the_float_of_the_same_value_are_different_keys_and_hash_apart() {
    let w = world();
    assert_ne!(w.compare(AnyValue::int(1), AnyValue::float(1.0)), Ordering::Equal);
    assert_ne!(w.hash(AnyValue::int(1)), w.hash(AnyValue::float(1.0)));
    assert_ne!(
        w.hash(AnyValue::float(0.0)),
        w.hash(AnyValue::float(-0.0)),
        "strict order tells the zeros apart"
    );
}

#[test]
fn a_pid_and_a_reference_of_one_word_are_different_keys_and_hash_apart() {
    let w = world();
    let pid = AnyValue::Opaque(ValueKind::PID, 7);
    let reference = AnyValue::Opaque(ValueKind::REF, 7);
    assert_ne!(w.compare(pid, reference), Ordering::Equal);
    assert_ne!(w.hash(pid), w.hash(reference));
}

#[test]
fn an_atom_hashes_by_its_name_whatever_order_atoms_were_interned_in() {
    let schemas = SchemaRegistry::new();
    let names = ["alpha", "beta", "gamma", "delta"];
    let forward = Node::empty();
    let backward = Node::empty();
    let forward_ids: Vec<_> = names.iter().map(|name| forward.intern_atom(name)).collect();
    let backward_ids: Vec<_> = names.iter().rev().map(|name| backward.intern_atom(name)).collect();
    assert_ne!(
        forward_ids[0], backward_ids[3],
        "the two nodes number the same name differently"
    );
    let (forward_hasher, backward_hasher) = (
        TermHasher::new(&forward, &schemas),
        TermHasher::new(&backward, &schemas),
    );
    for (index, name) in names.iter().enumerate() {
        assert_eq!(
            forward_hasher.hash(AnyValue::atom(forward_ids[index])),
            backward_hasher.hash(AnyValue::atom(backward_ids[names.len() - 1 - index])),
            "{name}"
        );
    }
    assert_ne!(
        forward_hasher.hash(AnyValue::atom(forward_ids[0])),
        forward_hasher.hash(AnyValue::atom(forward_ids[1]))
    );
}

#[test]
fn the_atom_table_keeps_each_names_hash_from_the_moment_it_is_interned() {
    let node = Node::new(vec!["seeded".into()]);
    let later = node.intern_atom("later");
    assert_eq!(node.atom_name_hash(0), name_hash("seeded"));
    assert_eq!(node.atom_name_hash(later), name_hash("later"));
}

#[test]
fn closures_of_equal_denotations_hash_equal_whatever_their_ids_and_unequal_ones_apart() {
    let mut w = world();
    let make = |w: &mut World, id: u32, capture: i64| {
        let bits = w.heap.alloc_closure_slots(ClosureDenotationId::user(id), 0, 1, 0);
        unsafe { closure_capture_set(closure_addr_from_tagged(bits).unwrap(), 0, AnyValue::int(capture)) };
        heap_value(bits)
    };
    let (a, same_denotation, other_capture, other_function) = (
        make(&mut w, 0, 5),
        make(&mut w, 100, 5),
        make(&mut w, 0, 6),
        make(&mut w, 1, 5),
    );
    assert_eq!(w.compare(a, same_denotation), Ordering::Equal);
    assert_eq!(w.hash(a), w.hash(same_denotation));
    assert_ne!(w.hash(a), w.hash(other_capture));
    assert_ne!(w.hash(a), w.hash(other_function));
}

#[test]
fn a_denotations_hash_is_kept_when_it_is_registered() {
    let node = Node::empty();
    let id = ClosureDenotationId::user(3);
    let origin = Arc::new(FunctionDenotation::named(None, "kept".to_string(), 2));
    node.register_closure_denotation(id, Arc::clone(&origin));
    assert_eq!(node.closure_denotation_hash(id), origin.semantic_hash());
}

#[test]
fn a_map_hashes_by_its_entries_not_the_order_they_were_given_in() {
    let mut w = world();
    for count in [3usize, 40, 500] {
        let entries: Vec<_> = (0..count as i64)
            .map(|i| (AnyValue::int(i * 7), AnyValue::int(i)))
            .collect();
        let mut reversed = entries.clone();
        reversed.reverse();
        let a = heap_value(w.heap.alloc_map_slots(&entries));
        let b = heap_value(w.heap.alloc_map_slots(&reversed));
        assert_eq!(w.compare(a, b), Ordering::Equal);
        assert_eq!(w.hash(a), w.hash(b), "{count} entries");
        assert_eq!(
            unsafe { map_header_is_trie(a.heap_addr().unwrap()) },
            count > crate::any_value::MAP_FLAT_MAX,
            "{count} entries"
        );
    }
}

#[test]
fn a_trie_built_by_puts_and_a_trie_built_at_once_that_spell_the_same_entries_hash_alike() {
    let mut w = world();
    let big: Vec<_> = (0..40).map(|i| (AnyValue::int(i), AnyValue::int(i * 2))).collect();
    let trie = heap_value(w.heap.alloc_map_slots(&big));
    let mut by_puts = heap_value(w.heap.alloc_map_slots(&big[..1]));
    for &(key, value) in &big[1..] {
        let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, by_puts.heap_addr().unwrap()).unwrap();
        let next = w.heap.map_put_slot(map_ref, key, value);
        by_puts = AnyValue::from_ref(next).unwrap();
    }
    assert!(unsafe { map_header_is_trie(trie.heap_addr().unwrap()) });
    assert!(unsafe { map_header_is_trie(by_puts.heap_addr().unwrap()) });
    assert_eq!(w.compare(trie, by_puts), Ordering::Equal);
    assert_eq!(w.hash(trie), w.hash(by_puts));
}

/// A tuple of `depth` levels in which every level holds the one below twice:
/// `depth` objects that read as `2^depth` leaves.
fn shared_substructure(w: &mut World, depth: u32) -> AnyValue {
    (0..depth).fold(AnyValue::int(0), |below, _| w.tuple(&[below, below]))
}

/// The same term built without sharing: every level a copy of the one below.
fn unshared(w: &mut World, depth: u32) -> AnyValue {
    if depth == 0 {
        return AnyValue::int(0);
    }
    let (left, right) = (unshared(w, depth - 1), unshared(w, depth - 1));
    w.tuple(&[left, right])
}

#[test]
fn a_key_that_shares_substructure_hashes_as_the_tree_it_reads_as() {
    let mut w = world();
    for depth in [1, 5, 12] {
        let shared = shared_substructure(&mut w, depth);
        let copied = unshared(&mut w, depth);
        assert_eq!(w.compare(shared, copied), Ordering::Equal);
        assert_eq!(w.hash(shared), w.hash(copied), "depth {depth}");
    }
}

#[test]
fn a_key_whose_tree_reading_is_astronomically_large_still_hashes() {
    let mut w = world();
    let key = shared_substructure(&mut w, 200);
    let again = shared_substructure(&mut w, 200);
    assert_eq!(w.hash(key), w.hash(again), "2^200 leaves, 200 objects");
}

#[test]
fn a_list_of_one_shared_list_hashes_without_walking_it_once_per_element() {
    let mut w = world();
    let mut level = AnyValue::EmptyList;
    for _ in 0..100 {
        let spine = w.heap.alloc_list_cons_slot(level, crate::any_value::EMPTY_LIST_BITS);
        let spine = w.heap.alloc_list_cons_slot(level, spine);
        level = heap_value(spine);
    }
    assert_eq!(w.hash(level), w.hash(level));
}
