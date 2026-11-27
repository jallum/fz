//! A map the compiler emits as read-only data holds the bytes the runtime's
//! builder writes for the same entries. Both are made here for the same keys
//! and values, with the atoms numbered in several orders, and compared over the
//! words a writer stores.

use super::*;
use crate::ground_value::{GroundValue, entries_in_key_order};
use fz_runtime::any_value::{AnyValue, AnyValueRef, MAP_FLAT_MAX, map_values_offset};
use fz_runtime::heap::SchemaRegistry;
use fz_runtime::process::Process;
use std::cell::RefCell;
use std::rc::Rc;

fn process() -> Box<Process> {
    Box::new(Process::new(Rc::new(RefCell::new(SchemaRegistry::new()))))
}

/// The bytes of the map at `reference`, to the end of its last value: the
/// words a writer stores. The pad after them is nothing's.
fn stored_bytes(reference: AnyValueRef, count: usize) -> Vec<u8> {
    let stored = map_values_offset(count) + 8 * count;
    let address = reference.map_addr().expect("a map").cast_const();
    unsafe { std::slice::from_raw_parts(address, stored) }.to_vec()
}

/// A value of each immediate kind a literal can hold, by position.
fn immediate(index: usize, atom: impl Fn(&str) -> AnyValue) -> AnyValue {
    match index % 4 {
        0 => AnyValue::int(index as i64 * 1_000_003 - 7),
        1 => AnyValue::float(index as f64 + 0.25),
        2 => atom("value"),
        _ => AnyValue::empty_list(),
    }
}

/// Intent: a flat map of literal atom keys, written as read-only data in the
/// order the compiler gives, is byte for byte the map the runtime builds from
/// the same entries, however the atoms happen to be numbered and for every size
/// a flat map has.
#[test]
fn a_read_only_map_holds_the_bytes_the_runtime_builder_stores() {
    let names: Vec<String> = (0..=MAP_FLAT_MAX)
        .map(|index| format!("key_{:02}", (index * 7) % 33))
        .collect();
    for interning in [Interning::AsWritten, Interning::Reversed, Interning::Scattered] {
        for count in 0..=MAP_FLAT_MAX {
            let mut process = process();
            let written = &names[..count];
            let interned: Vec<String> = written.iter().cloned().chain(["value".to_string()]).collect();
            let atom_ids = interning.intern(&process, &interned);
            let atom = |name: &str| AnyValue::atom(atom_ids[name]);

            let keys: Vec<GroundValue> = written.iter().cloned().map(GroundValue::Atom).collect();
            let compile_time =
                entries_in_key_order(keys.iter().zip(0..).map(|(key, index)| (Some(key), index))).unwrap_or_default();
            let fields: Vec<_> = compile_time
                .iter()
                .map(|index| {
                    let GroundValue::Atom(name) = &keys[*index] else {
                        unreachable!()
                    };
                    (
                        StaticLiteralField::Scalar(atom(name)),
                        StaticLiteralField::Scalar(immediate(*index, atom)),
                    )
                })
                .collect();
            let image = static_map_image(&fields).expect("a flat map of immediates is read-only data");

            let entries: Vec<_> = (0..count)
                .map(|index| (atom(&written[index]), immediate(index, atom)))
                .collect();
            let runtime = AnyValueRef::from_heap_object(ValueKind::MAP, {
                let word = process.heap.alloc_map_slots(&entries);
                fz_runtime::any_value::map_addr_from_tagged(word).expect("the runtime built a map")
            })
            .expect("a map ref");

            assert_eq!(image.bytes.len(), map_size_for_count(count));
            assert_eq!(
                image.bytes[..map_values_offset(count) + 8 * count],
                stored_bytes(runtime, count),
                "{count} entries, atoms numbered {interning:?}: the words a writer stores"
            );
            assert!(image.addresses.is_empty(), "immediates need no address");
        }
    }
}

/// How a process numbers the names a case uses: the order the ids are handed
/// out in, which decides every atom's id and so what an id-ordered map would be.
#[derive(Clone, Copy, Debug)]
enum Interning {
    AsWritten,
    Reversed,
    Scattered,
}

impl Interning {
    fn intern(self, process: &Process, names: &[String]) -> crate::fast_hash::HashMap<String, u32> {
        let mut order: Vec<&String> = names.iter().collect();
        match self {
            Interning::AsWritten => {}
            Interning::Reversed => order.reverse(),
            Interning::Scattered => order.sort_by_key(|name| name.bytes().map(u64::from).sum::<u64>() % 5),
        }
        order
            .into_iter()
            .map(|name| (name.clone(), process.node.intern_atom(name)))
            .collect()
    }
}

/// Intent: a read-only object an entry holds is named by its address and
/// carries its own kind, in the slot and the tag byte the runtime reads it
/// from; the word is the linker's to fill.
#[test]
fn a_read_only_map_names_a_read_only_object_by_address_and_kind() {
    let objects = StaticObject {
        data_id: cranelift_module::DataId::from_u32(7),
        kind: ValueKind::BITSTRING,
    };
    let fields = [
        (
            StaticLiteralField::Scalar(AnyValue::int(1)),
            StaticLiteralField::Object(objects),
        ),
        (
            StaticLiteralField::Object(objects),
            StaticLiteralField::Scalar(AnyValue::atom(3)),
        ),
    ];
    let image = static_map_image(&fields).expect("objects are read-only data");
    assert_eq!(
        image.addresses.iter().map(|(offset, _)| *offset).collect::<Vec<_>>(),
        [map_values_offset(2), map_keys_offset(2) + 8],
        "the value of the first entry and the key of the second"
    );
    assert_eq!(image.bytes[8], map_pack_tag(ValueKind::INT, ValueKind::BITSTRING));
    assert_eq!(image.bytes[9], map_pack_tag(ValueKind::BITSTRING, ValueKind::ATOM));
    assert_eq!(&image.bytes[map_values_offset(2)..map_values_offset(2) + 8], &[0; 8]);
}

/// Intent: the emitter refuses what the collector would not follow: a heap
/// reference, a missing value, or a map too large to be flat.
#[test]
fn a_read_only_map_refuses_what_is_not_an_immediate_or_a_read_only_object() {
    let mut process = process();
    let heap_ref = process.heap.alloc_bitstring(b"abc", 24);
    for refused in [heap_ref, AnyValue::null()] {
        let fields = [(
            StaticLiteralField::Scalar(AnyValue::int(1)),
            StaticLiteralField::Scalar(refused),
        )];
        assert!(static_map_image(&fields).is_err(), "{refused:?} is not read-only data");
    }
    let too_many: Vec<_> = (0..=MAP_FLAT_MAX as i64)
        .map(|index| {
            (
                StaticLiteralField::Scalar(AnyValue::int(index)),
                StaticLiteralField::Scalar(AnyValue::int(0)),
            )
        })
        .collect();
    assert!(
        static_map_image(&too_many).is_err(),
        "above the flat limit a map is a trie"
    );
}
