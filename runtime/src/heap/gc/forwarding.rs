//! The forwarding marker: the one use of an object's low address bits.
//!
//! Every heap object is 16-byte aligned, so a live pointer's low nibble is
//! clear. Each kind names one marker word whose live value has a clear low
//! nibble by construction: the schema/denotation/length header of a Struct,
//! Closure, Bitstring or Map, the pointer in word 0 of a ProcBin or Resource,
//! and the link in word 1 of a List cons (its head word stays untouched). A
//! collector that copies an object overwrites that word with the new address
//! plus a non-zero nibble, so "low nibble set" is the whole test.

use crate::any_value::ValueKind;
use std::ptr::{read, write};

const NIBBLE_MASK: u64 = 0xF;
const FORWARDED_NIBBLE: u64 = 0x1;

/// Byte offset of the word that holds the marker for `kind`.
const fn marker_offset(kind: ValueKind) -> usize {
    match kind {
        ValueKind::LIST => 8,
        _ => 0,
    }
}

/// Record that the object at `from` now lives at `to`.
pub(crate) fn write_forwarding_marker(from: *mut u8, kind: ValueKind, to: *mut u8) {
    debug_assert_eq!(to as u64 & NIBBLE_MASK, 0, "forwarding target is 16-byte aligned");
    unsafe {
        write(from.add(marker_offset(kind)) as *mut u64, to as u64 | FORWARDED_NIBBLE);
    }
}

/// Where the object at `addr` moved to, if it has been copied.
pub(crate) fn forwarded_target(addr: *const u8, kind: ValueKind) -> Option<*mut u8> {
    let marker = unsafe { read(addr.add(marker_offset(kind)) as *const u64) };
    (marker & NIBBLE_MASK != 0).then_some((marker & !NIBBLE_MASK) as *mut u8)
}

#[cfg(test)]
#[path = "forwarding_test.rs"]
mod forwarding_test;
