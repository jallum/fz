//! Forwarding marker write/read predicates.

use crate::any_value::{TAG_FWD, TAG_MASK};
use std::ptr::{read, write};

pub(super) fn write_forwarding_marker(from: *mut u8, to: *mut u8) {
    unsafe {
        write(from as *mut u64, (to as u64 & !TAG_MASK) | TAG_FWD);
    }
}

pub(super) fn is_forwarded_list(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { read(addr as *const u64) };
    if marker & TAG_MASK != TAG_FWD {
        return None;
    }
    let link_marker = unsafe { read(addr.add(8) as *const u64) };
    if link_marker & TAG_MASK == TAG_FWD {
        Some((marker & !TAG_MASK) as *const u8)
    } else {
        None
    }
}

pub(super) fn is_forwarded_headerless(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { read(addr as *const u64) };
    if marker & TAG_MASK != TAG_FWD {
        return None;
    }
    let confirm = unsafe { read(addr.add(8) as *const u64) };
    let forwarded = marker & !TAG_MASK;
    if confirm == TAG_FWD && forwarded != 0 {
        Some(forwarded as *const u8)
    } else {
        None
    }
}

pub(super) fn is_forwarded_procbin(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { read(addr as *const u64) };
    let forwarded = marker & !TAG_MASK;
    if marker & TAG_MASK == TAG_FWD && forwarded != 0 {
        Some(forwarded as *const u8)
    } else {
        None
    }
}

pub(super) fn is_forwarded_resource(addr: *const u8) -> Option<*const u8> {
    is_forwarded_procbin(addr)
}
