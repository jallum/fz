//! Forwarding marker write/read predicates.

pub(in crate::heap) fn write_forwarding_marker(from: *mut u8, to: *mut u8) {
    unsafe {
        std::ptr::write(
            from as *mut u64,
            (to as u64 & !crate::fz_value::TAG_MASK) | crate::fz_value::TAG_FWD,
        );
    }
}

pub(in crate::heap) fn is_forwarded_list(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { std::ptr::read(addr as *const u64) };
    if marker & crate::fz_value::TAG_MASK != crate::fz_value::TAG_FWD {
        return None;
    }
    let link_marker = unsafe { std::ptr::read(addr.add(8) as *const u64) };
    if link_marker & crate::fz_value::TAG_MASK == crate::fz_value::TAG_FWD {
        Some((marker & !crate::fz_value::TAG_MASK) as *const u8)
    } else {
        None
    }
}

pub(in crate::heap) fn is_forwarded_headerless(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { std::ptr::read(addr as *const u64) };
    if marker & crate::fz_value::TAG_MASK != crate::fz_value::TAG_FWD {
        return None;
    }
    let confirm = unsafe { std::ptr::read(addr.add(8) as *const u64) };
    let forwarded = marker & !crate::fz_value::TAG_MASK;
    if confirm == crate::fz_value::TAG_FWD && forwarded != 0 {
        Some(forwarded as *const u8)
    } else {
        None
    }
}

pub(in crate::heap) fn is_forwarded_procbin(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { std::ptr::read(addr as *const u64) };
    let forwarded = marker & !crate::fz_value::TAG_MASK;
    if marker & crate::fz_value::TAG_MASK == crate::fz_value::TAG_FWD && forwarded != 0 {
        Some(forwarded as *const u8)
    } else {
        None
    }
}

pub(in crate::heap) fn is_forwarded_resource(addr: *const u8) -> Option<*const u8> {
    is_forwarded_procbin(addr)
}
