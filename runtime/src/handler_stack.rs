//! The handlers a raise can reach: one record per `try` body the process is
//! inside, innermost on top.
//!
//! Records live in a word stack the process owns, so entering a `try` builds
//! nothing on the heap. Compiled code pushes and pops its records inline,
//! through the `top` and `end` fields whose offsets `process_abi` publishes;
//! only a full stack calls [`HandlerStack::reserve`] to grow it.
//!
//! Every record ends in a trailer word holding the record's size in bytes,
//! trailer included, so the innermost record is found from `top` alone:
//!
//! ```text
//! compiled:    [closure image: header, code, captures, kinds] [size]
//! interpreter:                                                [8]
//! ```
//!
//! A compiled record's image is laid out exactly as a heap closure is, with
//! the outer continuation as capture 0, so a raise materializes the delivered
//! handler from it the way it would from a heap template. The interpreter
//! keeps its handler frame itself, so its record is the trailer alone.

use crate::any_value::{
    AnyValueRef, closure_capture_raw_kind, closure_capture_ref_word, closure_capture_set_ref_word,
    closure_captured_count,
};

const WORD: usize = size_of::<u64>();
const INTERPRETER_RECORD_BYTES: u64 = WORD as u64;

/// The innermost handler a raise reaches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Innermost {
    /// Compiled code's handler: the closure image a raise materializes.
    Compiled(*mut u8),
    /// The interpreter's handler: the raise goes to `Process::raised`.
    Interpreter,
}

/// The word stack of a process's handler records. `top` and `end` lead the
/// struct because compiled code reads and writes them in place.
#[repr(C)]
#[derive(Debug)]
pub struct HandlerStack {
    /// One past the last word of the innermost record.
    top: *mut u64,
    /// One past the last word the storage holds.
    end: *mut u64,
    storage: Vec<u64>,
}

impl Default for HandlerStack {
    fn default() -> Self {
        Self {
            top: std::ptr::null_mut(),
            end: std::ptr::null_mut(),
            storage: Vec::new(),
        }
    }
}

/// Byte offsets of `HandlerStack::top` and `HandlerStack::end`, for compiled
/// code that pushes and pops records inline.
pub const HANDLER_STACK_TOP_OFFSET: usize = std::mem::offset_of!(HandlerStack, top);
pub const HANDLER_STACK_END_OFFSET: usize = std::mem::offset_of!(HandlerStack, end);

impl HandlerStack {
    /// Reserve `bytes` on top of the stack, growing its storage when it is
    /// full, and answer where the reserved bytes start. The caller fills them,
    /// ending with the trailer. Growing moves the records, so no address into
    /// the stack outlives a reservation.
    pub fn reserve(&mut self, bytes: usize) -> *mut u8 {
        assert!(
            bytes >= WORD && bytes.is_multiple_of(WORD),
            "a handler record is whole words with a trailer"
        );
        let words = bytes / WORD;
        let used = self.used_words();
        if used + words > self.storage.len() {
            self.grow(used + words);
        }
        let record = self.top;
        // SAFETY: the storage holds `used + words` words, so the new top is in bounds or one past.
        self.top = unsafe { record.add(words) };
        record as *mut u8
    }

    /// Leave every `try`, keeping the storage for the next records.
    pub fn clear(&mut self) {
        if !self.storage.is_empty() {
            self.top = self.storage.as_mut_ptr();
        }
    }

    /// Enter an interpreted `try`.
    pub fn push_interpreter(&mut self) {
        let record = self.reserve(WORD) as *mut u64;
        // SAFETY: `reserve` handed back one word for the trailer.
        unsafe { record.write(INTERPRETER_RECORD_BYTES) };
    }

    /// The innermost handler, if the process is inside any `try`.
    pub fn innermost(&self) -> Option<Innermost> {
        self.records().next().map(|(record, _)| record)
    }

    /// Leave the innermost `try`. A pop with no handler is a compiler defect,
    /// never a program state.
    pub fn pop(&mut self) {
        let (_, below) = self
            .records()
            .next()
            .expect("a try body completes under the handler it pushed");
        self.top = below;
    }

    /// How many handlers a raise could reach.
    pub fn depth(&self) -> usize {
        self.records().count()
    }

    /// Hand every heap value a compiled record captures, innermost first, to
    /// `forward`, which a collection uses to move it: each capture holds the
    /// value `forward` leaves in it.
    pub fn forward_captures(&mut self, mut forward: impl FnMut(&mut AnyValueRef)) {
        self.for_each_heap_capture(|image, idx| {
            // SAFETY: `image` is a live closure image and `idx` one of its captures.
            let word = unsafe { closure_capture_ref_word(image, idx) };
            let mut value = AnyValueRef::from_raw_word(word).expect("a heap capture is a value ref");
            forward(&mut value);
            // SAFETY: `image` is a live closure image the stack owns.
            unsafe { closure_capture_set_ref_word(image, idx, value.raw_word()) };
        });
    }

    fn for_each_heap_capture(&self, mut each: impl FnMut(*const u8, usize)) {
        for (record, _) in self.records() {
            let Innermost::Compiled(image) = record else {
                continue;
            };
            let image = image as *const u8;
            // SAFETY: a compiled record is a closure image.
            let count = unsafe { closure_captured_count(image) };
            for idx in 0..count {
                // SAFETY: `idx` is one of the image's captures.
                if unsafe { closure_capture_raw_kind(image, idx) }.1.is_heap() {
                    each(image, idx);
                }
            }
        }
    }

    /// The records from innermost to outermost, each with the top the stack
    /// has once that record is popped.
    fn records(&self) -> impl Iterator<Item = (Innermost, *mut u64)> + '_ {
        let base = self.storage.as_ptr() as *mut u64;
        let mut top = self.top;
        std::iter::from_fn(move || {
            if top.is_null() || top == base {
                return None;
            }
            // SAFETY: a non-empty stack's top word is its innermost record's trailer.
            let bytes = unsafe { top.sub(1).read() } as usize;
            // SAFETY: the innermost record spans `bytes` below `top`.
            let below = unsafe { (top as *mut u8).sub(bytes) as *mut u64 };
            let record = if bytes == INTERPRETER_RECORD_BYTES as usize {
                Innermost::Interpreter
            } else {
                Innermost::Compiled(below as *mut u8)
            };
            top = below;
            Some((record, below))
        })
    }

    fn used_words(&self) -> usize {
        if self.top.is_null() {
            return 0;
        }
        // SAFETY: `top` points into `storage` or one past its end.
        (unsafe { self.top.offset_from(self.storage.as_ptr()) }) as usize
    }

    fn grow(&mut self, needed: usize) {
        let used = self.used_words();
        let mut storage = vec![0u64; needed.max(2 * self.storage.len()).max(64)];
        storage[..used].copy_from_slice(&self.storage[..used]);
        self.storage = storage;
        let base = self.storage.as_mut_ptr();
        // SAFETY: `used` and `len` are within the new storage.
        unsafe {
            self.top = base.add(used);
            self.end = base.add(self.storage.len());
        }
    }
}

#[cfg(test)]
#[path = "handler_stack_test.rs"]
pub(crate) mod handler_stack_test;
