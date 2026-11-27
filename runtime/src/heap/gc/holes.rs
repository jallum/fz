//! Open fields in a collection: forwarding the destinations that name them,
//! writing down the ones still open, and reading the ones the last collection
//! wrote down.

use super::forward::Tracer;
use crate::any_value::{ListCons, ValueKind};
use crate::heap::Generation;
use crate::heap::destination::{FieldDestination, Place};

impl Tracer<'_> {
    /// The destination word `word` after the collection: its cell forwarded
    /// like any cell, its layout kept. A destination whose field is still
    /// open is written down for the next minor collection.
    ///
    /// Not inlined into the trace loops: a slot of this kind is rare, and the
    /// loops stay as they are for every other kind.
    #[cold]
    #[inline(never)]
    pub(super) fn forward_destination(&mut self, word: u64) -> u64 {
        let dest = FieldDestination::from_word(word);
        let cell = self.forward(dest.cell_addr() as u64, dest.layout().cell_kind());
        let dest = dest.rebased(cell as *mut u8);
        // The copy is read, never the from-space original, whose first word
        // may already be a forwarding marker.
        self.write_down_if_open(dest);
        dest.word()
    }

    /// Before anything else is forwarded, a minor collection reads every
    /// field the last collection wrote down open: each may hold a young value
    /// by now. The list is then rebuilt from the destinations this collection
    /// meets. A major collection reads nothing, because it traces everything,
    /// and rebuilds the list the same way.
    pub(in super::super) fn read_open_holes(&mut self, generation: Generation) {
        let written_down = std::mem::take(&mut self.heap.open_holes);
        if generation == Generation::Minor {
            for dest in written_down {
                self.forward_field(dest);
                // Its cell is old and stays where it is, so a field still open
                // stays written down whether or not anything names it again.
                self.write_down_if_open(dest);
            }
        }
    }

    /// Write `dest` down for the next minor collection if its field is open
    /// and is not written down already.
    fn write_down_if_open(&mut self, dest: FieldDestination) {
        if unsafe { dest.is_open(self.schemas) } && !self.heap.open_holes.contains(&dest) {
            self.heap.open_holes.push(dest);
        }
    }

    /// Forward the value the field `dest` names holds, if it holds one.
    fn forward_field(&mut self, dest: FieldDestination) {
        match unsafe { Place::of(dest, self.schemas) } {
            Place::Link(cons) => {
                let cons = unsafe { &mut *cons };
                self.forward_tail(cons);
            }
            Place::Struct { word, kind } => {
                let kind = ValueKind::new(unsafe { *kind }).expect("struct field kind");
                unsafe { self.forward_slot(word, kind) };
            }
            Place::Map { word, kinds } => {
                let kind = crate::any_value::map_value_kind(unsafe { *kinds });
                unsafe { self.forward_slot(word, kind) };
            }
        }
    }

    /// Forward the tail of `cons` and relocate its link; an open tail has no
    /// address and stays open.
    pub(super) fn forward_tail(&mut self, cons: &mut ListCons) {
        let tail = self.forward(cons.tail_cell_addr(), ValueKind::LIST);
        cons.relocate_tail_for_gc(tail);
    }
}
