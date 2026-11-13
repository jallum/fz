//! A set of the values of one body: one bit per value number.
//!
//! A body numbers its values densely from zero (`Lowerer::fresh_value`) and
//! knows how many it has, so a set is sized once, from that count, and never
//! grows. Membership is a shift and a mask over one contiguous run of words.
//! The run lives inside the set for the first 128 values -- all but a
//! fraction of a percent of the bodies in the fixture corpus -- so building,
//! marking and dropping a set for such a body allocates nothing; a larger body
//! gets one exact allocation.

use super::body::ValueId;
use smallvec::SmallVec;

const WORD_BITS: usize = u64::BITS as usize;
const INLINE_WORDS: usize = 2;

#[derive(Clone)]
pub struct ValueSet {
    words: SmallVec<[u64; INLINE_WORDS]>,
}

impl ValueSet {
    /// An empty set over the value numbers `0..count`.
    pub fn for_values(count: usize) -> Self {
        Self {
            words: SmallVec::from_elem(0, count.div_ceil(WORD_BITS)),
        }
    }

    pub fn contains(&self, value: ValueId) -> bool {
        let (index, mask) = Self::locate(value);
        self.words.get(index).is_some_and(|word| word & mask != 0)
    }

    /// Mark `value`; true when it was not marked before.
    pub fn mark(&mut self, value: ValueId) -> bool {
        let (index, mask) = Self::locate(value);
        let word = self
            .words
            .get_mut(index)
            .expect("a value is marked within the count its set was made for");
        let was_new = *word & mask == 0;
        *word |= mask;
        was_new
    }

    /// Unmark `value`; true when it was marked.
    pub fn unmark(&mut self, value: ValueId) -> bool {
        let (index, mask) = Self::locate(value);
        let Some(word) = self.words.get_mut(index) else {
            return false;
        };
        let was_marked = *word & mask != 0;
        *word &= !mask;
        was_marked
    }

    /// Unmark every value `other` marks.
    pub fn subtract(&mut self, other: &Self) {
        for (word, removed) in self.words.iter_mut().zip(&other.words) {
            *word &= !removed;
        }
    }

    /// The marked values in number order.
    pub fn iter(&self) -> Marked<'_> {
        Marked {
            rest: &self.words,
            word: 0,
            base: 0,
            next_base: 0,
        }
    }

    fn locate(value: ValueId) -> (usize, u64) {
        let number = value.as_u32() as usize;
        (number / WORD_BITS, 1 << (number % WORD_BITS))
    }
}

impl Extend<ValueId> for ValueSet {
    fn extend<I: IntoIterator<Item = ValueId>>(&mut self, values: I) {
        for value in values {
            self.mark(value);
        }
    }
}

/// The marked values of a set, lowest number first: the bits of the current
/// word are taken lowest first, then the next word is loaded.
pub struct Marked<'a> {
    rest: &'a [u64],
    word: u64,
    base: u32,
    next_base: u32,
}

impl Iterator for Marked<'_> {
    type Item = ValueId;

    fn next(&mut self) -> Option<ValueId> {
        while self.word == 0 {
            let (&word, rest) = self.rest.split_first()?;
            self.rest = rest;
            self.word = word;
            self.base = self.next_base;
            self.next_base += WORD_BITS as u32;
        }
        let bit = self.word.trailing_zeros();
        self.word &= self.word - 1;
        Some(ValueId::from_u32(self.base + bit))
    }
}

#[cfg(test)]
#[path = "value_set_test.rs"]
mod value_set_test;
