//! One conjunctive clause inside a DNF: `⋀ pos  ∧  ⋀ (¬neg)`.

#[derive(Clone, PartialEq, Eq, Hash)]
#[cfg_attr(test, derive(Debug))]
pub(crate) struct Conj<T> {
    pub(crate) pos: Vec<T>,
    pub(crate) neg: Vec<T>,
}

impl<T> Conj<T> {
    /// The "true" clause — empty conjunction. As a singleton DNF it represents
    /// the saturated kind (every tuple, every list, every function).
    pub const fn top() -> Self {
        Self {
            pos: Vec::new(),
            neg: Vec::new(),
        }
    }

    /// Whether this clause constrains nothing, so it denotes its whole kind.
    pub(crate) fn is_top(&self) -> bool {
        self.pos.is_empty() && self.neg.is_empty()
    }

    /// How many signatures the clause holds, positive then negative.
    pub(crate) fn sig_count(&self) -> usize {
        self.pos.len() + self.neg.len()
    }

    /// The `i`th signature in the order `pos` then `neg`.
    pub(crate) fn sig(&self, i: usize) -> &T {
        match self.pos.get(i) {
            Some(sig) => sig,
            None => &self.neg[i - self.pos.len()],
        }
    }

    pub(crate) fn sig_mut(&mut self, i: usize) -> &mut T {
        let pos_len = self.pos.len();
        if i < pos_len {
            &mut self.pos[i]
        } else {
            &mut self.neg[i - pos_len]
        }
    }
}
impl<T: Clone> Conj<T> {
    pub(crate) fn pos_of(t: T) -> Self {
        Self {
            pos: vec![t],
            neg: vec![],
        }
    }
}
