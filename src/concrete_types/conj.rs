//! One conjunctive clause inside a DNF: `⋀ pos  ∧  ⋀ (¬neg)`.

#[derive(Clone, PartialEq, Eq, Hash)]
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
}
impl<T: Clone> Conj<T> {
    pub(crate) fn pos_of(t: T) -> Self {
        Self {
            pos: vec![t],
            neg: vec![],
        }
    }
}
