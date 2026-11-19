//! The memo of a walker that maps each type to a value.
//!
//! A pure walker answers the same for the same [`Ty`] every time, so it
//! computes once per handle and every later question about that handle, from
//! any parent that shares it, is a table read. That is what makes such a walker
//! cost the number of distinct handles, not the size of the tree they unfold to.

use crate::fast_hash::HashMap;

use super::recursive::Mapper;
use super::{Ty, Types};

pub(crate) struct TyMemo<V>(HashMap<Ty, V>);

impl<V> Default for TyMemo<V> {
    fn default() -> Self {
        Self(HashMap::default())
    }
}

impl<V: Copy> TyMemo<V> {
    pub(crate) fn get(&self, ty: &Ty) -> Option<V> {
        self.0.get(ty).copied()
    }

    pub(crate) fn remember(&mut self, ty: Ty, value: V) {
        self.0.insert(ty, value);
    }
}

impl Types {
    /// The type the mapper whose memo is `table` makes of `ty`. A mapping that
    /// is still unfinished — it names a recursive construction in flight — is
    /// not remembered.
    pub(super) fn memoized(
        &mut self,
        mapper: Mapper,
        table: fn(&mut Types) -> &mut TyMemo<Ty>,
        ty: Ty,
        compute: impl FnOnce(&mut Types) -> Ty,
    ) -> Ty {
        if let Some(answer) = table(self).get(&ty) {
            return answer;
        }
        let (answer, settled) = self.map_type(|| mapper, ty, compute);
        if settled {
            table(self).remember(ty, answer);
        }
        answer
    }

    /// The lanes a whole value of each type travels in, for the transport layer.
    pub(crate) fn whole_value_lane_counts(&mut self) -> &mut TyMemo<usize> {
        &mut self.whole_value_lane_counts
    }
}
