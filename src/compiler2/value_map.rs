//! A table over the values of one body, stored as a vector indexed by the id.
//!
//! A body numbers its values from zero (`Lowerer::fresh_value`), so the ids of
//! one body are a small dense range and a slot per id is cheaper than hashing
//! one: no hasher, no second copy of the key, and iteration follows the id
//! rather than a per-process random seed. A set of values is a `ValueSet`.

use super::body::ValueId;

/// No body mints more values than this; a larger id is a bug, not a request
/// for a huge allocation.
const MAX_SLOT: usize = 1 << 24;

#[derive(Clone)]
pub struct ValueMap<V> {
    slots: Vec<Option<V>>,
    len: usize,
}

impl<V> Default for ValueMap<V> {
    fn default() -> Self {
        Self {
            slots: Vec::new(),
            len: 0,
        }
    }
}

impl<V> ValueMap<V> {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn get(&self, value: &ValueId) -> Option<&V> {
        self.slots.get(value.as_u32() as usize)?.as_ref()
    }

    fn get_mut(&mut self, value: &ValueId) -> Option<&mut V> {
        self.slots.get_mut(value.as_u32() as usize)?.as_mut()
    }

    pub fn contains_key(&self, value: &ValueId) -> bool {
        self.get(value).is_some()
    }

    pub fn insert(&mut self, value: ValueId, v: V) -> Option<V> {
        let slot = self.slot(value);
        let previous = slot.replace(v);
        if previous.is_none() {
            self.len += 1;
        }
        previous
    }

    pub fn remove(&mut self, value: &ValueId) -> Option<V> {
        let removed = self.slots.get_mut(value.as_u32() as usize)?.take();
        if removed.is_some() {
            self.len -= 1;
        }
        removed
    }

    pub fn clear(&mut self) {
        self.slots.clear();
        self.len = 0;
    }

    /// Keep only the entries `keep` accepts.
    pub fn retain(&mut self, mut keep: impl FnMut(&ValueId, &mut V) -> bool) {
        for (index, slot) in self.slots.iter_mut().enumerate() {
            if let Some(v) = slot
                && !keep(&ValueId::from_u32(index as u32), v)
            {
                *slot = None;
                self.len -= 1;
            }
        }
    }

    pub fn entry(&mut self, value: ValueId) -> ValueEntry<'_, V> {
        ValueEntry { map: self, value }
    }

    pub fn iter(&self) -> impl Iterator<Item = (ValueId, &V)> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(index, slot)| slot.as_ref().map(|v| (ValueId::from_u32(index as u32), v)))
    }

    pub fn keys(&self) -> impl Iterator<Item = ValueId> + '_ {
        self.iter().map(|(value, _)| value)
    }

    pub fn values_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.slots.iter_mut().filter_map(Option::as_mut)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.slots.iter().filter_map(Option::as_ref)
    }

    fn slot(&mut self, value: ValueId) -> &mut Option<V> {
        let index = value.as_u32() as usize;
        assert!(index < MAX_SLOT, "value id {index} is outside any body's range");
        if index >= self.slots.len() {
            self.slots.resize_with(index + 1, || None);
        }
        &mut self.slots[index]
    }
}

impl<V: Default> ValueMap<V> {
    /// The value at `value`, made from `V::default()` when absent.
    pub fn or_default(&mut self, value: ValueId) -> &mut V {
        self.entry(value).or_default()
    }
}

pub struct ValueEntry<'a, V> {
    map: &'a mut ValueMap<V>,
    value: ValueId,
}

impl<'a, V> ValueEntry<'a, V> {
    pub fn or_insert(self, v: V) -> &'a mut V {
        self.or_insert_with(|| v)
    }

    pub fn or_insert_with(self, make: impl FnOnce() -> V) -> &'a mut V {
        let slot = self.map.slot(self.value);
        if slot.is_none() {
            *slot = Some(make());
            self.map.len += 1;
        }
        self.map.slots[self.value.as_u32() as usize]
            .as_mut()
            .expect("the slot was just filled")
    }

    pub fn or_default(self) -> &'a mut V
    where
        V: Default,
    {
        self.or_insert_with(V::default)
    }

    /// Apply `change` to the entry when it is present.
    pub fn and_modify(self, change: impl FnOnce(&mut V)) -> Self {
        if let Some(v) = self.map.get_mut(&self.value) {
            change(v);
        }
        self
    }
}

impl<V: std::fmt::Debug> std::fmt::Debug for ValueMap<V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_map()
            .entries(self.iter().map(|(value, v)| (value.as_u32(), v)))
            .finish()
    }
}

impl<V: PartialEq> PartialEq for ValueMap<V> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other.iter())
    }
}

impl<V: Eq> Eq for ValueMap<V> {}

impl<V> std::ops::Index<&ValueId> for ValueMap<V> {
    type Output = V;

    fn index(&self, value: &ValueId) -> &V {
        self.get(value).expect("value id has no entry")
    }
}

impl<V> FromIterator<(ValueId, V)> for ValueMap<V> {
    fn from_iter<I: IntoIterator<Item = (ValueId, V)>>(iter: I) -> Self {
        let mut map = Self::default();
        map.extend(iter);
        map
    }
}

impl<V> Extend<(ValueId, V)> for ValueMap<V> {
    fn extend<I: IntoIterator<Item = (ValueId, V)>>(&mut self, iter: I) {
        for (value, v) in iter {
            self.insert(value, v);
        }
    }
}

impl<V, const N: usize> From<[(ValueId, V); N]> for ValueMap<V> {
    fn from(pairs: [(ValueId, V); N]) -> Self {
        pairs.into_iter().collect()
    }
}

impl<'a, V> IntoIterator for &'a ValueMap<V> {
    type Item = (ValueId, &'a V);
    type IntoIter = Box<dyn Iterator<Item = (ValueId, &'a V)> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.iter())
    }
}

impl<V> IntoIterator for ValueMap<V> {
    type Item = (ValueId, V);
    type IntoIter = std::iter::FilterMap<
        std::iter::Enumerate<std::vec::IntoIter<Option<V>>>,
        fn((usize, Option<V>)) -> Option<(ValueId, V)>,
    >;

    fn into_iter(self) -> Self::IntoIter {
        fn present<V>((index, slot): (usize, Option<V>)) -> Option<(ValueId, V)> {
            slot.map(|v| (ValueId::from_u32(index as u32), v))
        }
        self.slots.into_iter().enumerate().filter_map(present::<V>)
    }
}

#[cfg(test)]
#[path = "value_map_test.rs"]
mod value_map_test;
