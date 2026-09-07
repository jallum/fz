//! Immutable ordered inventories with path sharing and ordinal projection.

use std::cmp::Ordering;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub struct SharedOrder<K, V> {
    root: Option<Rc<Node<K, V>>>,
}

#[derive(Debug)]
struct Node<K, V> {
    key: K,
    value: V,
    left: SharedOrder<K, V>,
    right: SharedOrder<K, V>,
    height: usize,
    len: usize,
}

impl<K, V> Default for SharedOrder<K, V> {
    fn default() -> Self {
        Self { root: None }
    }
}

impl<K, V> SharedOrder<K, V> {
    pub fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |node| node.len)
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    fn height(&self) -> usize {
        self.root.as_ref().map_or(0, |node| node.height)
    }

    pub fn lookup<Q: ?Sized>(&self, key: &Q, compare: &impl Fn(&Q, &K) -> Ordering) -> Option<&V> {
        let mut cursor = self;
        while let Some(node) = &cursor.root {
            match compare(key, &node.key) {
                Ordering::Less => cursor = &node.left,
                Ordering::Equal => return Some(&node.value),
                Ordering::Greater => cursor = &node.right,
            }
        }
        None
    }

    pub fn rank<Q: ?Sized>(&self, key: &Q, compare: &impl Fn(&Q, &K) -> Ordering) -> Option<usize> {
        self.ranked(key, compare).map(|(rank, _)| rank)
    }

    pub fn ranked<Q: ?Sized>(&self, key: &Q, compare: &impl Fn(&Q, &K) -> Ordering) -> Option<(usize, &V)> {
        let mut cursor = self;
        let mut rank = 0;
        while let Some(node) = &cursor.root {
            match compare(key, &node.key) {
                Ordering::Less => cursor = &node.left,
                Ordering::Equal => return Some((rank + node.left.len(), &node.value)),
                Ordering::Greater => {
                    rank += node.left.len() + 1;
                    cursor = &node.right;
                }
            }
        }
        None
    }

    pub fn get_index(&self, mut index: usize) -> Option<&V> {
        let mut cursor = self;
        while let Some(node) = &cursor.root {
            match index.cmp(&node.left.len()) {
                Ordering::Less => cursor = &node.left,
                Ordering::Equal => return Some(&node.value),
                Ordering::Greater => {
                    index -= node.left.len() + 1;
                    cursor = &node.right;
                }
            }
        }
        None
    }

    pub fn get(&self, index: usize) -> Option<&V> {
        self.get_index(index)
    }

    pub fn first(&self) -> Option<&V> {
        self.get_index(0)
    }

    pub fn entries(&self) -> Entries<'_, K, V> {
        let mut iter = Entries { stack: Vec::new() };
        iter.descend(self);
        iter
    }

    pub fn iter(&self) -> Values<'_, K, V> {
        Values(self.entries())
    }

    fn same_root(&self, other: &Self) -> bool {
        match (&self.root, &other.root) {
            (None, None) => true,
            (Some(left), Some(right)) => Rc::ptr_eq(left, right),
            _ => false,
        }
    }
}

impl<K: Clone, V: Clone + PartialEq> SharedOrder<K, V> {
    fn node(key: K, value: V, left: Self, right: Self) -> Self {
        Self {
            root: Some(Rc::new(Node {
                height: 1 + left.height().max(right.height()),
                len: 1 + left.len() + right.len(),
                key,
                value,
                left,
                right,
            })),
        }
    }

    fn balanced(key: K, value: V, left: Self, right: Self) -> Self {
        if left.height() > right.height() + 1 {
            let child = left.root.as_ref().expect("left-heavy node has a left child");
            if child.left.height() >= child.right.height() {
                return Self::node(
                    child.key.clone(),
                    child.value.clone(),
                    child.left.clone(),
                    Self::node(key, value, child.right.clone(), right),
                );
            }
            let pivot = child.right.root.as_ref().expect("double rotation has a pivot");
            return Self::node(
                pivot.key.clone(),
                pivot.value.clone(),
                Self::node(
                    child.key.clone(),
                    child.value.clone(),
                    child.left.clone(),
                    pivot.left.clone(),
                ),
                Self::node(key, value, pivot.right.clone(), right),
            );
        }
        if right.height() > left.height() + 1 {
            let child = right.root.as_ref().expect("right-heavy node has a right child");
            if child.right.height() >= child.left.height() {
                return Self::node(
                    child.key.clone(),
                    child.value.clone(),
                    Self::node(key, value, left, child.left.clone()),
                    child.right.clone(),
                );
            }
            let pivot = child.left.root.as_ref().expect("double rotation has a pivot");
            return Self::node(
                pivot.key.clone(),
                pivot.value.clone(),
                Self::node(key, value, left, pivot.left.clone()),
                Self::node(
                    child.key.clone(),
                    child.value.clone(),
                    pivot.right.clone(),
                    child.right.clone(),
                ),
            );
        }
        Self::node(key, value, left, right)
    }

    pub fn insert(&mut self, key: K, value: V, compare: &impl Fn(&K, &K) -> Ordering) -> bool {
        let Some(node) = &self.root else {
            *self = Self::node(key, value, Self::default(), Self::default());
            return true;
        };
        match compare(&key, &node.key) {
            Ordering::Equal if node.value == value => false,
            Ordering::Equal => {
                *self = Self::node(key, value, node.left.clone(), node.right.clone());
                true
            }
            Ordering::Less => {
                let mut left = node.left.clone();
                if !left.insert(key, value, compare) {
                    return false;
                }
                *self = Self::balanced(node.key.clone(), node.value.clone(), left, node.right.clone());
                true
            }
            Ordering::Greater => {
                let mut right = node.right.clone();
                if !right.insert(key, value, compare) {
                    return false;
                }
                *self = Self::balanced(node.key.clone(), node.value.clone(), node.left.clone(), right);
                true
            }
        }
    }

    pub fn remove<Q: ?Sized>(&mut self, key: &Q, compare: &impl Fn(&Q, &K) -> Ordering) -> Option<V> {
        let node = self.root.as_ref()?;
        match compare(key, &node.key) {
            Ordering::Less => {
                let mut left = node.left.clone();
                let removed = left.remove(key, compare)?;
                *self = Self::balanced(node.key.clone(), node.value.clone(), left, node.right.clone());
                Some(removed)
            }
            Ordering::Greater => {
                let mut right = node.right.clone();
                let removed = right.remove(key, compare)?;
                *self = Self::balanced(node.key.clone(), node.value.clone(), node.left.clone(), right);
                Some(removed)
            }
            Ordering::Equal => {
                let removed = node.value.clone();
                *self = if node.left.is_empty() {
                    node.right.clone()
                } else if node.right.is_empty() {
                    node.left.clone()
                } else {
                    let mut right = node.right.clone();
                    let (next_key, next_value) = right.remove_first();
                    Self::balanced(next_key, next_value, node.left.clone(), right)
                };
                Some(removed)
            }
        }
    }

    fn remove_first(&mut self) -> (K, V) {
        let node = self.root.as_ref().expect("remove_first requires a nonempty tree");
        if node.left.is_empty() {
            let first = (node.key.clone(), node.value.clone());
            *self = node.right.clone();
            return first;
        }
        let mut left = node.left.clone();
        let first = left.remove_first();
        *self = Self::balanced(node.key.clone(), node.value.clone(), left, node.right.clone());
        first
    }
}

impl<K: PartialEq, V: PartialEq> PartialEq for SharedOrder<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.equal_with_work(other).0
    }
}

enum ComparisonPart<'a, K, V> {
    Tree(&'a Rc<Node<K, V>>),
    Row(&'a Node<K, V>),
}

impl<K, V> ComparisonPart<'_, K, V> {
    fn len(&self) -> usize {
        match self {
            Self::Tree(node) => node.len,
            Self::Row(_) => 1,
        }
    }
}

impl<K: PartialEq, V: PartialEq> SharedOrder<K, V> {
    fn equal_with_work(&self, other: &Self) -> (bool, usize) {
        if self.same_root(other) {
            return (true, 0);
        }
        if self.len() != other.len() {
            return (false, 0);
        }
        let mut left = self.root.iter().map(ComparisonPart::Tree).collect::<Vec<_>>();
        let mut right = other.root.iter().map(ComparisonPart::Tree).collect::<Vec<_>>();
        #[cfg(test)]
        let mut work = 0;
        #[cfg(not(test))]
        let work = 0;
        while let (Some(a), Some(b)) = (left.last(), right.last()) {
            #[cfg(test)]
            {
                work += 1;
            }
            match (a, b) {
                (ComparisonPart::Tree(a), ComparisonPart::Tree(b)) if Rc::ptr_eq(a, b) => {
                    left.pop();
                    right.pop();
                }
                (ComparisonPart::Row(a), ComparisonPart::Row(b)) => {
                    if a.key != b.key || a.value != b.value {
                        return (false, work);
                    }
                    left.pop();
                    right.pop();
                }
                _ => {
                    let a_len = a.len();
                    let b_len = b.len();
                    if a_len >= b_len {
                        Self::expand_comparison(&mut left);
                    }
                    if b_len >= a_len {
                        Self::expand_comparison(&mut right);
                    }
                }
            }
        }
        (left.is_empty() && right.is_empty(), work)
    }

    fn expand_comparison<'a>(parts: &mut Vec<ComparisonPart<'a, K, V>>) {
        if !matches!(parts.last(), Some(ComparisonPart::Tree(_))) {
            return;
        }
        let Some(ComparisonPart::Tree(node)) = parts.pop() else {
            unreachable!()
        };
        if let Some(right) = &node.right.root {
            parts.push(ComparisonPart::Tree(right));
        }
        parts.push(ComparisonPart::Row(node));
        if let Some(left) = &node.left.root {
            parts.push(ComparisonPart::Tree(left));
        }
    }
}

impl<K: Eq, V: Eq> Eq for SharedOrder<K, V> {}

impl<K, V> std::ops::Index<usize> for SharedOrder<K, V> {
    type Output = V;
    fn index(&self, index: usize) -> &V {
        self.get_index(index).expect("ordered inventory index out of bounds")
    }
}

pub struct Entries<'a, K, V> {
    stack: Vec<&'a Node<K, V>>,
}

pub struct Values<'a, K, V>(Entries<'a, K, V>);

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|(_, value)| value)
    }
}

impl<'a, K, V> IntoIterator for &'a SharedOrder<K, V> {
    type Item = &'a V;
    type IntoIter = Values<'a, K, V>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> Entries<'a, K, V> {
    fn descend(&mut self, mut cursor: &'a SharedOrder<K, V>) {
        while let Some(node) = &cursor.root {
            self.stack.push(node);
            cursor = &node.left;
        }
    }
}

impl<'a, K, V> Iterator for Entries<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        let node = self.stack.pop()?;
        self.descend(&node.right);
        Some((&node.key, &node.value))
    }
}

#[cfg(test)]
impl<K, V> SharedOrder<K, V> {
    fn shared_nodes(&self, other: &Self) -> usize {
        let Some(node) = &self.root else {
            return 0;
        };
        if self.same_root(other) {
            return self.len();
        }
        let Some(peer) = &other.root else {
            return 0;
        };
        node.left.shared_nodes(&peer.left) + node.right.shared_nodes(&peer.right)
    }

    fn assert_balanced(&self) {
        if let Some(node) = &self.root {
            assert!(node.left.height().abs_diff(node.right.height()) <= 1);
            assert_eq!(node.height, 1 + node.left.height().max(node.right.height()));
            assert_eq!(node.len, 1 + node.left.len() + node.right.len());
            node.left.assert_balanced();
            node.right.assert_balanced();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::SharedOrder;
    use std::collections::BTreeMap;
    use std::rc::Rc;

    #[test]
    fn equal_updates_share_the_whole_inventory_and_obey_the_supplied_order() {
        let compare = |left: &i32, right: &i32| right.cmp(left);
        let mut actual = SharedOrder::default();
        for key in 0..63 {
            actual.insert(key, key, &compare);
        }
        let retained = actual.clone();
        assert!(!actual.insert(31, 31, &compare));
        assert_eq!(actual.remove(&100, &compare), None);
        assert!(actual.same_root(&retained));
        assert_eq!(actual.shared_nodes(&retained), 63);
        assert_eq!(
            actual.iter().copied().collect::<Vec<_>>(),
            (0..63).rev().collect::<Vec<_>>()
        );
        assert_eq!(actual.rank(&0, &compare), Some(62));
        actual.remove(&31, &compare);
        assert_eq!(actual.rank(&0, &compare), Some(61));
        assert_eq!(actual.get_index(31), Some(&30));
    }

    #[test]
    fn changed_keys_preserve_prior_snapshots_and_unmodified_tree_branches() {
        let mut original = SharedOrder::default();
        for key in 0..255 {
            original.insert(key, Rc::new(key), &i32::cmp);
        }
        let retained = original.clone();
        let old_value = Rc::clone(original.lookup(&127, &i32::cmp).unwrap());
        original.insert(127, Rc::new(-127), &i32::cmp);
        assert_eq!(**retained.lookup(&127, &i32::cmp).unwrap(), 127);
        assert_eq!(**original.lookup(&127, &i32::cmp).unwrap(), -127);
        assert!(Rc::ptr_eq(&old_value, retained.lookup(&127, &i32::cmp).unwrap()));
        assert!(
            original.shared_nodes(&retained) >= 247,
            "one replacement copies at most one balanced path"
        );
        original.remove(&0, &i32::cmp);
        assert_eq!(retained.len(), 255);
        assert_eq!(original.len(), 254);
        assert!(
            original.shared_nodes(&retained) >= 235,
            "deletion preserves branches outside its balancing path"
        );
    }

    #[test]
    fn rotations_compare_shared_subtrees_without_scanning_unchanged_rows() {
        let mut original = SharedOrder::default();
        for key in 0..4095 {
            original.insert(key, key, &i32::cmp);
        }
        let mut changed = original.clone();
        // Equal content with different path shapes after deletion/reinsertion.
        for key in [0, 1, 2, 3, 4, 5, 6, 7] {
            changed.remove(&key, &i32::cmp);
        }
        for key in [7, 6, 5, 4, 3, 2, 1, 0] {
            changed.insert(key, key, &i32::cmp);
        }
        let (equal, work) = original.equal_with_work(&changed);
        assert!(equal);
        assert!(work < 200, "rotated paths must skip shared subtrees: {work}");
        changed.insert(4094, -1, &i32::cmp);
        let (equal, work) = original.equal_with_work(&changed);
        assert!(!equal);
        assert!(
            work < 300,
            "a far changed row does not scan intervening inventory: {work}"
        );
    }

    #[test]
    fn ordered_updates_match_a_map_and_project_each_rank_in_both_directions() {
        let mut actual = SharedOrder::default();
        let mut expected = BTreeMap::new();
        let mut random = 0x218a_b94c_u64;
        for step in 0..4000 {
            random ^= random << 13;
            random ^= random >> 7;
            random ^= random << 17;
            let key = (random % 127) as i32;
            if random & 256 == 0 {
                actual.insert(key, step, &i32::cmp);
                expected.insert(key, step);
            } else {
                assert_eq!(actual.remove(&key, &i32::cmp), expected.remove(&key));
            }
            assert_eq!(actual.len(), expected.len());
            assert_eq!(
                actual.entries().collect::<Vec<_>>(),
                expected.iter().collect::<Vec<_>>()
            );
            for (rank, (key, value)) in expected.iter().enumerate() {
                assert_eq!(actual.rank(key, &i32::cmp), Some(rank));
                assert_eq!(actual.lookup(key, &i32::cmp), Some(value));
                assert_eq!(actual.get_index(rank), Some(value));
            }
            assert!(actual.get_index(expected.len()).is_none());
            actual.assert_balanced();
        }
    }
}
