use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;

#[derive(Debug)]
pub struct Agenda<J> {
    queue: VecDeque<J>,
    queued: HashSet<J>,
    parked: HashMap<J, u32>,
}

impl<J> Default for Agenda<J> {
    fn default() -> Self {
        Self {
            queue: VecDeque::new(),
            queued: HashSet::new(),
            parked: HashMap::new(),
        }
    }
}

impl<J> Agenda<J>
where
    J: Clone + Eq + Hash,
{
    pub fn new() -> Self {
        Self::default()
    }

    pub fn enqueue(&mut self, job: J) -> bool {
        if !self.queued.insert(job.clone()) {
            return false;
        }
        self.queue.push_back(job);
        true
    }

    pub fn pop(&mut self) -> Option<J> {
        let index = self.queue.iter().position(|job| !self.parked.contains_key(job))?;
        let job = self.queue.remove(index).expect("position names a queued job");
        self.queued.remove(&job);
        Some(job)
    }

    /// Pops the first eligible job while parking matching jobs encountered on
    /// the same FIFO walk. Parked jobs remain owned (`contains` coalesces a
    /// duplicate demand). A job already parked by a nested owner keeps that
    /// owner. Only `pop`/`runnable_len` omit parked work; `len` retains the
    /// total used by timeout diagnostics.
    pub fn pop_or_park_where(&mut self, token: u32, mut should_park: impl FnMut(&J) -> bool) -> Option<J> {
        let mut eligible = None;
        for (index, job) in self.queue.iter().enumerate() {
            if self.parked.contains_key(job) {
                continue;
            }
            if should_park(job) {
                self.parked.insert(job.clone(), token);
            } else {
                eligible = Some(index);
                break;
            }
        }
        let job = self.queue.remove(eligible?).expect("position names a queued job");
        self.queued.remove(&job);
        Some(job)
    }

    /// Consumes one exact queued job if this token owns it or it has not yet
    /// been parked. A different token's parked job remains with that owner.
    pub fn take_for(&mut self, token: u32, job: &J) -> bool {
        if self.parked.get(job).is_some_and(|owner| *owner != token) {
            return false;
        }
        let Some(index) = self.queue.iter().position(|queued| queued == job) else {
            return false;
        };
        self.queue.remove(index).expect("position names a queued job");
        self.parked.remove(job);
        self.queued.remove(job)
    }

    /// Restores this owner's remaining jobs in their original FIFO positions.
    pub fn unpark(&mut self, token: u32) {
        self.parked.retain(|_, owner| *owner != token);
    }

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn runnable_len(&self) -> usize {
        self.queue.len() - self.parked.len()
    }

    pub fn contains(&self, job: &J) -> bool {
        self.queued.contains(job)
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn runnable_is_empty(&self) -> bool {
        self.runnable_len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::Agenda;

    #[test]
    fn parking_preserves_fifo_and_still_coalesces_demands() {
        let mut agenda = Agenda::new();
        for job in [2, 1, 3] {
            assert!(agenda.enqueue(job));
        }
        assert_eq!(agenda.pop_or_park_where(7, |job| *job == 2), Some(1));
        assert!(!agenda.enqueue(2), "a parked job remains owned by the agenda");
        assert_eq!(agenda.len(), 2, "len includes all queued work");
        assert_eq!(agenda.runnable_len(), 1);
        assert_eq!(agenda.pop(), Some(3));
        assert_eq!(agenda.pop(), None);
        assert!(!agenda.is_empty(), "a parked job is still queued");
        assert!(agenda.runnable_is_empty());
        agenda.unpark(7);
        assert_eq!(agenda.pop(), Some(2));
        assert!(agenda.is_empty());
    }

    #[test]
    fn nested_parking_and_exact_take_release_only_their_owner() {
        let mut agenda = Agenda::new();
        for job in [2, 1, 3, 4] {
            assert!(agenda.enqueue(job));
        }
        assert_eq!(agenda.pop_or_park_where(7, |job| *job == 2), Some(1));
        assert_eq!(agenda.pop_or_park_where(8, |job| *job == 3), Some(4));
        assert!(agenda.take_for(7, &2));
        assert!(!agenda.take_for(7, &3));
        agenda.unpark(7);
        assert_eq!(agenda.pop(), None);
        agenda.unpark(8);
        assert_eq!(agenda.pop(), Some(3));
    }

    #[test]
    fn root_aware_pops_classify_each_job_once_in_a_large_queue() {
        use std::cell::Cell;

        let mut agenda = Agenda::new();
        assert!(agenda.enqueue(usize::MAX));
        for job in 0..1_024 {
            assert!(agenda.enqueue(job));
        }
        let classifications = Cell::new(0);
        for expected in 0..1_024 {
            assert_eq!(
                agenda.pop_or_park_where(7, |job| {
                    classifications.set(classifications.get() + 1);
                    *job == usize::MAX
                }),
                Some(expected)
            );
        }
        assert_eq!(
            classifications.get(),
            1_025,
            "parked prefixes must not be reclassified after every completion"
        );
        assert_eq!(agenda.len(), 1);
        assert_eq!(agenda.runnable_len(), 0);
    }
}
