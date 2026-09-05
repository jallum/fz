use std::collections::{HashSet, VecDeque};
use std::hash::Hash;

#[derive(Debug)]
pub struct Agenda<J> {
    queue: VecDeque<J>,
    queued: HashSet<J>,
}

impl<J> Default for Agenda<J> {
    fn default() -> Self {
        Self {
            queue: VecDeque::new(),
            queued: HashSet::new(),
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
        let job = self.queue.pop_front()?;
        self.queued.remove(&job);
        Some(job)
    }

    pub fn len(&self) -> usize {
        self.queue.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::Agenda;

    #[test]
    fn duplicate_demand_preserves_fifo_position() {
        let mut agenda = Agenda::new();
        for job in [2, 1, 3] {
            assert!(agenda.enqueue(job));
        }
        assert!(!agenda.enqueue(1));
        assert_eq!(agenda.pop(), Some(2));
        assert!(agenda.enqueue(2));
        for expected in [1, 3, 2] {
            assert_eq!(agenda.pop(), Some(expected));
        }
        assert_eq!(agenda.pop(), None);
        assert!(agenda.is_empty());
    }
}
