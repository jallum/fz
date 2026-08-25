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
        self.queue.is_empty()
    }

    pub fn contains(&self, job: &J) -> bool {
        self.queued.contains(job)
    }
}
