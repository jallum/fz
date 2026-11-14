use std::hash::Hash;

use crate::facts::FactUse;
use crate::fast_hash::HashMap;

/// The waits that stopped one run, each with the job that will answer it.
///
/// The client names the answering job when it records the wait, so the wait
/// graph (which job waits on which) is stored with the waits and never
/// re-derived from a fact. A fact with no single answering job waits with no
/// producer; it blocks the run like any other wait and has no edge.
#[derive(Debug, Clone)]
pub struct StandingWaits<F, J> {
    producers: HashMap<FactUse<F>, Option<J>>,
}

impl<F, J> Default for StandingWaits<F, J> {
    fn default() -> Self {
        Self {
            producers: HashMap::default(),
        }
    }
}

impl<F: Eq + Hash, J> StandingWaits<F, J> {
    pub fn is_empty(&self) -> bool {
        self.producers.is_empty()
    }

    pub fn uses(&self) -> impl Iterator<Item = &FactUse<F>> {
        self.producers.keys()
    }

    /// Each wait with the job that answers it, when one is named.
    pub fn iter(&self) -> impl Iterator<Item = (&FactUse<F>, Option<&J>)> {
        self.producers
            .iter()
            .map(|(usage, producer)| (usage, producer.as_ref()))
    }

    /// The jobs these waits stand on: the out-edges of the waiting job.
    pub fn producers(&self) -> impl Iterator<Item = &J> {
        self.producers.values().flatten()
    }
}

impl<F: Eq + Hash, J> FromIterator<(FactUse<F>, Option<J>)> for StandingWaits<F, J> {
    fn from_iter<I: IntoIterator<Item = (FactUse<F>, Option<J>)>>(pairs: I) -> Self {
        Self {
            producers: pairs.into_iter().collect(),
        }
    }
}
