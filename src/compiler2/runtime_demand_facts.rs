use std::collections::HashMap;

use super::identity::ExecutableKey;
use super::semantic::ExecutableRuntimeDemand;

#[derive(Debug, Default)]
pub(crate) struct RuntimeDemandMap {
    slots: HashMap<ExecutableKey, ExecutableRuntimeDemand>,
}

impl RuntimeDemandMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn get(&self, key: &ExecutableKey) -> Option<&ExecutableRuntimeDemand> {
        self.slots.get(key)
    }

    pub(crate) fn define(&mut self, key: ExecutableKey, demand: ExecutableRuntimeDemand) -> bool {
        let changed = self.slots.get(&key) != Some(&demand);
        self.slots.insert(key, demand);
        changed
    }
}
