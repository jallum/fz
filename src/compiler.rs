use crate::types;
use crate::types::DefaultTypes;

pub(crate) struct Compiler {
    types: DefaultTypes,
}

impl Compiler {
    pub(crate) fn new() -> Self {
        Self { types: types::new() }
    }

    pub(crate) fn types(&mut self) -> &mut DefaultTypes {
        &mut self.types
    }
}
