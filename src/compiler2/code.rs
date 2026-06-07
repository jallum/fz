use std::rc::Rc;

use crate::ast::Item;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct CodeId(u32);

impl CodeId {
    pub const ZERO: Self = Self(0);

    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone)]
pub struct Code {
    state: CodeState,
    revision: u64,
}

impl Code {
    pub fn state(&self) -> &CodeState {
        &self.state
    }

    pub fn revision(&self) -> u64 {
        self.revision
    }
}

#[derive(Debug, Clone)]
pub enum CodeState {
    Pending,
    Indexed { items: Vec<Rc<Item>> },
}

#[derive(Debug, Default)]
pub struct CodeMap {
    slots: Vec<Code>,
    names: Vec<Option<String>>,
    texts: Vec<String>,
}

impl CodeMap {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn define(&mut self, name: Option<String>, text: String) -> CodeId {
        let id = CodeId(self.slots.len() as u32);
        self.slots.push(Code {
            state: CodeState::Pending,
            revision: 0,
        });
        self.names.push(name);
        self.texts.push(text);
        id
    }

    pub fn index(&mut self, id: CodeId, items: Vec<Rc<Item>>) -> u64 {
        let code = &mut self.slots[id.0 as usize];
        let next = CodeState::Indexed { items };
        if same_code_state(&code.state, &next) {
            return code.revision;
        }
        code.state = next;
        code.revision += 1;
        code.revision
    }

    pub fn get(&self, id: CodeId) -> Option<&Code> {
        self.slots.get(id.0 as usize)
    }

    pub fn name(&self, id: CodeId) -> Option<&str> {
        self.names.get(id.0 as usize).and_then(|name| name.as_deref())
    }

    pub fn text(&self, id: CodeId) -> &str {
        self.texts
            .get(id.0 as usize)
            .map(String::as_str)
            .expect("code ids should have source text")
    }

    pub fn len(&self) -> usize {
        self.slots.len()
    }

    pub fn is_empty(&self) -> bool {
        self.slots.is_empty()
    }
}

fn same_code_state(left: &CodeState, right: &CodeState) -> bool {
    match (left, right) {
        (CodeState::Pending, CodeState::Pending) => true,
        (CodeState::Indexed { items: left }, CodeState::Indexed { items: right }) => same_items(left, right),
        _ => false,
    }
}

fn same_items(left: &[Rc<Item>], right: &[Rc<Item>]) -> bool {
    left.len() == right.len() && left.iter().zip(right).all(|(left, right)| Rc::ptr_eq(left, right))
}
