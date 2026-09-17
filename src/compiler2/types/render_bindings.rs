use std::collections::HashMap;

use super::Ty;

pub(super) enum BindingVisit {
    Fresh,
    Reference(String),
}

#[derive(Default)]
pub(super) struct RenderBindings {
    active: HashMap<Ty, Option<String>>,
    next: usize,
}

impl RenderBindings {
    pub(super) fn reset(&mut self) {
        assert!(self.active.is_empty(), "a recursive render left an active binding");
        self.next = 0;
    }

    pub(super) fn enter(&mut self, ty: Ty) -> BindingVisit {
        if let Some(Some(name)) = self.active.get(&ty) {
            return BindingVisit::Reference(name.clone());
        }
        if self.active.contains_key(&ty) {
            return BindingVisit::Reference(self.reference(ty));
        }
        self.active.insert(ty, None);
        BindingVisit::Fresh
    }

    pub(super) fn reference(&mut self, ty: Ty) -> String {
        if let Some(Some(name)) = self.active.get(&ty) {
            return name.clone();
        }
        let name = self.next_name();
        *self
            .active
            .get_mut(&ty)
            .expect("a recursive render lost an active binding") = Some(name.clone());
        name
    }

    pub(super) fn finish(&mut self, ty: Ty, body: String) -> String {
        match self.active.remove(&ty).expect("a rendered type was not active") {
            Some(name) => format!("μ{name}. {body}"),
            None => body,
        }
    }

    fn next_name(&mut self) -> String {
        const NAMES: [&str; 26] = [
            "X", "Y", "Z", "W", "V", "U", "T", "S", "R", "Q", "P", "O", "N", "M", "L", "K", "J", "I", "H", "G", "F",
            "E", "D", "C", "B", "A",
        ];
        let index = self.next;
        self.next += 1;
        NAMES
            .get(index)
            .map_or_else(|| format!("X{index}"), ToString::to_string)
    }
}
