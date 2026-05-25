#![allow(dead_code)]
//! Backend-neutral module slot and code image lifetime model.
//!
//! This module is intentionally introduced before interpreter/JIT routing so
//! the replacement and purge semantics are testable in isolation.

use crate::ast::ModuleName;
use crate::fz_ir::{ExportKey, FnId};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ImageId(pub u64);

#[derive(Debug)]
pub struct CodeImage<I> {
    id: ImageId,
    module: ModuleName,
    exports: HashMap<ExportKey, FnId>,
    payload: I,
}

impl<I> CodeImage<I> {
    fn new(id: ImageId, module: ModuleName, exports: HashMap<ExportKey, FnId>, payload: I) -> Self {
        Self {
            id,
            module,
            exports,
            payload,
        }
    }

    pub fn id(&self) -> ImageId {
        self.id
    }

    pub fn module(&self) -> &ModuleName {
        &self.module
    }

    pub fn local_fn_for_export(&self, key: &ExportKey) -> Option<FnId> {
        self.exports.get(key).copied()
    }

    pub fn payload(&self) -> &I {
        &self.payload
    }
}

#[derive(Debug)]
pub struct ModuleSlot<I> {
    current: Arc<CodeImage<I>>,
    old: Option<Arc<CodeImage<I>>>,
}

impl<I> ModuleSlot<I> {
    pub fn current(&self) -> Arc<CodeImage<I>> {
        self.current.clone()
    }

    pub fn old(&self) -> Option<Arc<CodeImage<I>>> {
        self.old.clone()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SoftPurge {
    Purged(ImageId),
    NoOldImage,
    RefusedPinned(ImageId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HardPurge {
    Purged(ImageId),
    NoOldImage,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CodeServerError {
    MissingModule(ModuleName),
    MissingExport(ExportKey),
    OldImagePinned {
        module: ModuleName,
        old: ImageId,
    },
    CurrentImagePinned {
        module: ModuleName,
        current: ImageId,
    },
}

#[derive(Debug)]
pub struct CodeServer<I> {
    next_image_id: u64,
    slots: HashMap<ModuleName, ModuleSlot<I>>,
}

impl<I> Default for CodeServer<I> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I> CodeServer<I> {
    pub fn new() -> Self {
        Self {
            next_image_id: 0,
            slots: HashMap::new(),
        }
    }

    pub fn load(
        &mut self,
        module: ModuleName,
        exports: HashMap<ExportKey, FnId>,
        payload: I,
    ) -> Result<Arc<CodeImage<I>>, CodeServerError> {
        if let Some(slot) = self.slots.get(&module)
            && let Some(old) = &slot.old
            && Arc::strong_count(old) > 1
        {
            return Err(CodeServerError::OldImagePinned {
                module,
                old: old.id(),
            });
        }

        let image = Arc::new(CodeImage::new(
            self.fresh_image_id(),
            module.clone(),
            exports,
            payload,
        ));
        match self.slots.get_mut(&module) {
            Some(slot) => {
                let previous_current = std::mem::replace(&mut slot.current, image.clone());
                slot.old = Some(previous_current);
            }
            None => {
                self.slots.insert(
                    module,
                    ModuleSlot {
                        current: image.clone(),
                        old: None,
                    },
                );
            }
        }
        Ok(image)
    }

    pub fn slot(&self, module: &ModuleName) -> Option<&ModuleSlot<I>> {
        self.slots.get(module)
    }

    pub fn resolve_export(
        &self,
        key: &ExportKey,
    ) -> Result<(Arc<CodeImage<I>>, FnId), CodeServerError> {
        let slot = self
            .slots
            .get(&key.module)
            .ok_or_else(|| CodeServerError::MissingModule(key.module.clone()))?;
        let image = slot.current();
        let local_fn = image
            .local_fn_for_export(key)
            .ok_or_else(|| CodeServerError::MissingExport(key.clone()))?;
        Ok((image, local_fn))
    }

    pub fn soft_purge_old(&mut self, module: &ModuleName) -> Result<SoftPurge, CodeServerError> {
        let slot = self
            .slots
            .get_mut(module)
            .ok_or_else(|| CodeServerError::MissingModule(module.clone()))?;
        let Some(old) = slot.old.as_ref() else {
            return Ok(SoftPurge::NoOldImage);
        };
        if Arc::strong_count(old) > 1 {
            return Ok(SoftPurge::RefusedPinned(old.id()));
        }
        let old = slot.old.take().expect("old image checked above");
        Ok(SoftPurge::Purged(old.id()))
    }

    pub fn hard_purge_old(&mut self, module: &ModuleName) -> Result<HardPurge, CodeServerError> {
        let slot = self
            .slots
            .get_mut(module)
            .ok_or_else(|| CodeServerError::MissingModule(module.clone()))?;
        let Some(old) = slot.old.take() else {
            return Ok(HardPurge::NoOldImage);
        };
        Ok(HardPurge::Purged(old.id()))
    }

    pub fn delete_module(&mut self, module: &ModuleName) -> Result<(), CodeServerError> {
        let Some(slot) = self.slots.get(module) else {
            return Err(CodeServerError::MissingModule(module.clone()));
        };
        if Arc::strong_count(&slot.current) > 1 {
            return Err(CodeServerError::CurrentImagePinned {
                module: module.clone(),
                current: slot.current.id(),
            });
        }
        if let Some(old) = &slot.old
            && Arc::strong_count(old) > 1
        {
            return Err(CodeServerError::OldImagePinned {
                module: module.clone(),
                old: old.id(),
            });
        }
        self.slots.remove(module);
        Ok(())
    }

    pub fn hard_delete_module(&mut self, module: &ModuleName) -> Result<(), CodeServerError> {
        self.slots
            .remove(module)
            .map(|_| ())
            .ok_or_else(|| CodeServerError::MissingModule(module.clone()))
    }

    fn fresh_image_id(&mut self) -> ImageId {
        let id = ImageId(self.next_image_id);
        self.next_image_id += 1;
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(name: &str) -> ModuleName {
        ModuleName::from_segments(vec![name.to_string()])
    }

    fn export(module: &ModuleName, name: &str, arity: usize) -> ExportKey {
        ExportKey {
            module: module.clone(),
            name: name.to_string(),
            arity,
        }
    }

    fn exports(
        module: &ModuleName,
        name: &str,
        arity: usize,
        fn_id: u32,
    ) -> HashMap<ExportKey, FnId> {
        HashMap::from([(export(module, name, arity), FnId(fn_id))])
    }

    #[test]
    fn first_load_creates_current_image() {
        let m = module("M");
        let key = export(&m, "f", 1);
        let mut server = CodeServer::new();
        let loaded = server
            .load(m.clone(), exports(&m, "f", 1, 7), "v1")
            .expect("load");

        assert_eq!(loaded.id(), ImageId(0));
        assert!(server.slot(&m).expect("slot").old().is_none());
        let (image, local_fn) = server.resolve_export(&key).expect("resolve");
        assert_eq!(image.id(), ImageId(0));
        assert_eq!(local_fn, FnId(7));
    }

    #[test]
    fn replacement_moves_current_to_old() {
        let m = module("M");
        let mut server = CodeServer::new();
        let v1 = server
            .load(m.clone(), exports(&m, "f", 1, 1), "v1")
            .expect("v1");
        let v2 = server
            .load(m.clone(), exports(&m, "f", 1, 2), "v2")
            .expect("v2");

        let slot = server.slot(&m).expect("slot");
        assert_eq!(slot.current().id(), v2.id());
        assert_eq!(slot.old().expect("old").id(), v1.id());
        assert_eq!(
            server
                .resolve_export(&export(&m, "f", 1))
                .expect("resolve")
                .1,
            FnId(2)
        );
    }

    #[test]
    fn third_load_refuses_when_old_image_is_pinned() {
        let m = module("M");
        let mut server = CodeServer::new();
        let v1 = server
            .load(m.clone(), exports(&m, "f", 1, 1), "v1")
            .expect("v1");
        let _pin = v1.clone();
        server
            .load(m.clone(), exports(&m, "f", 1, 2), "v2")
            .expect("v2");

        let err = server
            .load(m.clone(), exports(&m, "f", 1, 3), "v3")
            .expect_err("old image should be pinned");
        assert_eq!(
            err,
            CodeServerError::OldImagePinned {
                module: m,
                old: ImageId(0),
            }
        );
    }

    #[test]
    fn third_load_replaces_unpinned_old_image() {
        let m = module("M");
        let mut server = CodeServer::new();
        server
            .load(m.clone(), exports(&m, "f", 1, 1), "v1")
            .expect("v1");
        server
            .load(m.clone(), exports(&m, "f", 1, 2), "v2")
            .expect("v2");
        server
            .load(m.clone(), exports(&m, "f", 1, 3), "v3")
            .expect("v3");

        let slot = server.slot(&m).expect("slot");
        assert_eq!(slot.current().id(), ImageId(2));
        assert_eq!(slot.old().expect("old").id(), ImageId(1));
    }

    #[test]
    fn soft_purge_refuses_when_old_is_pinned() {
        let m = module("M");
        let mut server = CodeServer::new();
        server
            .load(m.clone(), exports(&m, "f", 1, 1), "v1")
            .expect("v1");
        server
            .load(m.clone(), exports(&m, "f", 1, 2), "v2")
            .expect("v2");
        let old_pin = server.slot(&m).expect("slot").old().expect("old");

        assert_eq!(
            server.soft_purge_old(&m).expect("purge"),
            SoftPurge::RefusedPinned(old_pin.id())
        );
        assert!(server.slot(&m).expect("slot").old().is_some());
    }

    #[test]
    fn soft_purge_removes_unpinned_old() {
        let m = module("M");
        let mut server = CodeServer::new();
        server
            .load(m.clone(), exports(&m, "f", 1, 1), "v1")
            .expect("v1");
        server
            .load(m.clone(), exports(&m, "f", 1, 2), "v2")
            .expect("v2");

        assert_eq!(
            server.soft_purge_old(&m).expect("purge"),
            SoftPurge::Purged(ImageId(0))
        );
        assert!(server.slot(&m).expect("slot").old().is_none());
    }

    #[test]
    fn hard_purge_detaches_old_even_when_pinned() {
        let m = module("M");
        let mut server = CodeServer::new();
        server
            .load(m.clone(), exports(&m, "f", 1, 1), "v1")
            .expect("v1");
        server
            .load(m.clone(), exports(&m, "f", 1, 2), "v2")
            .expect("v2");
        let old_pin = server.slot(&m).expect("slot").old().expect("old");

        assert_eq!(
            server.hard_purge_old(&m).expect("purge"),
            HardPurge::Purged(ImageId(0))
        );
        assert!(server.slot(&m).expect("slot").old().is_none());
        assert_eq!(old_pin.payload(), &"v1");
    }

    #[test]
    fn soft_delete_refuses_pinned_current() {
        let m = module("M");
        let mut server = CodeServer::new();
        let current = server
            .load(m.clone(), exports(&m, "f", 1, 1), "v1")
            .expect("v1");
        let _pin = current.clone();

        assert_eq!(
            server.delete_module(&m).expect_err("current pinned"),
            CodeServerError::CurrentImagePinned {
                module: m,
                current: ImageId(0),
            }
        );
    }
}
