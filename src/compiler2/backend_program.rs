//! Root snapshots share ordered contribution inventories between requests.

pub(crate) mod boxed_contract;
#[cfg(test)]
mod contribution_test;

#[cfg(test)]
use std::collections::BTreeMap;
use std::rc::Rc;

use super::artifact::{BackendConstructionWrapper, BackendExecutable};
use super::identity::{ExecutableKey, ModuleId};
use super::semantic::SemanticOrd;
use super::shared_order::SharedOrder;
use super::transport::TransportPosition;
use super::types::Types;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BackendSchema {
    pub module: ModuleId,
    pub name: Rc<String>,
    pub fields: Rc<Vec<String>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AtomOccurrence {
    Builtin(usize),
    Executable(ExecutableKey, usize),
}

impl SemanticOrd<Types> for AtomOccurrence {
    fn semantic_cmp(&self, other: &Self, types: &Types) -> std::cmp::Ordering {
        match (self, other) {
            (Self::Builtin(left), Self::Builtin(right)) => left.cmp(right),
            (Self::Builtin(_), Self::Executable(..)) => std::cmp::Ordering::Less,
            (Self::Executable(..), Self::Builtin(_)) => std::cmp::Ordering::Greater,
            (Self::Executable(left, index), Self::Executable(right, next)) => {
                left.semantic_cmp(right, types).then_with(|| index.cmp(next))
            }
        }
    }
}

type AtomOwners = SharedOrder<AtomOccurrence, Rc<String>>;
type WrapperOwners = SharedOrder<ExecutableKey, ()>;

type WrapperChange = (
    Option<Rc<BackendConstructionWrapper>>,
    Option<Rc<BackendConstructionWrapper>>,
);

fn changed_wrappers(
    previous: Option<&BackendExecutable>,
    next: Option<&BackendExecutable>,
    types: &Types,
) -> Vec<WrapperChange> {
    let mut previous = previous
        .into_iter()
        .flat_map(|body| body.construction_wrappers.iter())
        .peekable();
    let mut next = next
        .into_iter()
        .flat_map(|body| body.construction_wrappers.iter())
        .peekable();
    let mut changes = Vec::new();
    loop {
        match (previous.peek(), next.peek()) {
            (Some(left), Some(right)) => match left.identity.semantic_cmp(&right.identity, types) {
                std::cmp::Ordering::Less => changes.push((previous.next().cloned(), None)),
                std::cmp::Ordering::Greater => changes.push((None, next.next().cloned())),
                std::cmp::Ordering::Equal => {
                    let left = previous.next().unwrap();
                    let right = next.next().unwrap();
                    if left != right {
                        changes.push((Some(Rc::clone(left)), Some(Rc::clone(right))));
                    }
                }
            },
            (Some(_), None) => changes.push((previous.next().cloned(), None)),
            (None, Some(_)) => changes.push((None, next.next().cloned())),
            (None, None) => return changes,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct BackendProgram {
    entry: ExecutableKey,
    pub atom_names: SharedOrder<AtomOccurrence, Rc<String>>,
    pub struct_schemas: SharedOrder<Rc<String>, Rc<Vec<String>>>,
    executables: SharedOrder<ExecutableKey, Rc<BackendExecutable>>,
    construction_wrappers: SharedOrder<Rc<TransportPosition>, Rc<BackendConstructionWrapper>>,
    atom_owners: SharedOrder<Rc<String>, AtomOwners>,
    wrapper_owners: SharedOrder<Rc<TransportPosition>, WrapperOwners>,
    schemas: SharedOrder<ModuleId, Rc<BackendSchema>>,
    boxed_contract: boxed_contract::BoxedContracts,
}

impl BackendProgram {
    pub fn entry(&self) -> &ExecutableKey {
        &self.entry
    }
    pub fn executables(&self) -> &SharedOrder<ExecutableKey, Rc<BackendExecutable>> {
        &self.executables
    }
    pub fn construction_wrappers(&self) -> &SharedOrder<Rc<TransportPosition>, Rc<BackendConstructionWrapper>> {
        &self.construction_wrappers
    }

    pub fn executable_index(&self, key: &ExecutableKey, types: &Types) -> Option<usize> {
        self.executables
            .rank(key, &|left, right| left.semantic_cmp(right, types))
    }

    pub fn construction_index(&self, key: &TransportPosition, types: &Types) -> Option<usize> {
        self.construction_wrappers
            .rank(key, &|left, right| left.semantic_cmp(right.as_ref(), types))
    }

    pub fn executable(&self, key: &ExecutableKey, types: &Types) -> Option<&Rc<BackendExecutable>> {
        self.executables
            .lookup(key, &|left, right| left.semantic_cmp(right, types))
    }

    pub fn schema(&self, name: &str) -> Option<&Vec<String>> {
        self.struct_schemas
            .lookup(name, &|left, right| left.cmp(right.as_str()))
            .map(Rc::as_ref)
    }

    pub(crate) fn empty(entry: ExecutableKey) -> Self {
        Self {
            entry,
            atom_names: SharedOrder::default(),
            struct_schemas: SharedOrder::default(),
            executables: SharedOrder::default(),
            construction_wrappers: SharedOrder::default(),
            atom_owners: SharedOrder::default(),
            wrapper_owners: SharedOrder::default(),
            schemas: SharedOrder::default(),
            boxed_contract: boxed_contract::BoxedContracts::default(),
        }
    }

    pub(crate) fn set_entry(&mut self, entry: ExecutableKey) {
        self.entry = entry;
    }

    pub(crate) fn validate_boxed_contract(
        &self,
        tel: &impl crate::telemetry::Telemetry,
        root: super::RootId,
    ) -> Result<(), super::scheduler::FatalError> {
        self.boxed_contract.validate(tel, root)
    }

    pub(crate) fn add_builtins(&mut self, types: &Types) {
        for (index, atom) in ["nil", "true", "false"].into_iter().enumerate() {
            self.add_atom(Rc::new(atom.to_string()), AtomOccurrence::Builtin(index), types);
        }
    }

    fn add_atom(&mut self, atom: Rc<String>, occurrence: AtomOccurrence, types: &Types) {
        let mut owners = self.atom_owners.lookup(&atom, &Rc::cmp).cloned().unwrap_or_default();
        let previous = owners.entries().next().map(|(key, _)| key.clone());
        let atom = previous
            .as_ref()
            .and_then(|key| {
                self.atom_names
                    .lookup(key, &|left, right| left.semantic_cmp(right, types))
            })
            .cloned()
            .unwrap_or(atom);
        owners.insert(occurrence, Rc::clone(&atom), &|left, right| {
            left.semantic_cmp(right, types)
        });
        let (first, name) = owners.entries().next().expect("an added atom has an owner");
        if previous.as_ref() != Some(first) {
            if let Some(previous) = previous {
                self.atom_names
                    .remove(&previous, &|left, right| left.semantic_cmp(right, types));
            }
            self.atom_names.insert(first.clone(), Rc::clone(name), &|left, right| {
                left.semantic_cmp(right, types)
            });
        }
        self.atom_owners.insert(atom, owners, &Rc::cmp);
    }

    fn remove_atom(&mut self, atom: &Rc<String>, occurrence: &AtomOccurrence, types: &Types) {
        let mut owners = self
            .atom_owners
            .lookup(atom, &Rc::cmp)
            .expect("registered atom contribution")
            .clone();
        let previous = owners.entries().next().expect("registered atom owner").0.clone();
        let retained_name = Rc::clone(
            self.atom_names
                .lookup(&previous, &|left, right| left.semantic_cmp(right, types))
                .expect("published atom"),
        );
        owners.remove(occurrence, &|left, right| left.semantic_cmp(right, types));
        if owners.is_empty() {
            self.atom_owners.remove(atom, &Rc::cmp);
            self.atom_names
                .remove(&previous, &|left, right| left.semantic_cmp(right, types));
        } else {
            let (first, _) = owners.entries().next().expect("remaining atom owner");
            if *first != previous {
                self.atom_names
                    .remove(&previous, &|left, right| left.semantic_cmp(right, types));
                self.atom_names.insert(first.clone(), retained_name, &|left, right| {
                    left.semantic_cmp(right, types)
                });
            }
            self.atom_owners.insert(Rc::clone(atom), owners, &Rc::cmp);
        }
    }

    #[cfg(test)]
    pub(crate) fn remove_executable(&mut self, key: &ExecutableKey, types: &Types) {
        self.reconcile_executables(vec![(key.clone(), None)], types);
    }

    pub(crate) fn reconcile_executables(
        &mut self,
        changes: Vec<(ExecutableKey, Option<Rc<BackendExecutable>>)>,
        types: &Types,
    ) {
        let changes = changes
            .into_iter()
            .map(|(key, next)| {
                let previous = self.executable(&key, types).cloned();
                let wrappers = changed_wrappers(previous.as_deref(), next.as_deref(), types);
                let atoms = next
                    .iter()
                    .flat_map(|body| body.atom_names.iter())
                    .enumerate()
                    .map(|(index, atom)| {
                        if previous.as_ref().and_then(|body| body.atom_names.get(index)) == Some(atom) {
                            return None;
                        }
                        let published = self
                            .atom_owners
                            .lookup(atom, &Rc::cmp)
                            .and_then(|owners| owners.entries().next())
                            .and_then(|(occurrence, _)| {
                                self.atom_names
                                    .lookup(occurrence, &|left, right| left.semantic_cmp(right, types))
                            });
                        Some(Rc::clone(published.unwrap_or(atom)))
                    })
                    .collect::<Vec<_>>();
                (key, previous, next, wrappers, atoms)
            })
            .collect::<Vec<_>>();
        // Retire changed local rows before installing replacements. Other owners
        // may replace the same complete wrapper in this transaction.
        for (key, previous, next, wrappers, _) in &changes {
            self.boxed_contract.replace_caller(
                key,
                previous
                    .as_ref()
                    .map_or(&[], |backend| backend.boxed_apply_requirements.as_ref()),
                next.as_ref()
                    .map_or(&[], |backend| backend.boxed_apply_requirements.as_ref()),
                types,
            );
            for (index, atom) in previous
                .iter()
                .flat_map(|previous| previous.atom_names.iter())
                .enumerate()
            {
                if next.as_ref().and_then(|next| next.atom_names.get(index)) != Some(atom) {
                    self.remove_atom(atom, &AtomOccurrence::Executable(key.clone(), index), types);
                }
            }
            for (wrapper, _) in wrappers {
                let Some(wrapper) = wrapper else {
                    continue;
                };
                self.remove_wrapper(key, &wrapper.identity, types);
            }
        }
        for (key, _, next, wrappers, atoms) in changes {
            let Some(next) = next else {
                self.executables
                    .remove(&key, &|left, right| left.semantic_cmp(right, types));
                continue;
            };
            for (index, atom) in atoms.iter().enumerate() {
                if let Some(atom) = atom {
                    self.add_atom(Rc::clone(atom), AtomOccurrence::Executable(key.clone(), index), types);
                }
            }
            for (_, wrapper) in wrappers {
                let Some(wrapper) = wrapper else {
                    continue;
                };
                self.add_wrapper(&key, &wrapper, types);
            }
            self.executables
                .insert(key, next, &|left, right| left.semantic_cmp(right, types));
        }
    }

    fn remove_wrapper(&mut self, owner: &ExecutableKey, position: &TransportPosition, types: &Types) {
        let mut owners = self
            .wrapper_owners
            .lookup(position, &|left, right| left.semantic_cmp(right.as_ref(), types))
            .expect("registered wrapper")
            .clone();
        owners.remove(owner, &|left, right| left.semantic_cmp(right, types));
        if owners.is_empty() {
            let previous = self
                .construction_wrappers
                .lookup(position, &|left, right| left.semantic_cmp(right.as_ref(), types))
                .expect("published wrapper");
            self.boxed_contract.replace_wrapper(Some(previous), None, types);
            self.wrapper_owners
                .remove(position, &|left, right| left.semantic_cmp(right.as_ref(), types));
            self.construction_wrappers
                .remove(position, &|left, right| left.semantic_cmp(right.as_ref(), types));
        } else {
            self.wrapper_owners
                .insert(Rc::new(position.clone()), owners, &|left, right| {
                    left.semantic_cmp(right, types)
                });
        }
    }

    fn add_wrapper(&mut self, owner: &ExecutableKey, wrapper: &Rc<BackendConstructionWrapper>, types: &Types) {
        let identity = Rc::new(wrapper.identity.clone());
        let mut owners = self
            .wrapper_owners
            .lookup(&identity, &|left, right| left.semantic_cmp(right, types))
            .cloned()
            .unwrap_or_default();
        if let Some(previous) = self
            .construction_wrappers
            .lookup(&identity, &|left, right| left.semantic_cmp(right, types))
        {
            assert_eq!(previous, wrapper, "one construction position has one complete wrapper");
        } else {
            self.boxed_contract.replace_wrapper(None, Some(wrapper), types);
        }
        owners.insert(owner.clone(), (), &|left, right| left.semantic_cmp(right, types));
        self.wrapper_owners
            .insert(Rc::clone(&identity), owners, &|left, right| {
                left.semantic_cmp(right, types)
            });
        self.construction_wrappers
            .insert(identity, Rc::clone(wrapper), &|left, right| {
                left.semantic_cmp(right, types)
            });
    }

    #[cfg(test)]
    pub(crate) fn add_executable(&mut self, backend: Rc<BackendExecutable>, types: &Types) {
        self.reconcile_executables(vec![(backend.key.clone(), Some(backend))], types);
    }

    pub(crate) fn replace_schema(&mut self, module: ModuleId, next: Option<Rc<BackendSchema>>) {
        if let Some(previous) = self.schemas.remove(&module, &ModuleId::cmp) {
            self.struct_schemas.remove(&previous.name, &Rc::cmp);
        }
        if let Some(schema) = next {
            self.struct_schemas
                .insert(Rc::clone(&schema.name), Rc::clone(&schema.fields), &Rc::cmp);
            self.schemas.insert(module, schema, &ModuleId::cmp);
        }
    }

    #[cfg(test)]
    pub(crate) fn empty_for_test() -> Self {
        let mut world = super::World::new();
        let function = world.reference_function(ModuleId::GLOBAL, "test_entry", 0);
        Self::empty(ExecutableKey {
            activation: super::ActivationKey::from_inputs(super::RootId::for_test(0), function, &[], world.types_mut()),
            need: super::ExecutableNeed::Value,
        })
    }

    #[cfg(test)]
    pub fn new(
        entry: ExecutableKey,
        atoms: Vec<String>,
        schemas: BTreeMap<String, Vec<String>>,
        executables: Vec<Rc<BackendExecutable>>,
        wrappers: Vec<Rc<BackendConstructionWrapper>>,
        types: &Types,
    ) -> Self {
        let mut program = Self::empty(entry);
        for (index, atom) in atoms.into_iter().enumerate() {
            program.add_atom(Rc::new(atom), AtomOccurrence::Builtin(index), types);
        }
        for (name, fields) in schemas {
            program.struct_schemas.insert(Rc::new(name), Rc::new(fields), &Rc::cmp);
        }
        for executable in executables {
            assert!(
                program.executable(&executable.key, types).is_none(),
                "duplicate backend executable identity"
            );
            program.add_executable(executable, types);
        }
        assert!(
            program.executable(program.entry(), types).is_some(),
            "backend entry must belong to its program"
        );
        let mut supplied = std::collections::HashSet::new();
        for wrapper in wrappers {
            let key = Rc::new(wrapper.identity.clone());
            assert!(
                supplied.insert(Rc::clone(&key)),
                "duplicate backend construction identity"
            );
            program
                .construction_wrappers
                .insert(key, wrapper, &|left, right| left.semantic_cmp(right, types));
        }
        program
    }
}
