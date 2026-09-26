//! Immutable source denotations shared by the compiler and runtime.

use crate::any_value::ClosureDenotationId;
use crate::module_name::{ModuleDenotation, ModuleName};
use std::cmp::Ordering;
use std::sync::Arc;

/// One lambda occurrence in a decoded source function, retained through cloning.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct LambdaOccurrence(u32);

impl LambdaOccurrence {
    pub fn from_u32(index: u32) -> Self {
        Self(index)
    }
    pub fn as_u32(self) -> u32 {
        self.0
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDenotation {
    pub origin: FunctionOrigin,
    pub arity: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FunctionOrigin {
    Named {
        module: Option<ModuleDenotation>,
        name: String,
    },
    Generated {
        owner: Arc<FunctionDenotation>,
        occurrence: LambdaOccurrence,
    },
}

impl FunctionDenotation {
    pub fn named(module: Option<ModuleName>, name: String, arity: usize) -> Self {
        Self {
            origin: FunctionOrigin::Named {
                module: module.map(ModuleDenotation::Named),
                name,
            },
            arity,
        }
    }
    pub fn source_name(&self) -> Option<&str> {
        match &self.origin {
            FunctionOrigin::Named { name, .. } => Some(name),
            FunctionOrigin::Generated { .. } => None,
        }
    }

    pub fn name(&self) -> &str {
        self.source_name().expect("a named function has a source identifier")
    }

    pub fn lexical_owner(&self) -> &Self {
        match &self.origin {
            FunctionOrigin::Named { .. } => self,
            FunctionOrigin::Generated { owner, .. } => owner.lexical_owner(),
        }
    }

    pub fn is_named(&self, name: &str) -> bool {
        self.source_name() == Some(name)
    }
    pub fn is_generated(&self) -> bool {
        matches!(self.origin, FunctionOrigin::Generated { .. })
    }
    pub fn display_name(&self) -> String {
        self.source_name().map(str::to_owned).unwrap_or_else(|| self.label())
    }

    pub fn semantic_cmp(&self, other: &Self) -> Ordering {
        match (&self.origin, &other.origin) {
            (FunctionOrigin::Named { module: lm, name: ln }, FunctionOrigin::Named { module: rm, name: rn }) => {
                lm.cmp(rm).then_with(|| ln.cmp(rn))
            }
            (FunctionOrigin::Named { .. }, FunctionOrigin::Generated { .. }) => Ordering::Less,
            (FunctionOrigin::Generated { .. }, FunctionOrigin::Named { .. }) => Ordering::Greater,
            (
                FunctionOrigin::Generated {
                    owner: lo,
                    occurrence: lp,
                },
                FunctionOrigin::Generated {
                    owner: ro,
                    occurrence: rp,
                },
            ) => lo.semantic_cmp(ro).then_with(|| lp.cmp(rp)),
        }
        .then_with(|| self.arity.cmp(&other.arity))
    }

    pub fn label(&self) -> String {
        match &self.origin {
            FunctionOrigin::Named { module, name } => match module {
                Some(module) => format!("{module}.{name}/{}", self.arity),
                None => format!("{name}/{}", self.arity),
            },
            FunctionOrigin::Generated { owner, occurrence } => {
                format!("{}#lambda@{}/{}", owner.label(), occurrence.as_u32(), self.arity)
            }
        }
    }
}

/// Encode the host-native AOT carrier directly from typed source fields.
/// Table order and IDs are preserved as transport coordinates, never sorted.
pub fn encode_closure_denotations(
    table: &[(ClosureDenotationId, Arc<FunctionDenotation>)],
) -> Result<Vec<u8>, &'static str> {
    let mut bytes = Vec::new();
    encode_u32(&mut bytes, table.len())?;
    for (id, denotation) in table {
        if *id == ClosureDenotationId::INTERNAL {
            return Err("internal continuation has no source denotation");
        }
        encode_u32(&mut bytes, id.as_u32() as usize)?;
        let mut current = denotation.as_ref();
        loop {
            encode_u32(&mut bytes, current.arity)?;
            match &current.origin {
                FunctionOrigin::Named { module, name } => {
                    bytes.push(0);
                    match module {
                        None => bytes.push(0),
                        Some(ModuleDenotation::Named(name)) => {
                            bytes.push(1);
                            encode_module_name(&mut bytes, name)?;
                        }
                        Some(ModuleDenotation::ProtocolImpl { protocol, target }) => {
                            bytes.push(2);
                            encode_module_name(&mut bytes, protocol)?;
                            encode_module_name(&mut bytes, target)?;
                        }
                    }
                    encode_string(&mut bytes, name)?;
                    break;
                }
                FunctionOrigin::Generated { owner, occurrence } => {
                    bytes.push(1);
                    encode_u32(&mut bytes, occurrence.as_u32() as usize)?;
                    current = owner;
                }
            }
        }
    }
    Ok(bytes)
}

fn encode_u32(bytes: &mut Vec<u8>, value: usize) -> Result<(), &'static str> {
    bytes.extend_from_slice(
        &u32::try_from(value)
            .map_err(|_| "source denotation field exceeds u32")?
            .to_ne_bytes(),
    );
    Ok(())
}

fn encode_string(bytes: &mut Vec<u8>, value: &str) -> Result<(), &'static str> {
    encode_u32(bytes, value.len())?;
    bytes.extend_from_slice(value.as_bytes());
    Ok(())
}

fn encode_module_name(bytes: &mut Vec<u8>, name: &ModuleName) -> Result<(), &'static str> {
    encode_u32(bytes, name.segments().len())?;
    for segment in name.segments() {
        encode_string(bytes, segment)?;
    }
    Ok(())
}

/// Decode the complete carrier, rejecting malformed tags, text and identities.
pub fn decode_closure_denotations(
    bytes: &[u8],
) -> Result<Vec<(ClosureDenotationId, Arc<FunctionDenotation>)>, &'static str> {
    let mut reader = DenotationReader(bytes);
    let count = reader.u32()?;
    let mut table = Vec::new();
    for _ in 0..count {
        let id = ClosureDenotationId::from_runtime_word(reader.u32()?);
        if id == ClosureDenotationId::INTERNAL {
            return Err("internal continuation has no source denotation");
        }
        table.push((id, reader.denotation()?));
    }
    if !reader.0.is_empty() {
        return Err("trailing source denotation bytes");
    }
    Ok(table)
}

struct DenotationReader<'a>(&'a [u8]);

impl<'a> DenotationReader<'a> {
    fn take(&mut self, length: usize) -> Result<&'a [u8], &'static str> {
        let (value, remaining) = self.0.split_at_checked(length).ok_or("truncated source denotation")?;
        self.0 = remaining;
        Ok(value)
    }

    fn u32(&mut self) -> Result<u32, &'static str> {
        Ok(u32::from_ne_bytes(self.take(4)?.try_into().expect("four-byte field")))
    }

    fn tag(&mut self) -> Result<u8, &'static str> {
        Ok(self.take(1)?[0])
    }

    fn string(&mut self) -> Result<String, &'static str> {
        let length = self.u32()? as usize;
        Ok(std::str::from_utf8(self.take(length)?)
            .map_err(|_| "invalid source denotation UTF-8")?
            .to_owned())
    }

    fn module_name(&mut self) -> Result<ModuleName, &'static str> {
        let count = self.u32()?;
        if count == 0 {
            return Err("empty source module");
        }
        let mut segments = Vec::new();
        for _ in 0..count {
            let segment = self.string()?;
            if segment.is_empty() {
                return Err("empty source module segment");
            }
            segments.push(segment);
        }
        Ok(ModuleName::from_segments(segments))
    }

    fn module(&mut self) -> Result<Option<ModuleDenotation>, &'static str> {
        match self.tag()? {
            0 => Ok(None),
            1 => Ok(Some(ModuleDenotation::Named(self.module_name()?))),
            2 => Ok(Some(ModuleDenotation::ProtocolImpl {
                protocol: self.module_name()?,
                target: self.module_name()?,
            })),
            _ => Err("invalid source module tag"),
        }
    }

    fn denotation(&mut self) -> Result<Arc<FunctionDenotation>, &'static str> {
        let mut generated = Vec::new();
        let mut denotation = loop {
            let arity = self.u32()? as usize;
            match self.tag()? {
                0 => {
                    break Arc::new(FunctionDenotation {
                        origin: FunctionOrigin::Named {
                            module: self.module()?,
                            name: self.string()?,
                        },
                        arity,
                    });
                }
                1 => generated.push((arity, LambdaOccurrence::from_u32(self.u32()?))),
                _ => return Err("invalid source denotation tag"),
            }
        };
        for (arity, occurrence) in generated.into_iter().rev() {
            denotation = Arc::new(FunctionDenotation {
                arity,
                origin: FunctionOrigin::Generated {
                    owner: denotation,
                    occurrence,
                },
            });
        }
        Ok(denotation)
    }
}

#[cfg(test)]
#[path = "function_denotation_test.rs"]
mod function_denotation_test;
