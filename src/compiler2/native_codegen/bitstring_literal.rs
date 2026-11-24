//! Where a program keeps the bitstring literals its code names.
//!
//! A literal of `SHARED_BIN_THRESHOLD_BYTES` or fewer is one read-only object
//! laid out like a heap bitstring: the header word, the bytes, and the
//! trailing NUL that lets an extern read it as a C string. Code names it by a
//! literal ref and allocates nothing. A longer literal is a static `SharedBin`
//! over its bytes, and naming it allocates the view that points at it.
//!
//! Equal literals share one object for the whole module.

use super::static_object::define_read_only_object;
use super::{CodegenError, define_static_sharedbin};
use crate::fast_hash::HashMap;
use cranelift_module::{DataDescription, DataId, Linkage, Module};
use fz_runtime::any_value::{BITSTRING_BYTES_OFFSET, bitstring_object_image};
use fz_runtime::heap::SHARED_BIN_THRESHOLD_BYTES;

/// The object a bitstring literal's code names.
#[derive(Clone, Copy)]
pub(crate) enum BitstringLiteral {
    /// A read-only bitstring object.
    Object(DataId),
    /// A static `SharedBin` a view is allocated over.
    Shared(DataId),
}

/// Where a literal's bytes sit: a data object and the offset into it.
#[derive(Clone, Copy)]
pub(crate) struct LiteralBytes {
    pub(crate) data: DataId,
    pub(crate) offset: i64,
}

/// A long literal's two objects: its bytes, and the `SharedBin` over them.
#[derive(Clone, Copy)]
struct SharedLiteral {
    bytes: DataId,
    shared: DataId,
}

/// The literals a module has emitted so far.
#[derive(Default)]
pub(crate) struct BitstringLiterals {
    objects: HashMap<(Vec<u8>, u64), DataId>,
    shared: HashMap<Vec<u8>, SharedLiteral>,
}

impl BitstringLiterals {
    /// The object for the literal `bytes` of `bit_len` bits, emitted on first use.
    pub(crate) fn literal<M: Module>(
        &mut self,
        jmod: &mut M,
        bytes: &[u8],
        bit_len: u64,
    ) -> Result<BitstringLiteral, CodegenError> {
        if bytes.len() > SHARED_BIN_THRESHOLD_BYTES {
            return self
                .shared(jmod, bytes)
                .map(|literal| BitstringLiteral::Shared(literal.shared));
        }
        if let Some(object) = self.objects.get(&(bytes.to_vec(), bit_len)) {
            return Ok(BitstringLiteral::Object(*object));
        }
        let name = format!(".fz_bs_literal_{}", self.objects.len());
        let object = define_read_only_object(jmod, &name, bitstring_object_image(bytes, bit_len), &[])?;
        self.objects.insert((bytes.to_vec(), bit_len), object);
        Ok(BitstringLiteral::Object(object))
    }

    /// Where the bytes of the literal `bytes` of `bit_len` bits are, read in
    /// place: nothing is allocated at run time.
    pub(crate) fn bytes_at<M: Module>(
        &mut self,
        jmod: &mut M,
        bytes: &[u8],
        bit_len: u64,
    ) -> Result<LiteralBytes, CodegenError> {
        Ok(match self.literal(jmod, bytes, bit_len)? {
            BitstringLiteral::Object(object) => LiteralBytes {
                data: object,
                offset: BITSTRING_BYTES_OFFSET as i64,
            },
            BitstringLiteral::Shared(_) => LiteralBytes {
                data: self.shared[bytes].bytes,
                offset: 0,
            },
        })
    }

    fn shared<M: Module>(&mut self, jmod: &mut M, bytes: &[u8]) -> Result<SharedLiteral, CodegenError> {
        if let Some(shared) = self.shared.get(bytes) {
            return Ok(*shared);
        }
        let index = self.shared.len();
        let name = format!(".fz_bs_const_{index}");
        let bytes_id = jmod
            .declare_data(&name, Linkage::Local, false, false)
            .map_err(|e| CodegenError::new(format!("declare {name}: {e}")))?;
        let mut desc = DataDescription::new();
        desc.define(nul_terminated(bytes).into_boxed_slice());
        desc.set_align(1);
        jmod.define_data(bytes_id, &desc)
            .map_err(|e| CodegenError::new(format!("define {name}: {e}")))?;
        let shared = SharedLiteral {
            bytes: bytes_id,
            shared: define_static_sharedbin(jmod, bytes_id, bytes, index)?,
        };
        self.shared.insert(bytes.to_vec(), shared);
        Ok(shared)
    }
}

/// `bytes` followed by the NUL a C string reader stops at. A `SharedBin`'s
/// length does not count it.
fn nul_terminated(bytes: &[u8]) -> Vec<u8> {
    let mut payload = bytes.to_vec();
    payload.push(0);
    payload
}
