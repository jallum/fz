use crate::type_expr::opaque_owner_module;
use crate::types::Types;
use std::fmt::{self, Display, Formatter};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpaqueVisibilityError {
    pub opaque: String,
    pub owner_module: String,
    pub using_module: String,
}

impl Display for OpaqueVisibilityError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "field of opaque type `{}` is not accessible from module `{}` \
             (declared in module `{}`)",
            self.opaque, self.using_module, self.owner_module,
        )
    }
}

pub(crate) fn check_brand_mint_visibility(brand_tag: &str, using_module: &str) -> Result<(), OpaqueVisibilityError> {
    let Some(owner) = opaque_owner_module(brand_tag) else {
        return Ok(());
    };
    if owner == using_module {
        Ok(())
    } else {
        Err(OpaqueVisibilityError {
            opaque: brand_tag.to_string(),
            owner_module: owner.to_string(),
            using_module: using_module.to_string(),
        })
    }
}

pub trait VisibilityTypes: Types {
    /// Check whether `a` (treated as an opaque-nominal type) is
    /// visible from `using_module`. If `a` is not a pure opaque, or is
    /// a built-in opaque with no owner module, the check trivially
    /// succeeds.
    fn check_opaque_visibility(&self, a: &Self::Ty, using_module: &str) -> Result<(), OpaqueVisibilityError>;
}

#[cfg(test)]
#[path = "visibility_test.rs"]
mod visibility_test;
