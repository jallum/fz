use crate::ast::{Attribute, FnClause, SpecDecl, TypeExprBody};
use crate::source::Span;

pub(crate) trait CallableSurface {
    fn name(&self) -> &str;
    fn clauses(&self) -> &[FnClause];
    fn extern_abi(&self) -> Option<&str>;
    fn extern_param_tokens(&self) -> &[TypeExprBody];
    fn extern_ret_tokens(&self) -> &TypeExprBody;
    fn extern_constraints(&self) -> &[(String, TypeExprBody)];

    fn arity(&self) -> usize {
        if self.extern_abi().is_some() {
            self.extern_param_tokens().len()
        } else {
            self.clauses()
                .first()
                .map(|clause| clause.params.len())
                .expect("functions should have at least one clause")
        }
    }

    fn extern_contract_decl(&self) -> Option<SpecDecl> {
        self.extern_abi()?;
        Some(SpecDecl {
            name: self.name().to_string(),
            param_body_tokens: self.extern_param_tokens().to_vec(),
            result_body_tokens: self.extern_ret_tokens().clone(),
            constraints: self.extern_constraints().to_vec(),
        })
    }
}

#[derive(Debug, Clone)]
pub struct FunctionSurface {
    pub name: String,
    pub name_span: Span,
    pub clauses: Vec<FnClause>,
    pub is_macro: bool,
    pub extern_abi: Option<String>,
    pub extern_param_tokens: Vec<TypeExprBody>,
    pub extern_ret_tokens: TypeExprBody,
    pub extern_constraints: Vec<(String, TypeExprBody)>,
    pub variadic: bool,
    /// What the extern's `raises:` tail declares, when its result can fail.
    pub extern_raises: Option<ExternRaises>,
    /// The kind an extern's `delivers:` tail declares, when calling it hands
    /// its first argument to the nearest handler.
    pub extern_delivers: Option<fz_runtime::failure::RaiseKind>,
    /// What the extern's `projects:` tail declares: the value its result
    /// holds is a property of its argument, so a comparison of the result with
    /// a literal is a question about the argument's type.
    pub extern_projection: Option<ExternProjection>,
    pub attrs: Vec<Attribute>,
    pub span: Span,
}

/// A property of its argument that an extern's integer result reports. The
/// result being `n` holds exactly when the argument has the type the property
/// names at `n`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExternProjection {
    /// The number of parameters of a function: `n` holds exactly when the
    /// argument is a function that takes `n` arguments.
    ArrowArity,
}

impl ExternProjection {
    pub const ALL: [Self; 1] = [Self::ArrowArity];

    /// The atom a `projects:` tail names it by.
    pub const fn name(self) -> &'static str {
        match self {
            Self::ArrowArity => "arrow_arity",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|projection| projection.name() == name)
    }
}

/// The failure an extern declares: the exception a body raises, as written
/// (an alias, resolved in the extern's own module), and the message it carries.
#[derive(Debug, Clone)]
pub struct ExternRaises {
    pub exception: crate::modules::identity::ModuleName,
    /// Where the declaration writes the exception's name.
    pub span: Span,
    pub message: String,
}

impl FunctionSurface {
    pub(crate) fn arity(&self) -> usize {
        CallableSurface::arity(self)
    }

    pub(crate) fn extern_contract_decl(&self) -> Option<SpecDecl> {
        CallableSurface::extern_contract_decl(self)
    }
}

impl CallableSurface for FunctionSurface {
    fn name(&self) -> &str {
        &self.name
    }

    fn clauses(&self) -> &[FnClause] {
        &self.clauses
    }

    fn extern_abi(&self) -> Option<&str> {
        self.extern_abi.as_deref()
    }

    fn extern_param_tokens(&self) -> &[TypeExprBody] {
        &self.extern_param_tokens
    }

    fn extern_ret_tokens(&self) -> &TypeExprBody {
        &self.extern_ret_tokens
    }

    fn extern_constraints(&self) -> &[(String, TypeExprBody)] {
        &self.extern_constraints
    }
}
