use crate::ast::{Attribute, FnClause, FnDef, SpecDecl, TypeExprBody};
use crate::compiler::source::Span;

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
    pub attrs: Vec<Attribute>,
    pub span: Span,
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

impl CallableSurface for FnDef {
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
