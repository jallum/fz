use crate::ast::{Attribute, FnClause, SpecDecl, TypeExprBody};
use crate::source::Span;

#[derive(Debug, Clone)]
pub enum NativeDeclaration {
    Extern(String),
    Intrinsic(String),
}

pub(crate) trait CallableSurface {
    fn name(&self) -> &str;
    fn clauses(&self) -> &[FnClause];
    fn declaration(&self) -> Option<&NativeDeclaration>;
    fn native_param_tokens(&self) -> &[TypeExprBody];
    fn native_ret_tokens(&self) -> &TypeExprBody;
    fn native_constraints(&self) -> &[(String, TypeExprBody)];

    fn arity(&self) -> usize {
        if self.declaration().is_some() {
            self.native_param_tokens().len()
        } else {
            self.clauses()
                .first()
                .map(|clause| clause.params.len())
                .expect("functions should have at least one clause")
        }
    }

    fn native_contract_decl(&self) -> Option<SpecDecl> {
        self.declaration()?;
        Some(SpecDecl {
            name: self.name().to_string(),
            param_body_tokens: self.native_param_tokens().to_vec(),
            result_body_tokens: self.native_ret_tokens().clone(),
            constraints: self.native_constraints().to_vec(),
        })
    }
}

#[derive(Debug, Clone)]
pub struct FunctionSurface {
    pub name: String,
    pub name_span: Span,
    pub clauses: Vec<FnClause>,
    pub is_macro: bool,
    pub declaration: Option<NativeDeclaration>,
    pub native_param_tokens: Vec<TypeExprBody>,
    pub native_ret_tokens: TypeExprBody,
    pub native_constraints: Vec<(String, TypeExprBody)>,
    pub variadic: bool,
    pub attrs: Vec<Attribute>,
    pub span: Span,
}

impl FunctionSurface {
    pub(crate) fn arity(&self) -> usize {
        CallableSurface::arity(self)
    }

    pub(crate) fn native_contract_decl(&self) -> Option<SpecDecl> {
        CallableSurface::native_contract_decl(self)
    }
}

impl CallableSurface for FunctionSurface {
    fn name(&self) -> &str {
        &self.name
    }

    fn clauses(&self) -> &[FnClause] {
        &self.clauses
    }

    fn declaration(&self) -> Option<&NativeDeclaration> {
        self.declaration.as_ref()
    }

    fn native_param_tokens(&self) -> &[TypeExprBody] {
        &self.native_param_tokens
    }

    fn native_ret_tokens(&self) -> &TypeExprBody {
        &self.native_ret_tokens
    }

    fn native_constraints(&self) -> &[(String, TypeExprBody)] {
        &self.native_constraints
    }
}
