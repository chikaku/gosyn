use crate::ast;
use crate::ast::*;
use crate::token::LitKind;
use std::rc::Rc;

impl From<Ident> for TypeName {
    fn from(id: Ident) -> Self {
        Self { pkg: None, name: id }
    }
}

impl From<Ident> for Type {
    fn from(id: Ident) -> Self {
        Self::Ident(id.into())
    }
}

impl From<Ident> for Field {
    fn from(id: Ident) -> Self {
        Self {
            name: vec![],
            typ: Expression::Type(id.into()),
            tag: None,
        }
    }
}

impl From<TypeName> for Field {
    fn from(id: TypeName) -> Self {
        Self {
            name: vec![],
            typ: ast::Expression::Ident(id),
            tag: None,
        }
    }
}

impl From<Type> for Field {
    fn from(typ: Type) -> Self {
        Self {
            name: vec![],
            typ: Expression::Type(typ),
            tag: None,
        }
    }
}

impl From<BasicLit> for StringLit {
    fn from(lit: BasicLit) -> StringLit {
        assert_eq!(lit.kind, LitKind::String);
        StringLit { pos: lit.pos, value: lit.value }
    }
}

impl From<Ellipsis> for Field {
    fn from(ell: Ellipsis) -> Self {
        Self {
            name: vec![],
            typ: Expression::Ellipsis(ell),
            tag: None,
        }
    }
}

impl AssignStmt {
    pub fn is_range(&self) -> bool {
        matches!(self.right.first(), Some(Expression::Range(_)))
    }
}

impl TypeName {
    fn pos(&self) -> usize {
        self.pkg.as_ref().map(|p| p.pos).unwrap_or(self.name.pos)
    }
}

impl FieldList {
    pub fn pos(&self) -> usize {
        match self.pos {
            Some((pos, _)) => pos,
            None => unreachable!("shouldn't call pos on empty field list"),
        }
    }
}

impl Type {
    fn pos(&self) -> usize {
        match self {
            Type::Map(x) => x.pos.0,
            Type::Ident(x) => x.pos(),
            Type::Array(x) => x.pos.0,
            Type::Slice(x) => x.pos.0,
            Type::Function(x) => x.pos,
            Type::Struct(x) => x.pos.0,
            Type::Channel(x) => x.pos.0,
            Type::Pointer(x) => x.pos,
            Type::Interface(x) => x.pos,
        }
    }
}

impl Expression {
    pub fn pos(&self) -> usize {
        match self {
            Expression::Type(x) => x.pos(),
            Expression::Call(x) => x.pos.0,
            Expression::Index(x) => x.pos.0,
            Expression::Slice(x) => x.pos.0,
            Expression::Ident(x) => x.pos(),
            Expression::FuncLit(x) => x.typ.pos,
            Expression::Ellipsis(x) => x.pos,
            Expression::Selector(x) => x.left.pos(),
            Expression::BasicLit(x) => x.pos,
            Expression::Range(x) => x.pos,
            Expression::Star(x) => x.pos,
            Expression::Paren(x) => x.pos.0,
            Expression::Unary(x) => x.pos,
            Expression::Binary(x) => x.left.pos(),
            Expression::TypeAssert(x) => x.left.pos(),
            Expression::CompositeLit(x) => x.typ.pos(),
        }
    }
}

pub(crate) trait Spec {
    fn with_docs(self, docs: Vec<Rc<Comment>>) -> Self;
}

impl Spec for VarSpec {
    fn with_docs(mut self, docs: Vec<Rc<Comment>>) -> VarSpec {
        self.docs = docs;
        self
    }
}

impl Spec for TypeSpec {
    fn with_docs(mut self, docs: Vec<Rc<Comment>>) -> TypeSpec {
        self.docs = docs;
        self
    }
}

impl Spec for ConstSpec {
    fn with_docs(mut self, docs: Vec<Rc<Comment>>) -> ConstSpec {
        self.docs = docs;
        self
    }
}
