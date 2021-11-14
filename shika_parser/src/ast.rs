use crate::token::Pos;
use crate::LitKind;
use std::path::PathBuf;
use std::rc::Rc;

#[derive(Default, Debug)]
pub struct Comment {
    pub pos: Pos,
    pub text: String,
}

#[derive(Default, Debug)]
pub struct Ident {
    pub pos: usize,
    pub name: String,
}

pub struct BasicLit {
    pub pos: usize,
    pub kind: LitKind,
    pub value: String,
}

#[derive(Default, Debug)]
pub struct StringLit {
    pub pos: usize,
    pub value: String,
}

impl Into<StringLit> for BasicLit {
    fn into(self) -> StringLit {
        assert_eq!(self.kind, LitKind::String);
        StringLit {
            pos: self.pos,
            value: self.value,
        }
    }
}

#[derive(Default, Debug)]
pub struct Import {
    pub docs: Vec<Rc<Comment>>,
    pub name: Option<Ident>,
    pub path: StringLit,
}

pub enum Expression {}

pub enum Type {
    Identify(Ident),
    Qualified(Ident, Ident),

    Map,
    Array(Box<Type>, Expression),
    Slice(Box<Type>),
    Struct,
    Channel,
    Pointer,
    Function,
    Interface,
}

#[derive(Default)]
pub struct VarSpec {
    pub docs: Vec<Rc<Comment>>,
    pub name: Vec<Ident>,
    pub typ: Option<Type>,
    pub values: Vec<Expression>,
}

pub enum Declaration {
    Var(Vec<VarSpec>),
}

#[derive(Default)]
pub struct File {
    pub path: PathBuf,
    pub line_info: Vec<usize>,

    pub name: Ident,
    pub comments: Vec<Rc<Comment>>,
    pub document: Vec<Rc<Comment>>,
    pub imports: Vec<Import>,
}
