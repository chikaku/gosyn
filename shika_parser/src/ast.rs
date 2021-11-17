use crate::LitKind;
use crate::Pos;
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

#[derive(Default)]
pub struct PkgName(pub Ident);

impl Into<Ident> for PkgName {
    fn into(self) -> Ident {
        self.0
    }
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

#[allow(dead_code)]
pub enum Type {
    Named(Ident),             // T
    PkgNamed(PkgName, Ident), // p.T

    Map(Box<Type>, Box<Type>),    // map[K]V
    Array(Box<Type>, Expression), // [N]T
    Slice(Box<Type>),             // []T
    Channel(ChanMode, Box<Type>), // <- chan T
    Pointer(Box<Type>),           // *T

    Function(),
    Interface(),
    Struct(Vec<(Vec<Ident>, Box<Type>)>),
}

pub enum ChanMode {
    None,
    Send,
    Receive,
}

#[derive(Default)]
pub struct VarSpec {
    pub docs: Vec<Rc<Comment>>,
    pub name: Vec<Ident>,
    pub typ: Option<Type>,
    pub values: Vec<Expression>,
}

#[allow(dead_code)]
pub enum Declaration {
    Var(Vec<VarSpec>),
}

#[derive(Default)]
pub struct File {
    pub path: PathBuf,
    pub line_info: Vec<usize>,

    pub name: PkgName,
    pub comments: Vec<Rc<Comment>>,
    pub document: Vec<Rc<Comment>>,
    pub imports: Vec<Import>,
}
