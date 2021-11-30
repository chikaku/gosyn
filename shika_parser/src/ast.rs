use crate::LitKind;
use crate::Operator;
use crate::Pos;
use std::path::PathBuf;
use std::rc::Rc;

#[derive(Default, Debug)]
pub struct Comment {
    pub pos: Pos,
    pub text: String,
}

#[derive(Default, Debug, Clone)]
pub struct Ident {
    pub pos: usize,
    pub name: String,
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

#[derive(Default, Debug)]
pub struct Import {
    pub docs: Vec<Rc<Comment>>,
    pub name: Option<Ident>,
    pub path: StringLit,
}

#[derive(Debug, Clone)]
pub struct BasicLit {
    pub pos: usize,
    pub kind: LitKind,
    pub value: String,
}

#[derive(Default, Debug, Clone)]
pub struct StringLit {
    pub pos: usize,
    pub value: String,
}

impl From<BasicLit> for StringLit {
    fn from(lit: BasicLit) -> StringLit {
        assert_eq!(lit.kind, LitKind::String);
        StringLit {
            pos: lit.pos,
            value: lit.value,
        }
    }
}

#[derive(Debug, Clone)]
pub struct FuncLit {
    pub input: Vec<Params>,
    pub output: Vec<Params>,
    // body: Option<Statement>,
}

#[derive(Debug, Clone)]
pub struct Params {
    pub name: Option<Ident>,
    pub typ: (Box<Type>, bool),
}

impl From<Ident> for Params {
    fn from(id: Ident) -> Self {
        Params {
            name: None,
            typ: (Box::new(id.into()), false),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Function {
    pub name: Option<Ident>,
    pub input: Vec<Params>,
    pub output: Vec<Params>,
    // body: Option<Statement>,
}

#[derive(Debug, Clone)]
pub enum Expression {
    Invalid,
    Ident(Ident),
    BasicLit(BasicLit),

    Type {
        pos: usize,
        typ: Box<Type>,
    },

    FuncLit {
        pos: usize,
        func: FuncLit,
    },

    Paren {
        pos: (usize, usize),
        expr: Box<Expression>,
    },

    Unary {
        pos: usize,
        operator: Operator,
        operand: Box<Expression>,
    },
    Star {
        pos: usize,
        right: Box<Expression>,
    },
    Selector {
        left: Box<Expression>,
        right: Ident,
    },
    TypeAssert {
        left: Box<Expression>,
        assert: Box<Option<Type>>,
    },
}

#[derive(Clone, Debug)]
pub enum Type {
    Ident(TypeName),
    Map(Box<Type>, Box<Type>),    // map[K]V
    Array(Box<Type>, Expression), // [N]T
    Slice(Box<Type>),             // []T
    Channel(ChanMode, Box<Type>), // <- chan T
    Pointer(Box<Type>),           // *T
    Struct {
        pos: (usize, usize),
        fields: Vec<Field>,
    },
    Function {
        pos: usize,
        input: Vec<Params>,
        output: Vec<Params>,
    },
    Interface {
        pos: (usize, usize),
        methods: Vec<InterfaceElem>,
    },
}

impl From<TypeName> for Type {
    fn from(id: TypeName) -> Self {
        Self::Ident(id)
    }
}

impl From<Ident> for Type {
    fn from(id: Ident) -> Self {
        Self::Ident(id.into())
    }
}

#[derive(Debug, Clone)]
pub struct TypeName {
    pub pkg: Option<Ident>,
    pub name: Ident,
}

impl From<Ident> for TypeName {
    fn from(id: Ident) -> Self {
        Self {
            pkg: None,
            name: id,
        }
    }
}

#[derive(Debug, Clone)]
pub enum InterfaceElem {
    Embed(TypeName), // TODO: here is a type name
    Method {
        name: Ident,
        input: Vec<Params>,
        output: Vec<Params>,
    },
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: Vec<Ident>,
    pub typ: Type,
    pub tag: Option<StringLit>,
}

#[derive(Debug, Clone, Copy)]
pub enum ChanMode {
    Double,
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
    Constant,
    Variable,
    Type,
    Func,
    Method,
}
