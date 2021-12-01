use crate::LitKind;
use crate::Operator;
use crate::Pos;
use std::path::PathBuf;
use std::rc::Rc;

use shika_proc_macro::EnumFrom;

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

// ================ Type Definition ================

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
pub struct PointerType {
    pub pos: usize,
    pub typ: Box<Type>,
}

pub struct EllipsisArrayType {
    pub pos: (usize, usize),
    pub typ: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct ArrayType {
    pub pos: (usize, usize),
    pub len: Box<Expression>,
    pub typ: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct SliceType {
    pub pos: usize,
    pub typ: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct MapType {
    pub pos: (usize, usize),
    pub key: Box<Type>,
    pub val: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct Field {
    pub name: Vec<Ident>,
    pub typ: Type,
    pub tag: Option<StringLit>,
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub pos: (usize, usize),
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone)]
pub struct Params {
    pub name: Vec<Ident>,
    pub typ: (Box<Type>, bool),
}

impl From<Ident> for Params {
    fn from(id: Ident) -> Self {
        Params {
            name: Vec::new(),
            typ: (Box::new(id.into()), false),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub pos: usize,
    pub input: Vec<Params>,
    pub output: Vec<Params>,
}

#[derive(Debug, Clone)]
pub enum ChanMode {
    Send,
    Recv,
}

#[derive(Debug, Clone)]
pub struct ChannelType {
    pub pos: usize,
    pub dir: Option<ChanMode>,
    pub typ: Box<Type>,
}

#[derive(Debug, Clone)]
pub enum InterfaceElem {
    Embed(TypeName),
    Method {
        name: Ident,
        input: Vec<Params>,
        output: Vec<Params>,
    },
}

#[derive(Debug, Clone)]
pub struct InterfaceType {
    pub pos: (usize, usize),
    pub methods: Vec<InterfaceElem>,
}

#[derive(Clone, Debug, EnumFrom)]
pub enum Type {
    // pkg.Type
    #[enum_from(inner)]
    Ident(TypeName),

    // map[K]V
    #[enum_from(inner)]
    Map(MapType),

    // [N]T
    #[enum_from(inner)]
    Array(ArrayType),

    // []T
    #[enum_from(inner)]
    Slice(SliceType),

    // <-chan T | chan<- T | chan T
    #[enum_from(inner)]
    Channel(ChannelType),

    // *T
    #[enum_from(inner)]
    Pointer(PointerType),

    // struct { ... }
    #[enum_from(inner)]
    Struct(StructType),

    // func (...) ...
    #[enum_from(inner)]
    Function(FunctionType),

    // interface { ... }
    #[enum_from(inner)]
    Interface(InterfaceType),
}

impl From<Ident> for Type {
    fn from(id: Ident) -> Self {
        Self::Ident(id.into())
    }
}

// ================ Operand Definition ================

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
pub struct FunctionLit {
    pub input: Vec<Params>,
    pub output: Vec<Params>,
    // body: Option<Statement>,
}

enum Key {
    FieldName(Ident),
    Expr(Expression),
    LitValue(LiteralValue),
}

enum Element {
    Expr(Expression),
    LitValue(LiteralValue),
}

struct KeyedElement {
    pos: Option<usize>,
    key: Option<Key>,
    elem: Element,
}

struct LiteralValue {
    pos: (usize, usize),
    values: Vec<KeyedElement>,
}

#[derive(EnumFrom)]
enum LiteralType {
    #[enum_from(inner)]
    Map(MapType),

    #[enum_from(inner)]
    Slice(SliceType),

    #[enum_from(inner)]
    Ident(TypeName),

    #[enum_from(inner)]
    Struct(StructType),

    #[enum_from(inner)]
    Array(ArrayType),

    #[enum_from(inner)]
    EllipsisArray(EllipsisArrayType),
}

struct CompositeLit {
    typ: LiteralType,
    val: LiteralValue,
}

enum Operand {
    Ident(TypeName),
    Expr(Expression),
    BasicLit(BasicLit),
    FunctionLit(FunctionLit),
    CompositeLit(CompositeLit),
}

// ================ Expression Definition ================

#[derive(Debug, Clone, EnumFrom)]
pub enum Expression {
    Invalid,
    #[enum_from(inner)]
    Ident(Ident),
    #[enum_from(inner)]
    BasicLit(BasicLit),
    Type {
        pos: usize,
        typ: Box<Type>,
    },
    FuncLit {
        pos: usize,
        func: FunctionLit,
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
