use crate::LitKind;
use crate::Operator;
use crate::Pos;
use std::path::PathBuf;
use std::rc::Rc;

use shika_proc_macro::EnumFrom;
use shika_proc_macro::EnumFromWrapped;
use shika_proc_macro::EnumIntoWrapped;

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
    pub typ: Expression,
    pub tag: Option<StringLit>,
    // TODO: doc and line comment
}

#[derive(Debug, Clone, Default)]
pub struct FieldList {
    pub pos: Option<(usize, usize)>,
    pub list: Vec<Field>,
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub pos: (usize, usize),
    pub fields: Vec<Field>,
}

#[derive(Debug, Clone, Default)]
pub struct FuncType {
    pub pos: usize,
    pub params: FieldList,
    pub result: FieldList,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ChanMode {
    Send,
    Recv,
}

#[derive(Debug, Clone)]
pub struct ChannelType {
    pub pos: (usize, usize), // chan, <-
    pub dir: Option<ChanMode>,
    pub typ: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct InterfaceType {
    pub pos: usize,
    pub methods: FieldList,
}

#[derive(Clone, Debug, EnumFromWrapped, EnumIntoWrapped)]
pub enum Type {
    Map(MapType),             // map[K]V
    Ident(TypeName),          // pkg.Type
    Array(ArrayType),         // [N]T
    Slice(SliceType),         // []T
    Function(FuncType),       // func (...) ...
    Struct(StructType),       // struct { ... }
    Channel(ChannelType),     // <-chan T | chan<- T | chan T
    Pointer(PointerType),     // *T
    Interface(InterfaceType), // interface { ... }
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
            typ: id.into(),
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

// ================ Expression Definition ================

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
    pub typ: FuncType,
    // body: Option<Statement>,
}

#[derive(Debug, Clone, EnumFrom)]
pub enum Element {
    #[enum_from(inner)]
    Expr(Expression),
    #[enum_from(inner)]
    LitValue(LiteralValue),
}

#[derive(Debug, Clone)]
pub struct KeyedElement {
    pub key: Option<Element>,
    pub val: Element,
}

#[derive(Debug, Clone)]
pub struct LiteralValue {
    pub pos: (usize, usize),
    pub values: Vec<KeyedElement>,
}

#[derive(Debug, Clone)]
pub struct CompositeLit {
    pub typ: Box<Expression>,
    pub val: LiteralValue,
}

#[derive(Debug, Clone)]
pub struct Conversion {
    pub pos: (usize, usize),
    pub typ: Box<Type>,
    pub expr: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct Selector {
    pub pos: usize,
    pub right: Ident,
    pub left: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct TypeAssertion {
    pub left: Box<Expression>,
    pub right: Option<Type>,
}

#[derive(Debug, Clone)]
pub struct Index {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub index: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct Slice {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub index: [Option<Box<Expression>>; 3],
}

#[derive(Debug, Clone)]
pub struct Call {
    pub pos: (usize, usize, usize), // third pos > 0 means the ellipsis argument
    pub args: Vec<Expression>,
    pub left: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct UnaryExpression {
    pub pos: usize,
    pub op: Operator,
    pub right: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct BinaryExpression {
    pub pos: usize,
    pub op: Operator,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct ParenExpression {
    pub pos: (usize, usize),
    pub expr: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct StarExpression {
    pub pos: usize,
    pub right: Box<Expression>,
}

#[derive(Debug, Clone)]
pub struct Ellipsis {
    pub pos: usize,
    pub elt: Option<Type>,
}

#[derive(Debug, Clone, EnumFromWrapped, EnumIntoWrapped)]
pub enum Expression {
    Type(Type),
    Call(Call),
    Index(Index),
    Slice(Slice),
    Ident(TypeName),
    FuncLit(FuncLit),
    Ellipsis(Ellipsis),
    Selector(Selector),
    BasicLit(BasicLit),
    Star(StarExpression),
    Paren(ParenExpression),
    Unary(UnaryExpression),
    Binary(BinaryExpression),
    TypeAssert(TypeAssertion),
    CompositeLit(CompositeLit),
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

pub struct Declaration<T> {
    pub pos0: usize,                  // pos of var | type
    pub pos1: Option<(usize, usize)>, // pos if '(' and ')'
    pub specs: Vec<T>,
}

#[derive(Default)]
pub struct VarSpec {
    pub docs: Vec<Rc<Comment>>,
    pub name: Vec<Ident>,
    pub typ: Option<Type>,
    pub values: Vec<Expression>,
}

#[derive(Default)]
pub struct ConstSpec {
    pub docs: Vec<Rc<Comment>>,
    pub name: Vec<Ident>,
    pub typ: Option<Type>,
    pub values: Vec<Expression>,
}

pub struct TypeSpec {
    pub docs: Vec<Rc<Comment>>,
    pub alias: bool,
    pub name: Ident,
    pub typ: Type,
}

pub struct FuncDecl {
    pub name: Ident,
    pub typ: FuncType,
}

pub struct Block {
    pub pos: (usize, usize),
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
