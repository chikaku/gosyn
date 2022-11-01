//! Define all golang syntax node

use crate::token::Keyword;
use crate::token::LitKind;
use crate::token::Operator;
use crate::Pos;
use std::collections::HashMap;
use std::path::PathBuf;
use std::rc::Rc;

pub struct Comment {
    pub pos: Pos,
    pub text: String,
}

#[derive(Default)]
pub struct Ident {
    pub pos: usize,
    pub name: String,
}

// ================ Type Definition ================

pub struct PointerType {
    pub pos: usize,
    pub typ: Box<Expression>,
}

pub struct ArrayType {
    pub pos: (usize, usize),
    pub len: Box<Expression>,
    pub typ: Box<Expression>,
}

pub struct SliceType {
    pub pos: (usize, usize),
    pub typ: Box<Expression>,
}

pub struct MapType {
    pub pos: (usize, usize),
    pub key: Box<Expression>,
    pub val: Box<Expression>,
}

pub struct Field {
    pub name: Vec<Ident>,
    pub typ: Expression,
    pub tag: Option<StringLit>,
}

#[derive(Default)]
pub struct FieldList {
    pub pos: Option<(usize, usize)>,
    pub list: Vec<Field>,
}

pub struct StructType {
    pub pos: (usize, usize),
    pub fields: Vec<Field>,
}

#[derive(Default)]
pub struct FuncType {
    pub pos: usize,
    pub typ_params: FieldList,
    pub params: FieldList,
    pub result: FieldList,
}

#[derive(PartialEq, Eq)]
pub enum ChanMode {
    Send,
    Recv,
}

pub struct ChannelType {
    pub pos: (usize, usize), // chan, <-
    pub dir: Option<ChanMode>,
    pub typ: Box<Expression>,
}

pub struct InterfaceType {
    pub pos: usize,
    pub methods: FieldList,
}

// ================ Expression Definition ================

pub struct BasicLit {
    pub pos: usize,
    pub kind: LitKind,
    pub value: String,
}

#[derive(Default)]
pub struct StringLit {
    pub pos: usize,
    pub value: String,
}

pub struct FuncLit {
    pub typ: FuncType,
    pub body: BlockStmt,
}

pub enum Element {
    Expr(Expression),
    LitValue(LiteralValue),
}

pub struct KeyedElement {
    pub key: Option<Element>,
    pub val: Element,
}

pub struct LiteralValue {
    pub pos: (usize, usize),
    pub values: Vec<KeyedElement>,
}

pub struct CompositeLit {
    pub typ: Box<Expression>,
    pub val: LiteralValue,
}

pub struct Selector {
    pub pos: usize,
    pub x: Box<Expression>,
    pub sel: Ident,
}

pub struct TypeAssertion {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub right: Option<Box<Expression>>, // None for x.(type)
}

pub struct Index {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub index: Box<Expression>,
}

pub struct IndexList {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub indices: Vec<Expression>,
}

pub struct Slice {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub index: [Option<Box<Expression>>; 3],
}

pub struct Call {
    pub pos: (usize, usize), // third pos > 0 means the ellipsis argument
    pub args: Vec<Expression>,
    pub func: Box<Expression>,
    pub dots: Option<usize>,
}

pub struct ParenExpression {
    pub pos: (usize, usize),
    pub expr: Box<Expression>,
}

pub struct StarExpression {
    pub pos: usize,
    pub right: Box<Expression>,
}

pub struct Ellipsis {
    pub pos: usize,
    pub elt: Option<Box<Expression>>,
}

pub struct RangeExpr {
    pub pos: usize, // pos of 'range'
    pub right: Box<Expression>,
}

pub struct Operation {
    pub pos: usize,
    pub op: Operator,
    pub x: Box<Expression>,
    pub y: Option<Box<Expression>>,
}

pub enum Expression {
    Call(Call),
    Index(Index),
    IndexList(IndexList),
    Slice(Slice),
    Ident(Ident),
    FuncLit(FuncLit),
    Ellipsis(Ellipsis),
    Selector(Selector),
    BasicLit(BasicLit),
    Range(RangeExpr),
    Star(StarExpression),
    Paren(ParenExpression),
    TypeAssert(TypeAssertion),
    CompositeLit(CompositeLit),
    List(Vec<Expression>),
    Operation(Operation),
    TypeMap(MapType),             // map[K]V
    TypeArray(ArrayType),         // [N]T
    TypeSlice(SliceType),         // []T
    TypeFunction(FuncType),       // func (...) ...
    TypeStruct(StructType),       // struct { ... }
    TypeChannel(ChannelType),     // <-chan T | chan<- T | chan T
    TypePointer(PointerType),     // *T
    TypeInterface(InterfaceType), // interface { ... }
}

// ================ Declaration Definition ================

pub struct Decl<T> {
    pub docs: Vec<Rc<Comment>>,
    pub pos0: usize,                  // pos of var | const | type
    pub pos1: Option<(usize, usize)>, // pos of '(' and ')'
    pub specs: Vec<T>,
}

#[derive(Default)]
pub struct VarSpec {
    pub docs: Vec<Rc<Comment>>,
    pub name: Vec<Ident>,
    pub typ: Option<Expression>,
    pub values: Vec<Expression>,
}

#[derive(Default)]
pub struct ConstSpec {
    pub docs: Vec<Rc<Comment>>,
    pub name: Vec<Ident>,
    pub typ: Option<Expression>,
    pub values: Vec<Expression>,
}

pub struct TypeSpec {
    pub docs: Vec<Rc<Comment>>,
    pub alias: bool,
    pub name: Ident,
    pub params: FieldList,
    pub typ: Expression,
}

pub struct FuncDecl {
    pub docs: Vec<Rc<Comment>>,
    pub recv: Option<FieldList>,
    pub name: Ident,
    pub typ: FuncType,
    pub body: Option<BlockStmt>,
}

pub enum Declaration {
    Function(FuncDecl),
    Type(Decl<TypeSpec>),
    Const(Decl<ConstSpec>),
    Variable(Decl<VarSpec>),
}

// ================ Statement Definition ================

pub struct BlockStmt {
    pub pos: (usize, usize),
    pub list: Vec<Statement>,
}

pub enum DeclStmt {
    Type(Decl<TypeSpec>),
    Const(Decl<ConstSpec>),
    Variable(Decl<VarSpec>),
}

pub struct GoStmt {
    pub pos: usize,
    pub call: Call,
}

pub struct DeferStmt {
    pub pos: usize,
    pub call: Call,
}

pub struct ReturnStmt {
    pub pos: usize,
    pub ret: Vec<Expression>,
}

pub struct BranchStmt {
    pub pos: usize,
    pub key: Keyword,
    pub ident: Option<Ident>,
}

pub struct IfStmt {
    pub pos: usize,
    pub init: Option<Box<Statement>>,
    pub cond: Expression,
    pub body: BlockStmt,
    pub else_: Option<Box<Statement>>,
}

pub struct AssignStmt {
    // position of assign operator like = | += | &=
    pub pos: usize,
    pub op: Operator,
    pub left: Vec<Expression>,
    pub right: Vec<Expression>,
}

pub struct LabeledStmt {
    pub pos: usize,
    pub name: Ident,
    pub stmt: Box<Statement>,
}

pub struct SendStmt {
    pub pos: usize,
    pub chan: Expression,
    pub value: Expression,
}

pub struct ExprStmt {
    pub expr: Expression,
}

pub struct CaseClause {
    pub tok: Keyword,
    pub pos: (usize, usize),
    pub list: Vec<Expression>,
    pub body: Vec<Box<Statement>>,
}

pub struct CaseBlock {
    pub pos: (usize, usize),
    pub body: Vec<CaseClause>,
}

pub struct SwitchStmt {
    pub pos: usize,
    pub init: Option<Box<Statement>>,
    pub tag: Option<Expression>,
    pub block: CaseBlock,
}

pub struct TypeSwitchStmt {
    pub pos: usize,
    pub init: Option<Box<Statement>>,
    pub tag: Option<Box<Statement>>,
    pub block: CaseBlock,
}

pub struct IncDecStmt {
    pub pos: usize,
    pub op: Operator,
    pub expr: Expression,
}

pub struct CommClause {
    pub pos: (usize, usize), // pos of (keyword, colon)
    pub tok: Keyword,
    pub comm: Option<Box<Statement>>,
    pub body: Vec<Box<Statement>>,
}

pub struct CommBlock {
    pub pos: (usize, usize),
    pub body: Vec<CommClause>,
}

pub struct SelectStmt {
    pub pos: usize,
    pub body: CommBlock,
}

pub struct RangeStmt {
    pub pos: (usize, usize), // pos of (for, range)
    pub key: Option<Expression>,
    pub value: Option<Expression>,
    pub op: Option<(usize, Operator)>, // define or assign
    pub expr: Expression,
    pub body: BlockStmt,
}

pub struct ForStmt {
    pub pos: usize,
    pub init: Option<Box<Statement>>,
    pub cond: Option<Box<Statement>>,
    pub post: Option<Box<Statement>>,
    pub body: BlockStmt,
}

pub struct EmptyStmt {
    pub pos: usize,
}

#[allow(clippy::large_enum_variant)]
pub enum Statement {
    Go(GoStmt),
    If(IfStmt),
    For(ForStmt),
    Send(SendStmt),
    Expr(ExprStmt),
    Defer(DeferStmt),
    Block(BlockStmt),
    Range(RangeStmt),
    Empty(EmptyStmt),
    Label(LabeledStmt),
    IncDec(IncDecStmt),
    Assign(AssignStmt),
    Return(ReturnStmt),
    Branch(BranchStmt),
    Switch(SwitchStmt),
    Select(SelectStmt),
    TypeSwitch(TypeSwitchStmt),
    Declaration(DeclStmt),
}

#[derive(Default)]
pub struct Import {
    pub name: Option<Ident>,
    pub path: StringLit,
}

#[derive(Default)]
pub struct File {
    pub path: PathBuf,
    pub line_info: Vec<usize>,
    pub docs: Vec<Rc<Comment>>,
    pub pkg_name: Ident,
    pub imports: Vec<Import>,
    pub decl: Vec<Declaration>,
    pub comments: Vec<Rc<Comment>>,
}

pub struct Package {
    pub path: PathBuf,
    pub files: HashMap<PathBuf, File>,
}

// ================ Type Implemention ================

impl From<Ident> for Field {
    fn from(id: Ident) -> Self {
        Self {
            name: vec![],
            typ: Expression::Ident(id),
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

impl From<Expression> for Field {
    fn from(expr: Expression) -> Self {
        Self {
            name: vec![],
            typ: expr,
            tag: None,
        }
    }
}

impl AssignStmt {
    pub fn is_range(&self) -> bool {
        matches!(self.right.first(), Some(Expression::Range(_)))
    }
}

impl FieldList {
    pub fn pos(&self) -> usize {
        if let Some((pos, _)) = self.pos {
            return pos;
        }

        if let Some(field) = self.list.first() {
            if let Some(name) = field.name.first() {
                return name.pos;
            }

            return field.typ.pos();
        }

        panic!("call pos on empty FieldList");
    }
}

impl Expression {
    pub fn pos(&self) -> usize {
        match self {
            Expression::Call(x) => x.pos.0,
            Expression::Index(x) => x.pos.0,
            Expression::Slice(x) => x.pos.0,
            Expression::Ident(x) => x.pos,
            Expression::FuncLit(x) => x.typ.pos,
            Expression::Ellipsis(x) => x.pos,
            Expression::Selector(x) => x.x.pos(),
            Expression::BasicLit(x) => x.pos,
            Expression::Range(x) => x.pos,
            Expression::Star(x) => x.pos,
            Expression::Paren(x) => x.pos.0,
            Expression::TypeAssert(x) => x.left.pos(),
            Expression::CompositeLit(x) => x.typ.pos(),
            Expression::IndexList(x) => x.left.pos(),
            Expression::List(_) => unimplemented!("list may empty"),
            Expression::Operation(x) => x.x.pos(),
            Expression::TypeMap(x) => x.pos.0,
            Expression::TypeArray(x) => x.pos.0,
            Expression::TypeSlice(x) => x.pos.0,
            Expression::TypeFunction(f) => f.pos,
            Expression::TypeStruct(x) => x.pos.0,
            Expression::TypeChannel(x) => x.pos.0,
            Expression::TypePointer(x) => x.pos,
            Expression::TypeInterface(x) => x.pos,
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
