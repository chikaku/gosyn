use crate::Keyword;
use crate::LitKind;
use crate::Operator;
use crate::Pos;
use std::path::PathBuf;
use std::rc::Rc;

use shika_proc_macro::EnumFromWrapped;
use shika_proc_macro::EnumIntoWrapped;

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

pub struct TypeName {
    pub pkg: Option<Ident>,
    pub name: Ident,
}

pub struct PointerType {
    pub pos: usize,
    pub typ: Box<Type>,
}

pub struct ArrayType {
    pub pos: (usize, usize),
    pub len: Box<Expression>,
    pub typ: Box<Type>,
}

pub struct SliceType {
    pub pos: (usize, usize),
    pub typ: Box<Type>,
}

pub struct MapType {
    pub pos: (usize, usize),
    pub key: Box<Type>,
    pub val: Box<Type>,
}

pub struct Field {
    pub name: Vec<Ident>,
    pub typ: Expression,
    pub tag: Option<StringLit>,
    // TODO: doc and line comment
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
    pub params: FieldList,
    pub result: FieldList,
}

#[derive(PartialEq)]
pub enum ChanMode {
    Send,
    Recv,
}

pub struct ChannelType {
    pub pos: (usize, usize), // chan, <-
    pub dir: Option<ChanMode>,
    pub typ: Box<Type>,
}

pub struct InterfaceType {
    pub pos: usize,
    pub methods: FieldList,
}

#[derive(EnumFromWrapped, EnumIntoWrapped)]
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
    pub body: Option<BlockStmt>,
}

#[derive(EnumFromWrapped)]
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
    pub right: Ident,
    pub left: Box<Expression>,
}

pub struct TypeAssertion {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub right: Option<Type>, // None for x.(type)
}

pub struct Index {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub index: Box<Expression>,
}

pub struct Slice {
    pub pos: (usize, usize),
    pub left: Box<Expression>,
    pub index: [Option<Box<Expression>>; 3],
}

pub struct Call {
    pub pos: (usize, usize), // third pos > 0 means the ellipsis argument
    pub args: Vec<Expression>,
    pub left: Box<Expression>,
    pub ellipsis: Option<usize>,
}

pub struct UnaryExpression {
    pub pos: usize,
    pub op: Operator,
    pub right: Box<Expression>,
}

pub struct BinaryExpression {
    pub pos: usize, // pos of operator
    pub op: Operator,
    pub left: Box<Expression>,
    pub right: Box<Expression>,
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
    pub elt: Option<Type>,
}

pub struct RangeExpr {
    pub pos: usize, // pos of 'range'
    pub right: Box<Expression>,
}

#[derive(EnumFromWrapped, EnumIntoWrapped)]
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
    Range(RangeExpr),
    Star(StarExpression),
    Paren(ParenExpression),
    Unary(UnaryExpression),
    Binary(BinaryExpression),
    TypeAssert(TypeAssertion),
    CompositeLit(CompositeLit),
}

// ================ Declaration Definition ================

pub struct Decl<T> {
    pub pos0: usize,                  // pos of var | const | type
    pub pos1: Option<(usize, usize)>, // pos of '(' and ')'
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
    pub recv: Option<FieldList>,
    pub name: Ident,
    pub typ: FuncType,
    pub body: Option<BlockStmt>,
}

#[derive(EnumFromWrapped)]
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

#[derive(EnumFromWrapped)]
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

#[derive(EnumFromWrapped)]
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
    pub docs: Vec<Rc<Comment>>,
    pub name: Option<Ident>,
    pub path: StringLit,
}

#[derive(Default)]
pub struct File {
    pub path: PathBuf,
    pub line_info: Vec<usize>,

    pub pkg_name: Ident,
    pub document: Vec<Rc<Comment>>,
    pub comments: Vec<Rc<Comment>>,
    pub imports: Vec<Import>,
    pub decl: Vec<Declaration>,
}
