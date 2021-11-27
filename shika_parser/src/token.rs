use shika_proc_macro::EnumFrom;
use std::fmt::{write, Debug, Display, Formatter};

#[derive(Copy, Clone, Eq, PartialEq, EnumFrom, Debug)]
pub enum Operator {
    #[enum_from(str = "+")]
    Add,
    #[enum_from(str = "-")]
    Sub,
    #[enum_from(str = "*")]
    Mul,
    #[enum_from(str = "/")]
    Quo,
    #[enum_from(str = "%")]
    Rem,

    #[enum_from(str = "&")]
    And,
    #[enum_from(str = "|")]
    Or,
    #[enum_from(str = "^")]
    Xor,
    #[enum_from(str = "<<")]
    Shl,
    #[enum_from(str = ">>")]
    Shr,
    #[enum_from(str = "&^")]
    AndNot,

    #[enum_from(str = "+=")]
    AddAssign,
    #[enum_from(str = "-=")]
    SubAssign,
    #[enum_from(str = "*=")]
    MulAssign,
    #[enum_from(str = "/=")]
    QuoAssign,
    #[enum_from(str = "%=")]
    RemAssign,

    #[enum_from(str = "&=")]
    AndAssign,
    #[enum_from(str = "|=")]
    OrAssign,
    #[enum_from(str = "^=")]
    XorAssign,
    #[enum_from(str = "<<=")]
    ShlAssign,
    #[enum_from(str = ">>=")]
    ShrAssign,
    #[enum_from(str = "&^=")]
    AndNotAssign,

    #[enum_from(str = "&&")]
    AndAnd,
    #[enum_from(str = "||")]
    OrOr,
    #[enum_from(str = "<-")]
    Arrow,
    #[enum_from(str = "++")]
    Inc,
    #[enum_from(str = "--")]
    Dec,

    #[enum_from(str = "==")]
    Equal,
    #[enum_from(str = "<")]
    Less,
    #[enum_from(str = ">")]
    Greater,
    #[enum_from(str = "=")]
    Assign,
    #[enum_from(str = "!")]
    Not,

    #[enum_from(str = ":=")]
    Define,
    #[enum_from(str = "!=")]
    NotEqual,
    #[enum_from(str = "<=")]
    LessEqual,
    #[enum_from(str = ">=")]
    GreaterEqual,
    #[enum_from(str = "...")]
    Ellipsis,

    #[enum_from(str = "(")]
    ParenLeft,
    #[enum_from(str = ")")]
    ParenRight,
    #[enum_from(str = "[")]
    BarackLeft,
    #[enum_from(str = "]")]
    BarackRight,
    #[enum_from(str = "{")]
    BraceLeft,
    #[enum_from(str = "}")]
    BraceRight,

    #[enum_from(str = ",")]
    Comma,
    #[enum_from(str = ":")]
    Colon,
    #[enum_from(str = ".")]
    Period,
    #[enum_from(str = ";")]
    SemiColon,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug, EnumFrom)]
pub enum Keyword {
    #[enum_from(str = "break")]
    Break,
    #[enum_from(str = "case")]
    Case,
    #[enum_from(str = "chan")]
    Chan,
    #[enum_from(str = "const")]
    Const,
    #[enum_from(str = "continue")]
    Continue,

    #[enum_from(str = "default")]
    Default,
    #[enum_from(str = "defer")]
    Defer,
    #[enum_from(str = "else")]
    Else,
    #[enum_from(str = "fallthrough")]
    FallThrough,
    #[enum_from(str = "for")]
    For,

    #[enum_from(str = "func")]
    Func,
    #[enum_from(str = "go")]
    Go,
    #[enum_from(str = "goto")]
    Goto,
    #[enum_from(str = "if")]
    If,
    #[enum_from(str = "import")]
    Import,

    #[enum_from(str = "interface")]
    Interface,
    #[enum_from(str = "map")]
    Map,
    #[enum_from(str = "package")]
    Package,
    #[enum_from(str = "range")]
    Range,
    #[enum_from(str = "return")]
    Return,

    #[enum_from(str = "select")]
    Select,
    #[enum_from(str = "struct")]
    Struct,
    #[enum_from(str = "switch")]
    Switch,
    #[enum_from(str = "type")]
    Type,
    #[enum_from(str = "var")]
    Var,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum LitKind {
    Ident,
    String,
    Integer,
    Float,
    Imag,
    Char,
}

#[derive(Eq, PartialEq, Clone, EnumFrom)]
pub enum Token {
    Comment(String),
    #[enum_from(inner)]
    Keyword(Keyword),
    #[enum_from(inner)]
    Operator(Operator),
    Literal(LitKind, String),
}

impl Debug for Token {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Comment(_) => write!(f, "/* comment */"),
            Token::Literal(_, lit) => write!(f, "'{}'", lit),
            Token::Operator(op) => write!(f, "'{}'", op.to_str()),
            Token::Keyword(word) => write!(f, "'{}'", word.to_str()),
        }
    }
}

impl Token {
    pub fn len(&self) -> usize {
        match self {
            Token::Operator(op) => op.to_str().len(),
            Token::Keyword(word) => word.to_str().len(),
            Token::Comment(text) => text.chars().count(),
            Token::Literal(_, value) => value.chars().count(),
        }
    }

    pub fn kind(&self) -> TokenKind {
        match self {
            Token::Comment(_) => TokenKind::Comment,
            Token::Operator(op) => TokenKind::Operator(op.clone()),
            Token::Keyword(word) => TokenKind::Keyword(word.clone()),
            Token::Literal(kind, _) => TokenKind::Literal(kind.clone()),
        }
    }

    pub fn is<K: Into<TokenKind>>(&self, exp: K) -> bool {
        self.kind() == exp.into()
    }
}

pub trait IntoKind = Into<TokenKind> + Copy;

#[derive(Eq, PartialEq, EnumFrom, Copy, Clone)]
pub enum TokenKind {
    Comment,
    #[enum_from(inner)]
    Keyword(Keyword),
    #[enum_from(inner)]
    Literal(LitKind),
    #[enum_from(inner)]
    Operator(Operator),
}

impl Debug for TokenKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Comment => unreachable!(),
            Self::Keyword(word) => write!(f, "'{}'", word.to_str()),
            Self::Operator(op) => write!(f, "'{}'", op.to_str()),
            Self::Literal(kind) => match kind {
                LitKind::Ident => write!(f, "Identifier"),
                LitKind::String => write!(f, "String Literals"),
                LitKind::Integer => write!(f, "Integer Literals"),
                LitKind::Imag => write!(f, "Imaginary Literals"),
                LitKind::Char => write!(f, "Character Literals"),
                LitKind::Float => write!(f, "Float Literals"),
            },
        }
    }
}
