use shika_proc_macro::EnumFrom;

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum LitKind {
    Ident,
    Integer,
    Float,
    Imag,
    Char,
    String,
}

#[derive(Clone, Eq, PartialEq, Debug, EnumFrom)]
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
    BraceLeft,
    #[enum_from(str = "]")]
    BraceRight,
    #[enum_from(str = "{")]
    BarackLeft,
    #[enum_from(str = "}")]
    BarackRight,

    #[enum_from(str = ",")]
    Comma,
    #[enum_from(str = ":")]
    Colon,
    #[enum_from(str = ".")]
    Period,
    #[enum_from(str = ";")]
    SemiColon,
}

#[derive(Clone, Eq, PartialEq, Debug, EnumFrom)]
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

#[derive(Eq, PartialEq, Debug, Clone)]
pub enum Token {
    Comment(String),
    Keyword(Keyword),
    Operator(Operator),
    Literal(LitKind, String),
}

impl From<Keyword> for Token {
    fn from(word: Keyword) -> Self {
        Self::Keyword(word)
    }
}

impl From<Operator> for Token {
    fn from(op: Operator) -> Self {
        Self::Operator(op)
    }
}

impl Token {
    pub fn length(&self) -> usize {
        match self {
            Token::Comment(text) => text.len(),
            Token::Keyword(word) => word.to_str().len(),
            Token::Operator(op) => op.to_str().len(),
            Token::Literal(_, value) => value.len(),
        }
    }

    pub fn as_expected(&self) -> String {
        match self {
            Token::Comment(_) => unreachable!(),
            Token::Keyword(word) => format!("'{}'", word.to_str()),
            Token::Operator(op) => format!("'{}'", op.to_str()),
            Token::Literal(kind, _) => match kind {
                LitKind::Ident => "Identifier".to_string(),
                LitKind::String => "String Literals".to_string(),
                LitKind::Integer => "Integer Literals".to_string(),
                _ => unreachable!(),
            },
        }
    }

    pub fn as_actual(&self) -> String {
        match self {
            Token::Operator(_) => self.as_expected(),
            Token::Keyword(_) => self.as_expected(),
            Token::Literal(_, lit) => format!("'{}'", lit),
            _ => unreachable!(),
        }
    }
}
