use core::result;
use std::assert_matches::assert_matches;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::ast::{self, BasicLit, Expression, FuncLit, Ident};
use crate::ast::{ChanMode, VarSpec};
use crate::scanner::{PosTok, Scanner};
use crate::token::IntoKind;
use crate::token::{Keyword, LitKind, Operator, Token};
use crate::{Pos, TokenKind};

use shika_proc_macro::EnumFrom;

pub fn parse_source<S: AsRef<str>>(source: S) -> Result<ast::File> {
    Parser::from_str(source).run()
}

pub fn parse_file<P: AsRef<Path>>(path: P) -> Result<ast::File> {
    Parser::from_file(path)?.run()
}

type Result<T> = result::Result<T, Error>;

#[derive(EnumFrom)]
pub enum Error {
    #[enum_from(inner)]
    IO(io::Error),
    UnexpectedToken {
        path: PathBuf,
        location: (usize, usize),
        expect: Vec<TokenKind>,
        actual: Option<Token>,
    },
    Else {
        path: PathBuf,
        location: (usize, usize),
        reason: String,
    },
}

impl Debug for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IO(err) => write!(f, "os error: {}", err),
            Error::UnexpectedToken {
                expect,
                actual,
                path,
                location,
            } => {
                let (line, offset) = location;
                let path = path.as_os_str().to_str().unwrap();
                let file_line = format!("{}:{}:{}", path, line, offset);
                let exp = match expect.len() {
                    0 => format!("expected something"),
                    1 => format!("expected {:?}", expect[0]),
                    _ => format!("expected {:?}", expect),
                };

                match actual {
                    None => write!(f, "{} {}, found EOF", file_line, exp),
                    Some(tok) => write!(f, "{} {}, found {:?}", file_line, exp, tok),
                }
            }
            Error::Else {
                path,
                location,
                reason,
            } => {
                let (line, offset) = location;
                let path = path.as_os_str().to_str().unwrap();
                write!(f, "{:}:{:}:{:} {:?}", path, line, offset, reason)
            }
        }
    }
}

#[derive(Default)]
pub struct Parser {
    path: PathBuf,
    scan: Scanner,

    current: Option<PosTok>,
    comments: Vec<Rc<ast::Comment>>,
    lead_comments: Vec<Rc<ast::Comment>>,
}

impl Parser {
    pub fn from_str<S: AsRef<str>>(s: S) -> Self {
        let mut parser = Self::default();
        parser.path = PathBuf::from("<input>");
        parser.scan = Scanner::new(s);
        parser.next().expect("unpexected new Parser error");

        parser
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut source = String::new();
        File::open(path.as_ref())?.read_to_string(&mut source)?;

        let mut parser = Parser::default();
        parser.path = PathBuf::from(path.as_ref());
        parser.scan = Scanner::new(source);
        parser.next()?;

        Ok(parser)
    }
}

const ERR_PKG_NAME_BLANK: &'static str = "package name can't be blank";

const BLANK: &'static str = "_";

const VAR: Token = Token::Keyword(Keyword::Var);
const MAP: Token = Token::Keyword(Keyword::Map);
const CHAN: Token = Token::Keyword(Keyword::Chan);
const TYPE: Token = Token::Keyword(Keyword::Type);
const FUNC: Token = Token::Keyword(Keyword::Func);
const CONST: Token = Token::Keyword(Keyword::Const);
const IMPORT: Token = Token::Keyword(Keyword::Import);

const STAR: Token = Token::Operator(Operator::Sub);
const ARROW: Token = Token::Operator(Operator::Arrow);
const COMMA: Token = Token::Operator(Operator::Comma);
const ASSIGN: Token = Token::Operator(Operator::Assign);
const PERIOD: Token = Token::Operator(Operator::Period);
const PAREN_LEFT: Token = Token::Operator(Operator::ParenLeft);
const PAREN_RIGHT: Token = Token::Operator(Operator::ParenRight);
const SEMI_COLON: Token = Token::Operator(Operator::SemiColon);
const BARACK_LEFT: Token = Token::Operator(Operator::BarackLeft);
const BARACK_RIGHT: Token = Token::Operator(Operator::BarackRight);

#[allow(dead_code)]
const BRACE_LEFT: Token = Token::Operator(Operator::BraceLeft);
#[allow(dead_code)]
const BRACE_RIGHT: Token = Token::Operator(Operator::BraceRight);

const LIT_STRING: TokenKind = TokenKind::Literal(LitKind::String);

impl Parser {
    fn unexpected<K: IntoKind>(&self, expect: Vec<K>, actual: Option<PosTok>) -> Error {
        let (pos, actual) = actual
            .map(|(pos, tok)| (pos, Some(tok)))
            .unwrap_or((self.scan.position(), None));

        let expect = expect.iter().map(|&x| x.into()).collect();
        Error::UnexpectedToken {
            expect,
            actual,
            path: self.path.clone(),
            location: self.scan.line_info(pos),
        }
    }

    fn else_error_at<S: AsRef<str>>(&self, pos: Pos, reason: S) -> Error {
        Error::Else {
            path: self.path.clone(),
            location: self.scan.line_info(pos),
            reason: reason.as_ref().to_string(),
        }
    }

    fn else_error<S: AsRef<str>>(&self, reason: S) -> Error {
        self.else_error_at(self.scan.position(), reason)
    }

    fn expect<K: IntoKind>(&mut self, expect: K) -> Result<()> {
        if let Some((_, tok)) = &self.current {
            if tok.kind() == expect.into() {
                self.next()?;
                return Ok(());
            }
        }

        Err(self.unexpected(vec![expect.into()], self.current.to_owned()))
    }

    fn current_is<K: IntoKind>(&self, expect: K) -> bool {
        match &self.current {
            Some((_, tok)) => tok.kind() == expect.into(),
            _ => false,
        }
    }

    /// skip while current equal to expect
    fn skipped<K: IntoKind>(&mut self, expect: K) -> Result<bool> {
        self.current_is(expect)
            .then(|| self.next().map(|_| true))
            .unwrap_or(Ok(false))
    }

    /// check next token must be expect and go to next
    fn expect_next(&mut self, expect: TokenKind) -> Result<()> {
        self.next()?;
        self.expect(expect)?;
        self.next();
        Ok(())
    }

    /// if current token match with expect then go next
    fn forward_matched(&mut self, expect: Token) -> Result<bool> {
        Ok(match self.current.as_ref() {
            Some((_, tok)) if tok == &expect => {
                self.next()?;
                true
            }
            _ => false,
        })
    }

    fn expect_none_or<K: IntoKind>(&mut self, expect: K) -> Result<bool> {
        match self.current.to_owned() {
            None => Ok(true),
            Some((_, actual)) if actual.kind() == expect.into() => {
                self.next()?;
                Ok(false)
            }
            other @ _ => Err(self.unexpected(vec![expect.into()], other)),
        }
    }

    fn parse_ident(&mut self) -> Result<ast::Ident> {
        match self.current.to_owned() {
            Some((pos, Token::Literal(LitKind::Ident, name))) => Ok(ast::Ident { pos, name }),
            other @ _ => Err(self.unexpected(vec![LitKind::Ident], other)),
        }
    }

    fn parse_pkg_name(&mut self) -> Result<ast::Ident> {
        let id = self.parse_ident()?;
        match id.name.as_str() {
            BLANK => Err(self.else_error_at(id.pos, ERR_PKG_NAME_BLANK)),
            _ => {
                self.next()?;
                Ok(id)
            }
        }
    }

    /// expect next to be a string literal and go to next
    fn expect_string_literal(&mut self) -> Result<ast::StringLit> {
        match self.next_owned()? {
            Some((pos, Token::Literal(LitKind::String, value))) => {
                self.next()?;
                Ok(ast::StringLit { pos, value })
            }
            other @ _ => Err(self.unexpected(vec![LitKind::String], other)),
        }
    }

    fn expect_identifier_list(&mut self) -> Result<Vec<ast::Ident>> {
        let mut result = vec![self.parse_ident()?];
        while matches!(self.next()?, Some((_, Token::Operator(Operator::Comma)))) {
            result.push(self.parse_ident()?);
        }

        Ok(result)
    }

    fn scan_next(&mut self) -> Result<Option<PosTok>> {
        self.scan
            .next_token()
            .map_err(|serr| self.else_error_at(serr.pos, serr.reason))
    }

    fn next(&mut self) -> Result<Option<&PosTok>> {
        let mut pos_tok = self.scan_next()?;
        while let Some((pos, Token::Comment(text))) = pos_tok {
            let comment = Rc::new(ast::Comment { pos, text });
            self.comments.push(comment.clone());
            self.lead_comments.push(comment.clone());
            if self.scan.skip_whitespace() > 0 {
                self.lead_comments.clear();
            }

            pos_tok = self.scan_next()?;
        }

        self.current = pos_tok;
        Ok(self.current.as_ref())
    }

    fn next_owned(&mut self) -> Result<Option<PosTok>> {
        Ok(match self.next()? {
            None => None,
            Some(pk) => Some(pk.to_owned()),
        })
    }

    pub fn parse_package(&mut self) -> Result<ast::Ident> {
        self.expect(Keyword::Package)?;
        self.parse_pkg_name()
    }

    pub fn run(&mut self) -> Result<ast::File> {
        let mut file = ast::File::default();
        file.path = self.path.clone();

        file.name = self.parse_package()?;
        file.document.append(&mut self.lead_comments);
        self.expect_none_or(Operator::SemiColon)?;

        // match Import declaration
        file.imports.extend(self.parse_imports()?);

        loop {
            self.next()?;
            let tok = self.current.to_owned().map(|(_, tok)| tok);

            // match Var Const Type Func declaration
            // match tok {
            //     Some(VAR) => {
            //         self.parse_var()?;
            //     }
            //     Some(CONST) => {}
            //     Some(TYPE) => {}
            //     Some(FUNC) => {}
            //     None => {
            //         file.comments.append(&mut self.comments);
            //         return Ok(file);
            //     }
            //     Some(other) => {
            //         return Err(self.unexpected(
            //             self.scan.position(),
            //             vec![VAR, CONST, TYPE, FUNC],
            //             other,
            //         ));
            //     }
            // }
            unimplemented!()
        }
    }

    pub fn parse_imports(&mut self) -> Result<Vec<ast::Import>> {
        let mut imports = vec![];
        while self.current_is(Keyword::Import) {
            self.next()?;
            match self.current_is(Operator::ParenLeft) {
                true => imports.extend(self.parse_import_group()?),
                false => imports.push(self.parse_import_sepc()?),
            }
            self.skipped(Operator::SemiColon)?;
        }

        Ok(imports)
    }

    /// parse import group like
    /// ```go
    /// import (
    ///     net "x/net"
    ///     sys "x/sys"
    /// )
    /// ```
    fn parse_import_group(&mut self) -> Result<Vec<ast::Import>> {
        // come here only because we met a ( so need go next
        // current must be ParenLeft
        self.next()?;
        let mut imports = vec![];
        while !self.current_is(Operator::ParenRight) {
            imports.push(self.parse_import_sepc()?);
            self.skipped(Operator::SemiColon)?;
        }

        Ok(imports)
    }

    fn parse_import_sepc(&mut self) -> Result<ast::Import> {
        let mut docs = Vec::new();
        docs.append(&mut self.lead_comments);

        let exp_list: Vec<TokenKind> = vec![
            Operator::Period.into(),
            LitKind::Ident.into(),
            LitKind::String.into(),
        ];

        let (name, path) = match self.current.to_owned() {
            Some((pos, Token::Literal(LitKind::Ident, name))) => (
                Some(ast::Ident { pos, name }),
                self.expect_string_literal()?.into(),
            ),
            Some((pos, Token::Operator(Operator::Period))) => {
                let name = String::from(".");
                (
                    Some(ast::Ident { pos, name }),
                    self.expect_string_literal()?.into(),
                )
            }
            Some((pos, Token::Literal(LitKind::String, value))) => {
                self.next()?;
                (None, ast::StringLit { pos, value })
            }
            other @ _ => return Err(self.unexpected(exp_list, other)),
        };

        Ok(ast::Import { docs, name, path })
    }

    fn parse_var(&mut self) -> Result<Vec<VarSpec>> {
        let mut vars = vec![];
        if self.skipped(Keyword::Var)? {
            if self.skipped(Operator::ParenLeft)? {
                while !self.current_is(Operator::ParenRight) {
                    vars.push(self.parse_var_spec()?);
                    self.skipped(Operator::SemiColon)?;
                }
                return Ok(vars);
            }

            vars.push(self.parse_var_spec()?);
            self.skipped(Operator::SemiColon)?;
        }

        Ok(vars)
    }

    fn parse_var_spec(&mut self) -> Result<ast::VarSpec> {
        let mut spec = ast::VarSpec::default();
        spec.name = self.expect_identifier_list()?;
        if !self.forward_matched(ASSIGN)? {
            spec.typ = Some(self.parse_type()?);
        }

        if self.forward_matched(ASSIGN)? {
            // TODO: expect ExpressionList
        }

        // TODO: should expect something ?
        Ok(spec)
    }

    pub fn parse_type(&mut self) -> Result<ast::Type> {
        let (pos, tok) = self
            .current
            .to_owned()
            .ok_or(self.else_error("unexpecred EOF"))?;

        match tok {
            Token::Literal(LitKind::Ident, name) if &name != BLANK => {
                let id0 = ast::Ident { pos, name };
                // TODO: nexted !
                match self.next()? {
                    Some((_, PERIOD)) => Ok(ast::Type::PkgNamed(id0, self.parse_ident()?)),
                    _ => Ok(ast::Type::Named(id0.into())),
                }
            }
            PAREN_LEFT => {
                self.next()?;
                let typ = self.parse_type()?;
                self.expect(PAREN_RIGHT.kind())?;
                return Ok(typ);
            }
            BARACK_LEFT => {
                match self.next()? {
                    Some((_, BARACK_RIGHT)) => {
                        self.next()?;
                        let elem_type = self.parse_type()?;
                        return Ok(ast::Type::Slice(Box::new(elem_type)));
                    }
                    // Array Type
                    // TODO: expect Expression
                    _ => unimplemented!(),
                }
            }
            MAP => {
                self.expect_next(BARACK_LEFT.kind())?;
                let key_type = Box::new(self.parse_type()?);
                self.expect(BARACK_RIGHT.kind())?;
                self.next()?;
                let val_type = Box::new(self.parse_type()?);
                Ok(ast::Type::Map(key_type, val_type))
            }
            CHAN => {
                self.next()?;
                let ch_mode = match self.forward_matched(ARROW)? {
                    true => ChanMode::Send,
                    false => ChanMode::Double,
                };

                let ch_type = Box::new(self.parse_type()?);
                Ok(ast::Type::Channel(ch_mode, ch_type))
            }
            ARROW => {
                self.next()?;
                Ok(ast::Type::Channel(
                    ChanMode::Receive,
                    Box::new(self.parse_type()?),
                ))
            }
            STAR => Ok(ast::Type::Pointer(Box::new(self.parse_type()?))),
            _ => unimplemented!(), // TODO: raise error
        }
    }

    pub fn parse_expr(&mut self) -> Result<ast::Expression> {
        self.parse_binary_expr()
    }

    fn parse_binary_expr(&mut self) -> Result<ast::Expression> {
        self.parse_unary_expr()
    }

    fn parse_unary_expr(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self
            .current
            .to_owned()
            .ok_or(self.else_error("unexpecred EOF"))?;

        match tok {
            Token::Operator(
                op
                @ (Operator::Add | Operator::Sub | Operator::Not | Operator::Xor | Operator::And),
            ) => Ok(ast::Expression::Unary {
                pos,
                operator: op,
                operand: Box::new(self.parse_unary_expr()?),
            }),
            Token::Operator(op @ Operator::Arrow) => {
                // TODO: handle <- chan int(nil)
                Ok(Expression::Invalid)
            }
            Token::Operator(Operator::Mul) => Ok(Expression::Star {
                pos,
                right: Box::new(self.parse_unary_expr()?),
            }),
            _ => self.parse_primary_expr(),
        }
    }

    fn parse_primary_expr(&mut self) -> Result<ast::Expression> {
        let operand = self.parse_operand()?;
        match self.next()? {
            Some((_, PERIOD)) => match self.next_owned()? {
                // TODO: check type or expr
                Some((pos, Token::Literal(LitKind::Ident, name))) => Ok(Expression::Selector {
                    left: Box::new(operand),
                    right: ast::Ident { pos, name },
                }),
                // TODO: check type
                Some((_, PAREN_LEFT)) => {
                    self.next()?;
                    let typ = match self.current {
                        Some((_, TYPE)) => None,
                        _ => Some(self.parse_type()?),
                    };

                    self.expect_next(PAREN_RIGHT.kind())?;
                    Ok(Expression::TypeAssert {
                        left: Box::new(operand),
                        assert: Box::new(typ),
                    })
                }
                _ => Err(self.else_error("expect selector or type assertion")),
            },
            // Some((_, BARACK_LEFT)) => {}
            // Some((_, PAREN_LEFT)) => {}
            // Some((_, BRACE_LEFT)) => {}
            _ => unimplemented!(),
        }
    }

    fn parse_operand(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self
            .current
            .to_owned()
            .ok_or(self.else_error("unexpecred EOF"))?;

        match tok {
            Token::Literal(LitKind::Ident, name) => Expression::Ident(Ident { pos, name }),
            Token::Literal(kind, value) => Expression::BasicLit(BasicLit { pos, kind, value }),
            PAREN_LEFT => {
                let expr = self.parse_expr()?;
                self.expect_next(PAREN_RIGHT.kind())?;
                Expression::Paren {
                    pos: (pos, self.scan.position() - 1),
                    expr: Box::new(expr),
                }
            }
            FUNC => {
                // TODO: parse_func_type
                unimplemented!()
            }
            _ => unimplemented!(),
        };

        Ok(Expression::Invalid)
    }

    fn parse_func_type(&mut self) -> Result<ast::FuncLit> {
        self.expect(FUNC.kind())?;
        self.expect_next(PAREN_LEFT.kind())?;
        while !matches!(self.next()?, Some((_, PAREN_RIGHT))) {}

        Ok(ast::FuncLit {
            typ: Box::new(ast::Type::Function()),
        })
    }

    fn parse_params_list(&mut self) {}
}

#[cfg(test)]
mod test {
    use std::assert_matches::assert_matches;

    use crate::ast::{ChanMode, Type};
    use crate::parser::Parser;
    use crate::{Keyword, Token};

    const VAR_CODE: &'static str = r#"
    var x1 int
    var x2, x3 int
    var x4 = 1
    var x5, x6 = 1, 2
    var x7 int = 1
    var x8, x9 int = 1, 2
    
    var (
        x10      int
        x11, x12 int = 3, 4;
        x15, x16     = 7, 8;
    )
    
    var (x17 int = 9; x18 int = 10);
    var (x19=11;x20 int=12;);
    "#;

    #[test]
    fn parse_var() {
        let vars = |s| Parser::from_str(s).parse_var();

        assert!(vars(VAR_CODE).is_ok());
    }

    #[test]
    fn parse_type() {
        let type_of = |x| Parser::from_str(x).parse_type().ok();

        assert_matches!(type_of("int"), Some(Type::Named(_)));
        assert_matches!(type_of("int"), Some(Type::Named(_)));
        assert_matches!(type_of("((int))"), Some(Type::Named(_)));
        assert_matches!(type_of("a.b;"), Some(Type::PkgNamed(..)));
        assert_matches!(type_of("[]int;"), Some(Type::Slice(..)));
        assert_matches!(type_of("map[int]map[int]int;"), Some(Type::Map(..)));

        assert_matches!(
            type_of("chan int;"),
            Some(Type::Channel(ChanMode::Double, ..))
        );

        assert_matches!(
            type_of("<-chan <- chan int;"),
            Some(Type::Channel(ChanMode::Receive, ..))
        );
    }

    #[test]
    fn parse_imports() {
        let imps = |s: &str| Parser::from_str(s).parse_imports();

        assert!(imps("import ()").is_ok());
        assert!(imps("import `aa`").is_ok());
        assert!(imps("import (\n\n)").is_ok());
        assert!(imps(r#"import "liba""#).is_ok());
        assert!(imps(r#"import . "libb""#).is_ok());
        assert!(imps(r#"import _ "libc""#).is_ok());
        assert!(imps(r#"import d "libd""#).is_ok());
        assert!(imps("import (\"a\"\n. \"b\"\n_ \"c\"\nd \"d\")").is_ok());

        assert!(imps("import _").is_err());
        assert!(imps("import _ _").is_err());
        assert!(imps("import . ()").is_err());
    }

    #[test]
    fn parse_package() {
        let pkg = |s| Parser::from_str(s).parse_package();

        assert!(pkg("package main").is_ok());
        assert!(pkg("package\n\nmain").is_ok());

        assert!(pkg("\n\n").is_err());
        assert!(pkg("package _").is_err());
        assert!(pkg("package\n_").is_err());
        assert!(pkg("package package").is_err());
    }
}
