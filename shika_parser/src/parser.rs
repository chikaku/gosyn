use core::result;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::ast;
use crate::ast::{ChanMode, VarSpec};
use crate::scanner::{PosTok, Scanner};
use crate::token::{Keyword, LitKind, Operator, Token};
use crate::Pos;

pub fn parse_source<S: AsRef<str>>(source: S) -> Result<ast::File> {
    Parser::from_str(source).run()
}

pub fn parse_file<P: AsRef<Path>>(path: P) -> Result<ast::File> {
    Parser::from_file(path)?.run()
}

type Result<T> = result::Result<T, Error>;

pub enum Error {
    IO(io::Error),
    UnexpectedToken {
        expect: Vec<Token>,
        actual: Option<Token>,
        path: PathBuf,
        location: (usize, usize),
    },
    Else {
        path: PathBuf,
        location: (usize, usize),
        reason: &'static str,
    },
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Self::IO(err)
    }
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
                    1 => format!("expected {}", expect[0].as_expected()),
                    _ => format!(
                        "expected {}",
                        expect
                            .iter()
                            .map(|t| t.as_expected())
                            .collect::<Vec<_>>()
                            .join(" or ")
                    ),
                };

                match actual {
                    None => write!(f, "{} {}, found EOF", file_line, exp),
                    Some(tok) => write!(f, "{} {}, found {}", file_line, exp, tok.as_actual()),
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

    comments: Vec<Rc<ast::Comment>>,
    lead_comments: Vec<Rc<ast::Comment>>,
}

impl Parser {
    pub fn from_str<S: AsRef<str>>(s: S) -> Self {
        let mut parser = Self::default();
        parser.path = PathBuf::from("<input>");
        parser.scan = Scanner::new(s);

        parser
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut source = String::new();
        File::open(path.as_ref())?.read_to_string(&mut source)?;

        let mut parser = Parser::default();
        parser.path = PathBuf::from(path.as_ref());
        parser.scan = Scanner::new(source);

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
const ASSIGN: Token = Token::Operator(Operator::Assign);
const PERIOD: Token = Token::Operator(Operator::Period);
const PAREN_LEFT: Token = Token::Operator(Operator::ParenLeft);
const PAREN_RIGHT: Token = Token::Operator(Operator::ParenRight);
const SEMI_COLON: Token = Token::Operator(Operator::SemiColon);
const BRACE_LEFT: Token = Token::Operator(Operator::BraceLeft);
const BRACE_RIGHT: Token = Token::Operator(Operator::BraceRight);

const LIT_STRING: Token = Token::Literal(LitKind::String, String::new());

impl Parser {
    fn unexpected(&self, pos: usize, expect: Vec<Token>, actual: Token) -> Error {
        Error::UnexpectedToken {
            expect,
            actual: Some(actual),
            path: self.path.clone(),
            location: self.scan.line_info(pos),
        }
    }

    fn unexpected_none(&self, expect: Vec<Token>) -> Error {
        Error::UnexpectedToken {
            expect,
            actual: None,
            path: self.path.clone(),
            location: self.scan.line_info(self.scan.position()),
        }
    }

    fn else_error(&self, pos: Pos, reason: &'static str) -> Error {
        let path = self.path.clone();
        let location = self.scan.line_info(pos);
        Error::Else {
            path,
            location,
            reason,
        }
    }

    fn expect_next(&mut self, expect: Token) -> Result<()> {
        match self.next()? {
            Some((_, actual)) if actual == expect.clone() => Ok(()),
            Some((pos, actual)) => Err(self.unexpected(pos, vec![expect], actual)),
            _ => Err(self.unexpected_none(vec![expect])),
        }
    }

    fn forward_matched(&mut self, expect: Token) -> Result<bool> {
        let pos_tok = self.next()?;
        Ok(match pos_tok {
            Some((_, tok)) if tok == expect => true,
            _ => {
                self.rewind(pos_tok);
                false
            }
        })
    }

    fn expect_some(&mut self) -> Result<PosTok> {
        self.next()?.ok_or(self.unexpected_none(vec![]))
    }

    fn expect_next_none_or(&mut self, expect: Token) -> Result<bool> {
        match self.next()? {
            None => Ok(true),
            Some((_, actual)) if actual == expect => Ok(false),
            Some((pos, other)) => Err(self.unexpected(pos, vec![expect], other)),
        }
    }

    fn expect_identify(&mut self) -> Result<ast::Ident> {
        let expect = Token::Literal(LitKind::Ident, String::new());
        match self.next()? {
            Some((pos, Token::Literal(LitKind::Ident, name))) => Ok(ast::Ident { pos, name }),
            Some((pos, actual)) => Err(self.unexpected(pos, vec![expect], actual)),
            _ => Err(self.unexpected_none(vec![expect])),
        }
    }

    fn expect_pkg_name(&mut self) -> Result<ast::PkgName> {
        let id = self.expect_identify()?;
        match id.name.as_str() {
            BLANK => Err(self.else_error(id.pos, ERR_PKG_NAME_BLANK)),
            _ => Ok(ast::PkgName(id)),
        }
    }

    fn expect_string_literal(&mut self, expect: LitKind) -> Result<ast::StringLit> {
        match self.next()? {
            Some((pos, Token::Literal(kind, value))) if kind == expect => {
                Ok(ast::StringLit { pos, value })
            }
            Some((pos, actual)) => Err(self.unexpected(pos, vec![LIT_STRING], actual)),
            _ => Err(self.unexpected_none(vec![LIT_STRING])),
        }
    }

    fn expect_identifier_list(&mut self) -> Result<Vec<ast::Ident>> {
        let mut result = vec![self.expect_identify()?];
        while self.forward_matched(Token::Operator(Operator::Comma))? {
            result.push(self.expect_identify()?);
        }

        Ok(result)
    }

    fn rewind(&mut self, pos_tok: Option<PosTok>) {
        if let Some(pos_tok) = pos_tok {
            self.scan.rewind(pos_tok);
        }
    }

    fn next(&mut self) -> Result<Option<PosTok>> {
        let mut pos_tok = self.scan.next_token().map_err(|serr| Error::Else {
            path: self.path.clone(),
            location: self.scan.line_info(serr.pos),
            reason: serr.reason,
        })?;

        while let Some((pos, Token::Comment(text))) = pos_tok {
            let comment = Rc::new(ast::Comment { pos, text });
            self.comments.push(comment.clone());
            self.lead_comments.push(comment.clone());
            if self.scan.skip_whitespace() > 0 {
                self.lead_comments.clear();
            }

            pos_tok = self.scan.next_token().map_err(|serr| Error::Else {
                path: self.path.clone(),
                location: self.scan.line_info(serr.pos),
                reason: serr.reason,
            })?;
        }

        Ok(pos_tok)
    }

    pub fn run(&mut self) -> Result<ast::File> {
        let mut file = ast::File::default();
        file.path = self.path.clone();

        // match Package {identify} with comments
        self.expect_next(Keyword::Package.into())?;
        file.name = self.expect_pkg_name()?;
        file.document.append(&mut self.lead_comments);
        self.expect_next_none_or(SEMI_COLON)?;

        // match Import declaration
        file.imports.extend(self.parse_imports()?);

        // match Var Const Type Func declaration
        match self.next()? {
            Some((pos, VAR)) => {
                self.rewind(Some((pos, VAR)));
                self.parse_var()?;
            }
            Some((_, CONST)) => {}
            Some((_, TYPE)) => {}
            Some((_, FUNC)) => {}

            None => {}
            Some((pos, other)) => {
                return Err(self.unexpected(pos, vec![VAR, CONST, TYPE, FUNC], other))
            }
        }

        file.comments.append(&mut self.comments);
        Ok(file)
    }

    fn parse_imports(&mut self) -> Result<Vec<ast::Import>> {
        let mut imports = vec![];
        while self.forward_matched(IMPORT)? {
            if self.forward_matched(PAREN_LEFT)? {
                imports.extend(self.parse_import_group()?);
                self.expect_next_none_or(SEMI_COLON)?;
                continue;
            }

            imports.push(self.parse_import_sepc()?);
            self.expect_next_none_or(SEMI_COLON)?;
        }

        Ok(imports)
    }

    fn parse_import_sepc(&mut self) -> Result<ast::Import> {
        let mut docs = Vec::new();
        docs.append(&mut self.lead_comments);

        let exp_list = vec![
            Operator::Period.into(),
            Token::Literal(LitKind::Ident, String::new()),
            Token::Literal(LitKind::String, String::new()),
        ];

        let kind = LitKind::String;
        let (name, path) = match self.next()? {
            Some((pos, Token::Literal(LitKind::Ident, name))) => (
                Some(ast::Ident { pos, name }),
                self.expect_string_literal(kind)?.into(),
            ),
            Some((pos, Token::Operator(Operator::Period))) => {
                let name = String::from(".");
                (
                    Some(ast::Ident { pos, name }),
                    self.expect_string_literal(kind)?.into(),
                )
            }
            Some((pos, Token::Literal(LitKind::String, value))) => {
                (None, ast::StringLit { pos, value })
            }
            Some((pos, other)) => return Err(self.unexpected(pos, exp_list, other)),
            None => return Err(self.unexpected_none(exp_list)),
        };

        Ok(ast::Import { docs, name, path })
    }

    fn parse_import_group(&mut self) -> Result<Vec<ast::Import>> {
        let mut imports = vec![];
        while !self.forward_matched(PAREN_RIGHT)? {
            imports.push(self.parse_import_sepc()?);
            self.forward_matched(SEMI_COLON)?;
        }

        Ok(imports)
    }

    fn parse_var(&mut self) -> Result<Vec<VarSpec>> {
        let mut vars = vec![];
        if self.forward_matched(VAR)? {
            if self.forward_matched(PAREN_LEFT)? {
                while !self.forward_matched(PAREN_RIGHT)? {
                    vars.push(self.parse_var_spec()?);
                    self.forward_matched(SEMI_COLON)?;
                }
                return Ok(vars);
            }

            vars.push(self.parse_var_spec()?);
            self.expect_next_none_or(SEMI_COLON)?;
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
        let (pos, tok) = self.expect_some()?;
        match tok {
            Token::Literal(LitKind::Ident, name) if &name != BLANK => {
                let id0 = ast::PkgName(ast::Ident { pos, name });
                match self.forward_matched(PERIOD)? {
                    false => Ok(ast::Type::Named(id0.into())),
                    true => Ok(ast::Type::PkgNamed(id0, self.expect_identify()?)),
                }
            }
            PAREN_LEFT => {
                let typ = self.parse_type()?;
                self.expect_next(PAREN_RIGHT)?;
                return Ok(typ);
            }
            BRACE_LEFT => {
                if self.forward_matched(BRACE_RIGHT)? {
                    let elem_type = self.parse_type()?;
                    return Ok(ast::Type::Slice(Box::new(elem_type)));
                }

                // Array Type
                // TODO: expect Expression
                unimplemented!();
            }
            MAP => {
                self.expect_next(BRACE_LEFT)?;
                let key_type = Box::new(self.parse_type()?);
                self.expect_next(BRACE_RIGHT)?;
                let val_type = Box::new(self.parse_type()?);
                Ok(ast::Type::Map(key_type, val_type))
            }
            CHAN => {
                let ch_mode = match self.forward_matched(ARROW)? {
                    true => ChanMode::Send,
                    false => ChanMode::None,
                };

                let ch_type = Box::new(self.parse_type()?);
                Ok(ast::Type::Channel(ch_mode, ch_type))
            }
            ARROW => Ok(ast::Type::Channel(
                ChanMode::Receive,
                Box::new(self.parse_type()?),
            )),
            STAR => Ok(ast::Type::Pointer(Box::new(self.parse_type()?))),
            _ => unimplemented!(), // TODO: raise error
        }
    }
}

#[cfg(test)]
mod test {
    use super::parse_file;
    use super::Result;
    use crate::ast::Import;
    use crate::ast::Type;
    use crate::parser::{parse_source, Parser};

    #[test]
    fn parse_package() -> Result<()> {
        let ast = parse_source("package main")?;
        assert_eq!(&ast.name.0.name, "main");

        Ok(())
    }

    #[test]
    fn parse_type() -> Result<()> {
        let type_of = |x| Parser::from_str(x).parse_type();
        assert!(matches!(type_of("int")?, Type::Named(_)));
        assert!(matches!(type_of("((int))")?, Type::Named(_)));
        assert!(matches!(type_of("a.b;")?, Type::PkgNamed(..)));
        assert!(matches!(type_of("[]int;")?, Type::Slice(..)));
        assert!(matches!(type_of("map[int]map[int]int;")?, Type::Map(..)));
        assert!(matches!(type_of("<-chan <- chan int;")?, Type::Channel(..)));

        Ok(())
    }

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
    fn parse_var() -> Result<()> {
        let ast = Parser::from_str(VAR_CODE).parse_var()?;
        assert_eq!(ast.len(), 9);

        Ok(())
    }

    #[test]
    fn parse_imports() -> Result<()> {
        let imports = Parser::from_str(IMPORT_CODE).parse_imports()?;
        let mut imports = imports.iter().map(|Import { name, path, .. }| {
            (
                match name {
                    None => None,
                    Some(idt) => Some(idt.name.as_ref()),
                },
                path.value.as_str(),
            )
        });

        assert_eq!(imports.next(), Some((None, "\"liba\"")));
        assert_eq!(imports.next(), Some((Some("."), "\"libb\"")));
        assert_eq!(imports.next(), Some((Some("_"), "\"libc\"")));
        assert_eq!(imports.next(), Some((Some("d"), "\"libd\"")));
        assert_eq!(imports.next(), Some((None, "\"liba\"")));
        assert_eq!(imports.next(), Some((Some("."), "\"libb\"")));
        assert_eq!(imports.next(), Some((Some("_"), "\"libc\"")));
        assert_eq!(imports.next(), Some((Some("d"), "\"libd\"")));
        assert_eq!(imports.next(), None);

        Ok(())
    }

    #[test]
    fn from_file() -> Result<()> {
        parse_file("testdata/main.go")?;

        Ok(())
    }

    const IMPORT_CODE: &'static str = r#"
    import ()
    import (
    
    )
    import   "liba"
    import . "libb"
    import _ "libc"
    import d "libd"
    import (
          "liba"
        . "libb"
     )
     import (
        _ "libc"
        d "libd")

    "#;
}
