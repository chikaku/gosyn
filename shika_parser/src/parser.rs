use core::result;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::ast;
use crate::scanner::{PosTok, Scanner};
use crate::token::{Keyword, LitKind, Operator, Token};

pub fn parse_source<S: AsRef<str>>(source: S) -> Result<ast::File> {
    Parser::from_str(source).run()
}

pub fn parse_file<P: AsRef<Path>>(path: P) -> Result<ast::File> {
    Parser::from_file(path)?.run()
}

type Result<T> = result::Result<T, Error>;

pub enum Error {
    IO(io::Error),
    ParseError {
        expect: Vec<Token>,
        actual: Option<Token>,
        path: PathBuf,
        location: (usize, usize),
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
            Error::ParseError {
                expect,
                actual,
                path,
                location,
            } => {
                let (line, offset) = location;
                let path = path.as_os_str().to_str().unwrap();
                let expect_str = if expect.len() > 0 {
                    format!(
                        "one of {:?}",
                        expect
                            .iter()
                            .map(|tok| format!("{:?}", tok))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                } else {
                    format!(
                        "{:?}",
                        expect.get(0).expect("expected token shouldn't empty")
                    )
                };

                match actual {
                    Some(actual) => write!(
                        f,
                        "{:?}:{:?}:{:?} expect {:?} actual {:?}",
                        path, line, offset, expect_str, actual,
                    ),
                    None => write!(
                        f,
                        "{:?}:{:?}:{:?} expect {:?} found EOF",
                        path, line, offset, expect_str,
                    ),
                }
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

const VAR: Token = Token::Keyword(Keyword::Var);
const TYPE: Token = Token::Keyword(Keyword::Type);
const FUNC: Token = Token::Keyword(Keyword::Func);
const CONST: Token = Token::Keyword(Keyword::Const);
const IMPORT: Token = Token::Keyword(Keyword::Import);
const PAREN_LEFT: Token = Token::Operator(Operator::ParenLeft);
const PAREN_RIGHT: Token = Token::Operator(Operator::ParenRight);
const SEMI_COLON: Token = Token::Operator(Operator::SemiColon);

impl Parser {
    fn unexpected(&self, pos: usize, expect: Vec<Token>, actual: Token) -> Error {
        Error::ParseError {
            expect,
            actual: Some(actual),
            path: self.path.clone(),
            location: self.scan.line_info(pos),
        }
    }

    fn unexpected_none(&self, expect: Vec<Token>) -> Error {
        Error::ParseError {
            expect,
            actual: None,
            path: self.path.clone(),
            location: self.scan.line_info(self.scan.position()),
        }
    }

    fn expect_next(&mut self, expect: Token) -> Result<()> {
        match self.next() {
            Some((_, actual)) if actual == expect.clone() => Ok(()),
            Some((pos, actual)) => Err(self.unexpected(pos, vec![expect], actual)),
            _ => Err(self.unexpected_none(vec![expect])),
        }
    }

    fn expect_next_none_or(&mut self, expect: Token) -> Result<bool> {
        match self.next() {
            None => Ok(true),
            Some((_, actual)) if actual == expect => Ok(false),
            Some((pos, other)) => Err(self.unexpected(pos, vec![expect], other)),
        }
    }

    fn expect_identify(&mut self) -> Result<ast::Ident> {
        let expect = Token::Literal(LitKind::Ident, String::new());
        match self.next() {
            Some((pos, Token::Literal(LitKind::Ident, name))) => Ok(ast::Ident { pos, name }),
            Some((pos, actual)) => Err(self.unexpected(pos, vec![expect], actual)),
            _ => Err(self.unexpected_none(vec![expect])),
        }
    }

    fn expect_literal(&mut self, expect: LitKind) -> Result<ast::BasicLit> {
        // TODO: handle literal symbol
        let fake = Token::Literal(expect, String::new());
        let exp_list = vec![fake];
        match self.next() {
            Some((pos, Token::Literal(kind, value))) if kind == expect => {
                Ok(ast::BasicLit { pos, kind, value })
            }
            Some((pos, actual)) => Err(self.unexpected(pos, exp_list, actual)),
            _ => Err(self.unexpected_none(exp_list)),
        }
    }

    fn rewind(&mut self, pos_tok: Option<PosTok>) {
        if let Some(pos_tok) = pos_tok {
            self.scan.rewind(pos_tok);
        }
    }

    fn next(&mut self) -> Option<PosTok> {
        let mut pos_tok = self.scan.next_token();
        while let Some((pos, Token::Comment(text))) = pos_tok {
            let comment = Rc::new(ast::Comment { pos, text });
            self.comments.push(comment.clone());
            self.lead_comments.push(comment.clone());
            if self.scan.skip_whitespace() > 0 {
                self.lead_comments.clear();
            }

            pos_tok = self.scan.next_token();
        }

        pos_tok
    }

    pub fn run(&mut self) -> Result<ast::File> {
        let mut file = ast::File::default();
        file.path = self.path.clone();

        // match Package {identify} with comments
        self.expect_next(Keyword::Package.into())?;
        file.name = self.expect_identify()?;
        file.document.append(&mut self.lead_comments);
        self.expect_next_none_or(SEMI_COLON)?;

        // match Import declaration
        file.imports.extend(self.parse_imports()?);

        // match Var Const Type Func
        match self.next() {
            Some((pos, VAR)) => {
                self.rewind(Some((pos, VAR)));
                self.parse_var();
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
        let mut pos_tok = self.next();
        while matches!(pos_tok, Some((_, IMPORT))) {
            pos_tok = self.next();
            if matches!(pos_tok, Some((_, PAREN_LEFT))) {
                imports.extend(self.parse_import_group()?);
                self.expect_next_none_or(SEMI_COLON)?;
                pos_tok = self.next();
                continue;
            }

            self.rewind(pos_tok);
            imports.push(self.parse_import_sepc()?);
            self.expect_next_none_or(SEMI_COLON)?;
            pos_tok = self.next();
        }

        self.rewind(pos_tok);
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
        let (name, path) = match self.next() {
            Some((pos, Token::Literal(LitKind::Ident, name))) => (
                Some(ast::Ident { pos, name }),
                self.expect_literal(kind)?.into(),
            ),
            Some((pos, Token::Operator(Operator::Period))) => {
                let name = String::from(".");
                (
                    Some(ast::Ident { pos, name }),
                    self.expect_literal(kind)?.into(),
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
        let mut pos_tok = self.next();
        while !matches!(pos_tok, Some((_, PAREN_RIGHT))) {
            self.rewind(pos_tok);
            imports.push(self.parse_import_sepc()?);
            pos_tok = self.next();
            if matches!(pos_tok, Some((_, SEMI_COLON))) {
                pos_tok = self.next();
            }
        }

        Ok(imports)
    }

    fn parse_var(&mut self) {}
}

#[cfg(test)]
mod test {
    use super::parse_file;
    use super::Result;
    use crate::ast::Import;
    use crate::parser::{parse_source, Parser};

    #[test]
    fn parse_package() -> Result<()> {
        let ast = parse_source("package main")?;
        assert_eq!(&ast.name.name, "main");

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
        _ "libc"
        d "libd"
    )

    "#;
}
