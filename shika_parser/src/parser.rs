use core::result;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::rc::Rc;

use crate::ast;
use crate::scanner::Scanner;
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
        expect: Token,
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
                match actual {
                    Some(actual) => write!(
                        f,
                        "{:?}:{:?}:{:?} expect {:?} actual {:?}",
                        path, line, offset, expect, actual,
                    ),
                    None => write!(
                        f,
                        "{:?}:{:?}:{:?} expect {:?} found EOF",
                        path, line, offset, expect,
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

impl Parser {
    fn error(&self, pos: usize, expect: Token, actual: Option<Token>) -> Error {
        Error::ParseError {
            expect,
            actual,
            path: self.path.clone(),
            location: self.scan.line_info(pos),
        }
    }

    fn expect_next(&mut self, expect: Token) -> Result<()> {
        match self.next() {
            Some((_, actual)) if actual == expect => Ok(()),
            Some((pos, actual)) => Err(self.error(pos, expect, Some(actual))),
            _ => Err(self.error(self.scan.position(), expect, None)),
        }
    }

    fn expect_identify(&mut self) -> Result<String> {
        let expect = Token::Literal(LitKind::Ident, String::new());
        match self.next() {
            Some((_, Token::Literal(LitKind::Ident, name))) => Ok(name),
            Some((pos, actual)) => Err(self.error(pos, expect, Some(actual))),
            _ => Err(self.error(self.scan.position(), expect, None)),
        }
    }

    fn next(&mut self) -> Option<(usize, Token)> {
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
        file.package = self.expect_identify()?;
        file.document.append(&mut self.lead_comments);
        file.comments.append(&mut self.comments);

        // match EOF or ;
        let expect = Token::Operator(Operator::SemiColon);
        match self.next() {
            Some((_, tok)) if tok == expect => {}
            Some((pos, actual)) => return Err(self.error(pos, expect, Some(actual))),
            None => {
                file.comments.append(&mut self.comments);
                return Ok(file);
            }
        }

        Ok(file)
    }
}

#[cfg(test)]
mod test {
    use super::parse_file;
    use super::Result;
    use crate::parser::parse_source;

    #[test]
    fn from_str() -> Result<()> {
        parse_source("package main")?;

        Ok(())
    }

    #[test]
    fn from_file() -> Result<()> {
        parse_file("testdata/main.go")?;

        Ok(())
    }
}
