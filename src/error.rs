use crate::token::Token;
use crate::token::TokenKind;

use std::fmt::Display;
use std::fmt::{Debug, Formatter};
use std::io;
use std::path::PathBuf;

/// indicates all possible errors during parsing
pub enum Error {
    /// wrap system IO errors, usually an open error when opening the given path
    IO(io::Error),
    /// syntax error such as some token are not in the right position
    UnexpectedToken {
        path: Option<PathBuf>,
        location: (usize, usize),
        expect: Vec<TokenKind>,
        actual: Option<Token>,
    },
    /// some other parser errors include scanner errors
    /// such as parsing numeric literal errors
    Else {
        path: Option<PathBuf>,
        location: (usize, usize),
        reason: String,
    },
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::IO(err)
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IO(err) => write!(f, "os error: {err}"),
            Error::UnexpectedToken { expect, actual, path, location } => {
                let (line, offset) = location;
                let path = match path {
                    Some(path) => format!("{:?}", path.as_os_str()),
                    None => "<input>".to_string(),
                };

                let file_line = format!("{path:?}:{line}:{offset}");
                let exp = match expect.len() {
                    0 => "expected something".to_string(),
                    1 => format!("expected {:?}", expect[0]),
                    _ => format!("expected {expect:?}"),
                };

                match actual {
                    None => write!(f, "{file_line} {exp}, found EOF"),
                    Some(tok) => write!(f, "{file_line} {exp}, found {tok:?}"),
                }
            }
            Error::Else { path, location, reason } => {
                let (line, offset) = location;
                let path = match path {
                    Some(path) => format!("{:?}", path.as_os_str()),
                    None => "<input>".to_string(),
                };

                write!(f, "{path:?}:{line}:{offset} {reason:?}")
            }
        }
    }
}

impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}
