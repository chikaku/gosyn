use crate::token::Token;
use crate::token::TokenKind;
use std::fmt::{Debug, Formatter};
use std::io;
use std::path::Path;
use std::path::PathBuf;

/// indicates all possible errors during parsing
pub enum Error {
    /// wrap system IO errors, usually an open error when opening the given path
    IO(io::Error),
    /// syntax error such as some token are not in the right position
    UnexpectedToken {
        path: PathBuf,
        location: (usize, usize),
        expect: Vec<TokenKind>,
        actual: Option<Token>,
    },
    /// some other parser errors include scanner errors
    /// such as parsing numeric literal errors
    Else {
        path: PathBuf,
        location: (usize, usize),
        reason: String,
    },
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::IO(err)
    }
}

impl Error {
    /// reset source path
    pub fn with_path<P: AsRef<Path>>(self, path: P) -> Error {
        let path = path.as_ref().into();
        match self {
            Error::IO(err) => Error::IO(err),
            Self::Else { location, reason, .. } => Error::Else { path, location, reason },
            Self::UnexpectedToken { location, expect, actual, .. } => {
                Error::UnexpectedToken { location, expect, actual, path }
            }
        }
    }
}

impl Debug for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Error::IO(err) => write!(f, "os error: {}", err),
            Error::UnexpectedToken { expect, actual, path, location } => {
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
            Error::Else { path, location, reason } => {
                let (line, offset) = location;
                let path = path.as_os_str().to_str().unwrap();
                write!(f, "{}:{}:{} {:?}", path, line, offset, reason)
            }
        }
    }
}
