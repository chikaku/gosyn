use crate::Token;
use crate::TokenKind;
use std::fmt::{Debug, Formatter};
use std::io;
use std::path::PathBuf;

use shika_proc_macro::EnumFrom;

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
