#![feature(exclusive_range_pattern)]
#![feature(assert_matches)]
#![feature(bool_to_option)]
#![feature(trait_alias)]

mod ast;
mod error;
mod parser;
mod scanner;
mod token;

pub use error::Error;
pub use parser::*;
pub use scanner::*;
pub use token::*;

type Result<T> = core::result::Result<T, Error>;

pub fn parse_source<S: AsRef<str>>(source: S) -> Result<ast::File> {
    Parser::from_str(source).parse_file()
}

pub fn parse_file<P: AsRef<std::path::Path>>(path: P) -> Result<ast::File> {
    Parser::from_file(path)?.parse_file()
}
