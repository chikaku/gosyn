#![feature(exclusive_range_pattern)]
#![feature(assert_matches)]
#![feature(bool_to_option)]
#![feature(trait_alias)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]

mod ast_impl;
mod error;
mod parser;
mod scanner;

pub mod ast;
pub mod token;

pub use parser::Parser;

/// represent the offset of a `Token` relative to the beginning of source code
pub type Pos = usize;

/// a tuple of `(Pos, Token)`
pub type PosTok = (Pos, token::Token);

pub use error::Error;

/// standard parser result
pub type Result<T> = core::result::Result<T, Error>;

/// parse source code to `ast::File`
pub fn parse_source<S: AsRef<str>>(source: S) -> Result<ast::File> {
    parser::Parser::from_str(source).parse_file()
}

/// parse source code from given path to  `ast::File`
pub fn parse_file<P: AsRef<std::path::Path>>(path: P) -> Result<ast::File> {
    parser::Parser::from_file(path)?.parse_file()
}
