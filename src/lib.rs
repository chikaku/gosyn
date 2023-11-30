use std::collections::HashMap;
use std::ffi::OsStr;

mod error;
mod parser;
mod scanner;

pub mod ast;
pub mod token;

pub use error::Error;
pub use parser::Parser;

/// parse source code to `ast::File`
pub fn parse_source<S: AsRef<str>>(source: S) -> anyhow::Result<ast::File> {
    parser::Parser::from(source)?.parse_file()
}

/// parse source code from given path to  `ast::File`
pub fn parse_file<P: AsRef<std::path::Path>>(path: P) -> anyhow::Result<ast::File> {
    parser::Parser::from_file(path)?.parse_file()
}

/// parse a directory to packages
pub fn parse_dir<P: AsRef<std::path::Path>>(
    dir_path: P,
) -> anyhow::Result<HashMap<String, ast::Package>> {
    let go = &OsStr::new("go");
    let mut result = HashMap::new();
    for file in std::fs::read_dir(&dir_path)? {
        let path = file?.path();
        if path.extension() == Some(go) {
            let file = parse_file(&path)?;
            result
                .entry(String::from(&file.pkg_name.name))
                .or_insert(ast::Package {
                    // FIXME: here will be executed in every loop
                    path: dir_path.as_ref().into(),
                    files: vec![],
                })
                .files
                .push(file);
        }
    }

    Ok(result)
}
