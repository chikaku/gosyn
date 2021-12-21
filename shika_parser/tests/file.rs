#![feature(generators)]

use shika_parser::Parser;
use shika_parser::Result;
use shika_tool::Walkdir;
use std::env;
use std::fs;
use std::path::PathBuf;
use std::time::{Duration, Instant};

#[allow(unused)]
fn parse_source(source: String) -> Result<Duration> {
    let clock = Instant::now();
    Parser::from_str(source)
        .parse_file()
        .map(|_| clock.elapsed())
}

#[test]
fn test_third_party_projects() -> Result<()> {
    let root = match env::var("SHIKA_PARSER_TEST") {
        Ok(dir) => PathBuf::from(dir),
        _ => return Ok(()),
    };

    for entry in root.read_dir()? {
        if let Ok(object) = entry {
            let mut walk = Walkdir::new(object.path())?.with_ext("go")?;
            while let Some(path) = walk.next()? {
                let source = fs::read_to_string(&path)?;
                println!(
                    "{}: {}",
                    path.as_path().strip_prefix(&root).unwrap().display(),
                    match parse_source(source) {
                        Ok(elapsed) => format!("{}μs", elapsed.as_micros()),
                        Err(err) => format!("\n{:?}\n", err),
                    }
                );
            }
        }
    }

    Ok(())
}
