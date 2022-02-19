mod walkdir;

use gosyn::Parser;
use gosyn::Result;
use pprof::protos::Message;
use std::env;
use std::fs;
use std::io::Write;
use std::path::Path;
use std::path::PathBuf;
use std::time::{Duration, Instant};
use walkdir::Walkdir;

fn resolve<P: AsRef<Path>>(path: P) -> PathBuf {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    root.join(path)
}

fn parse_source<P: AsRef<Path>>(source: String, path: P) -> Result<Duration> {
    let clock = Instant::now();
    Parser::from_str(source)
        .parse_file()
        .map(|_| clock.elapsed())
        .map_err(|err| err.with_path(path))
}

#[test]
fn pprof_parser() {
    // kubernetes/vendor/google.golang.org/api/compute/v0.beta/compute-gen.go
    let path = resolve("tests/compute-gen.txt");
    if !path.exists() {
        return;
    }

    let source = fs::read_to_string(&path).unwrap();
    let guard = pprof::ProfilerGuard::new(1000).unwrap();
    let elapsed = parse_source(source, &path).unwrap();
    println!("finished! {}ms", elapsed.as_millis());

    let report = guard.report().build().unwrap();
    let file = fs::File::create("flamegraph.svg").unwrap();
    report.flamegraph(file).unwrap();

    let mut file = fs::File::create("profile.pb").unwrap();
    let profile = report.pprof().unwrap();
    let mut content = Vec::new();
    profile.encode(&mut content).unwrap();
    file.write_all(&content).unwrap();
}

#[test]
fn test_exception_file() -> Result<()> {
    let file = resolve("tests/exception.txt");
    if file.exists() {
        let source = fs::read_to_string(&file)?;
        if source.lines().count() > 1 {
            parse_source(source, file)?;
        }
    }

    Ok(())
}

#[test]
fn test_third_party_projects() -> Result<()> {
    let root = match env::var("SHIKA_PARSER_TEST") {
        Ok(dir) => PathBuf::from(dir),
        _ => return Ok(()),
    };

    let path = root.as_path();
    let mut walk = Walkdir::new(path)?.with_ext("go")?;
    while let Some(path) = walk.next()? {
        println!(
            "{}: {}μs",
            path.as_path().strip_prefix(&root).unwrap().display(),
            parse_source(fs::read_to_string(&path)?, &path)?.as_micros(),
        );
    }

    Ok(())
}
