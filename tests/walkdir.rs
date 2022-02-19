use std::ffi::OsStr;
use std::ffi::OsString;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

pub struct Walkdir {
    dirs: Vec<fs::ReadDir>,
}

impl Walkdir {
    pub fn new<P: AsRef<Path>>(root: P) -> io::Result<Walkdir> {
        let root = root.as_ref();
        let dirs = vec![root.read_dir()?];

        Ok(Walkdir { dirs })
    }

    pub fn with_ext<S: AsRef<OsStr>>(self, ext: S) -> io::Result<Walkext> {
        let dir = self;
        let ext = ext.as_ref().to_os_string();
        Ok(Walkext { dir, ext })
    }

    pub fn next(&mut self) -> io::Result<Option<PathBuf>> {
        match self.dirs.pop() {
            None => Ok(None),
            Some(mut dir) => match dir.next() {
                None => self.next(),
                Some(entry) => {
                    self.dirs.push(dir);
                    match entry {
                        Err(err) => Err(err),
                        Ok(file) => match file.path() {
                            path if path.is_file() => Ok(Some(path)),
                            path if path.is_dir() => {
                                let dir2 = path.read_dir()?;
                                self.dirs.push(dir2);
                                return self.next();
                            }
                            _ => self.next(),
                        },
                    }
                }
            },
        }
    }
}

pub struct Walkext {
    dir: Walkdir,
    ext: OsString,
}

impl Walkext {
    pub fn next(&mut self) -> io::Result<Option<PathBuf>> {
        let some_ext = Some(self.ext.as_os_str());
        let not_matched = |file: &Path| file.extension() != some_ext;

        match self.dir.next()? {
            Some(file) if not_matched(&file) => self.next(),
            other @ _ => Ok(other),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Walkdir;
    use std::env;
    use std::fs;
    use std::io;

    #[test]
    fn list_files() -> io::Result<()> {
        let temp = env::temp_dir();
        let dir = temp.join("walkdir_test");
        fs::create_dir_all(&dir)?;

        println!("list all files...");
        let mut walk = Walkdir::new(&dir)?;
        while let Ok(Some(path)) = walk.next() {
            println!("{:?}", path);
        }

        println!("list go files...");
        let mut walk = Walkdir::new(&dir)?.with_ext("go")?;
        while let Ok(Some(path)) = walk.next() {
            println!("{:?}", path);
        }

        Ok(())
    }
}
