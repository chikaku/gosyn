use crate::token::Pos;
use std::path::PathBuf;
use std::rc::Rc;

pub struct Comment {
    pub pos: Pos,
    pub text: String,
}

pub struct Import {
    pub docs: Vec<Comment>,
    pub name: String,
    pub path: String,
}

#[derive(Default)]
pub struct File {
    pub path: PathBuf,
    pub line_info: Vec<usize>,

    pub comments: Vec<Rc<Comment>>,
    pub document: Vec<Rc<Comment>>,
    pub package: String,
    pub imports: Vec<Import>,
}
