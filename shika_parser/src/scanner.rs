use crate::token::Operator;
use crate::token::Token;
use crate::{Keyword, LitKind};
use std::ops::Add;
use std::str::FromStr;

pub type PosTok = (usize, Token);

#[derive(Default)]
pub struct Scanner {
    pos: usize,
    source: String,
    lines: Vec<usize>,

    prev: Option<Token>,
    next: Vec<PosTok>,
}

impl Scanner {
    pub fn new<S: AsRef<str>>(source: S) -> Self {
        let mut scan = Self::default();
        scan.source = source.as_ref().into();
        scan
    }

    pub fn position(&self) -> usize {
        self.pos
    }

    pub fn line_info(&self, pos: usize) -> (usize, usize) {
        self.lines
            .iter()
            .zip(self.lines.iter().skip(1))
            .enumerate()
            .find(|(_, (&a, &b))| a < pos && pos < b)
            .map(|(index, (a, _))| (index + 1, pos - a))
            .unwrap_or((1, pos))
    }

    fn add_line(&mut self, line_start: usize) {
        self.lines.push(line_start);
    }

    fn try_insert_semicolon(&mut self, pos: usize) {
        match self.prev {
            Some(
                Token::Literal(..)
                | Token::Operator(
                    Operator::Inc
                    | Operator::Dec
                    | Operator::ParenRight
                    | Operator::BraceRight
                    | Operator::BarackRight,
                )
                | Token::Keyword(
                    Keyword::Break | Keyword::Continue | Keyword::FallThrough | Keyword::Return,
                ),
            ) => self.next.push((pos, Token::Operator(Operator::SemiColon))),
            _ => {}
        }
    }

    pub fn skip_whitespace(&mut self) -> usize {
        let mut skipped = 0;
        while let Some(ch) = self.source.chars().nth(self.pos) {
            if ch.is_whitespace() {
                if ch == '\n' {
                    self.add_line(self.pos + 1);
                    self.try_insert_semicolon(self.pos)
                }

                skipped += 1;
                self.pos += 1;
                continue;
            }

            break;
        }
        skipped
    }

    pub fn next_token(&mut self) -> Option<PosTok> {
        self.skip_whitespace();
        if let Some(pos_tok) = self.next.pop() {
            return Some(pos_tok);
        }

        let (pos, tok) = self.scan_token()?;
        self.prev = Some(tok.clone());
        Some((pos, tok))
    }

    /// return next Token and position
    pub fn scan_token(&mut self) -> Option<PosTok> {
        let pos = self.pos;

        // scan 3 char
        if let Some(next3) = self.source.get(self.pos..self.pos + 3) {
            if let Some(tok) = Operator::from_str(next3).ok() {
                self.pos += 3;
                return Some((pos, tok.into()));
            }
        }

        if let Some(next2) = self.source.get(self.pos..self.pos + 2) {
            if matches!(next2, "//") {
                let comment = self.scan_line_comment();
                self.pos += comment.len();
                return Some((pos, Token::Comment(comment.trim().to_string())));
            }

            if matches!(next2, "/*") {
                let comment = self.scan_general_comment();
                self.pos += comment.len();
                return Some((pos, Token::Comment(comment)));
            }

            if let Some(tok) = Operator::from_str(next2).ok() {
                self.pos += 2;
                return Some((pos, tok.into()));
            }
        }

        let next1 = self.source.get(self.pos..self.pos + 1)?;
        if let Some(tok) = Operator::from_str(next1).ok() {
            self.pos += 1;
            return Some((pos, tok.into()));
        }

        let ch = next1.chars().next().unwrap();
        if ch.is_alphabetic() {
            let identify = next1.to_string().add(self.scan_ident().as_str());
            self.pos += identify.len();

            return match Keyword::from_str(&identify) {
                Ok(word) => Some((pos, Token::Keyword(word))),
                _ => Some((pos, Token::Literal(LitKind::Ident, identify))),
            };
        }

        None
    }

    fn scan_ident(&mut self) -> String {
        self.source
            .chars()
            .skip(self.pos + 1)
            .take_while(|ch| ch.is_alphabetic() || ch.is_alphanumeric())
            .collect()
    }

    /// Scan line comment from `//` to `\n`
    fn scan_line_comment(&mut self) -> String {
        self.source
            .chars()
            .skip(self.pos)
            .take_while(|&ch| ch != '\n')
            .collect()
    }

    /// Scan general comment from `/*` to `*/`  
    /// TODO: handle `*/` not found
    fn scan_general_comment(&mut self) -> String {
        let it0 = self.source.chars().skip(self.pos);
        let it1 = self.source.chars().skip(self.pos + 1);
        let comments = it0
            .zip(it1)
            .take_while(|&x| x != ('*', '/'))
            .map(|(x, _)| x)
            .collect::<String>();

        for (index, ch) in comments.chars().enumerate() {
            if ch == '\n' {
                self.add_line(self.pos + index + 1)
            }
        }

        comments.add("*/")
    }
}

#[cfg(test)]
mod test {
    use crate::scanner::Scanner;
    use crate::token::{Operator, Token};

    #[test]
    fn scan_comment() {
        let mut scanner = Scanner::new("// 123\r\n//123\n/*123*/");

        assert_eq!(
            scanner.next_token().unwrap().1,
            Token::Comment("// 123".into()),
        );

        assert_eq!(
            scanner.next_token().unwrap().1,
            Token::Comment("//123".into()),
        );

        assert_eq!(
            scanner.next_token().unwrap().1,
            Token::Comment("/*123*/".into()),
        );
    }

    #[test]
    fn scan_token() {
        assert_eq!(
            Scanner::new("...").next_token().unwrap().1,
            Operator::Ellipsis.into()
        );

        assert_eq!(
            Scanner::new(">=").next_token().unwrap().1,
            Operator::GreaterEqual.into()
        );
    }

    const CODE: &'static str = r#"package main
    /*  
    
 */

    // 123

    "#;

    #[test]
    fn scan_line_info() {
        let mut scanner = Scanner::new(CODE);
        while let Some(_) = scanner.next_token() {}
        let mut lines = scanner.lines.iter();
        assert_eq!(lines.next(), Some(&13));
        assert_eq!(lines.next(), Some(&22));
        assert_eq!(lines.next(), Some(&27));
        assert_eq!(lines.next(), Some(&31));
        assert_eq!(lines.next(), Some(&32));
        assert_eq!(lines.next(), Some(&43));
        assert_eq!(lines.next(), Some(&44));
        assert_eq!(lines.next(), None);
    }
}
