use crate::token::Operator;
use crate::token::Token;
use crate::{Keyword, LitKind};
use std::collections::VecDeque;
use std::ops::Add;
use std::str::FromStr;

pub type PosTok = (usize, Token);

#[derive(Default)]
pub struct Scanner {
    pos: usize,
    source: String,
    lines: Vec<usize>,

    prev: Option<Token>,
    next: VecDeque<PosTok>,
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
            ) => self
                .next
                .push_front((pos, Token::Operator(Operator::SemiColon))),
            _ => {}
        }
    }

    pub fn skip_whitespace(&mut self) -> usize {
        let mut skipped = 0;
        while let Some(ch) = self.source.chars().nth(self.pos) {
            if ch.is_whitespace() {
                if ch == '\n' {
                    self.add_line(self.pos + 1);
                    self.try_insert_semicolon(self.pos);
                    self.prev = Some(Operator::SemiColon.into());
                }

                skipped += 1;
                self.pos += 1;
                continue;
            }

            break;
        }
        skipped
    }

    pub fn rewind(&mut self, pos_tok: PosTok) {
        self.next.push_front(pos_tok);
    }

    pub fn next_token(&mut self) -> Option<PosTok> {
        if let Some(pos_tok) = self.next.pop_back() {
            return Some(pos_tok);
        }

        self.skip_whitespace();
        if let Some(pos_tok) = self.next.pop_back() {
            return Some(pos_tok);
        }

        let (pos, tok) = self.scan_token()?;
        self.pos += tok.length();
        self.prev = Some(tok.clone());
        Some((pos, tok))
    }

    /// return next Token and position
    pub fn scan_token(&mut self) -> Option<PosTok> {
        let current = self.pos;

        // scan 3 char
        if let Some(next3) = self.source.get(self.pos..self.pos + 3) {
            if let Some(tok) = Operator::from_str(next3).ok() {
                return Some((current, tok.into()));
            }
        }

        if let Some(next2) = self.source.get(self.pos..self.pos + 2) {
            if matches!(next2, "//") {
                let comment = self.scan_line_comment();
                return Some((current, Token::Comment(comment.trim().to_string())));
            }

            if matches!(next2, "/*") {
                let comment = self.scan_general_comment();
                return Some((current, Token::Comment(comment)));
            }

            if let Some(tok) = Operator::from_str(next2).ok() {
                return Some((current, tok.into()));
            }
        }

        let next1 = self.source.get(self.pos..self.pos + 1)?;
        if let Some(tok) = Operator::from_str(next1).ok() {
            return Some((current, tok.into()));
        }

        match next1.chars().nth(0) {
            Some('"' | '`') => Some((
                current,
                Token::Literal(LitKind::String, self.scan_lit_string()),
            )),
            Some(ch) if !ch.is_numeric() => {
                // TODO: fix identify unicode ranges
                // https://golang.org/ref/spec#Letters_and_digits
                let identify = self.scan_identify();
                Some((
                    current,
                    match Keyword::from_str(&identify) {
                        Ok(word) => Token::Keyword(word),
                        _ => Token::Literal(LitKind::Ident, identify),
                    },
                ))
            }
            _ => None,
        }
    }

    /// scan an identify
    /// caller must ensure that the first character is alphabetic
    /// caller should check if identify is a keyword
    fn scan_identify(&mut self) -> String {
        self.source
            .chars()
            .skip(self.pos)
            .take_while(|ch| !ch.is_whitespace())
            .collect()
    }

    fn scan_lit_string(&mut self) -> String {
        let mut chars = self.source.chars().skip(self.pos);
        let ch0 = chars.nth(0).unwrap();
        assert!(ch0 == '"' || ch0 == '`');

        // let chars = chars.skip(1);
        let lit = chars.take_while(|&ch| ch != ch0).collect::<String>();
        let mut chars = self.source.chars().skip(self.pos + lit.len() + 1);
        assert_eq!(chars.next(), Some(ch0));

        format!("{}{}{}", ch0, lit, ch0)
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
    /// TODO: no termination `*/`
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

    #[test]
    fn scan_comment() {
        let mut scanner = Scanner::new("// 123\r\n//123\n/*123*/");
        assert_eq!(&scanner.scan_line_comment(), "// 123\r");
        scanner.pos += 8;
        assert_eq!(&scanner.scan_line_comment(), "//123");
        scanner.pos += 6;
        assert_eq!(&scanner.scan_line_comment(), "/*123*/");
    }

    #[test]
    fn scan_line_info() {
        let code = "package main\n    /*  \n    \n */\n\n    // 123\n\n    ";
        let mut scanner = Scanner::new(code);
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

    #[test]
    fn scan_lit_string() {
        let mut scanner = Scanner::new("\"123\"`2312\n123\"123`");
        assert_eq!(&scanner.scan_lit_string(), "\"123\"");
        scanner.pos += 5;
        assert_eq!(&scanner.scan_lit_string(), "`2312\n123\"123`");
    }
}
