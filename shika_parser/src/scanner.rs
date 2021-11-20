use crate::token::Operator;
use crate::token::Token;
use crate::{Keyword, LitKind};
use std::collections::VecDeque;
use std::fmt::{Debug, Formatter};
use std::ops::Add;
use std::str::FromStr;
use unic_ucd_category::GeneralCategory;

pub type Pos = usize;
pub type PosTok = (Pos, Token);

pub struct Error {
    pub pos: Pos,
    pub reason: String,
}

impl Debug for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.reason)
    }
}

pub type Result<T> = core::result::Result<T, Error>;

#[allow(dead_code)]
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
            .enumerate()
            .take_while(|(_, &start)| pos >= start)
            .last()
            .map(|(index, &start)| (index + 1, pos - start))
            .unwrap_or((1, pos))
    }

    fn add_line(&mut self, line_start: usize) {
        self.lines.push(line_start);
    }

    fn error<S: AsRef<str>>(&self, reason: S) -> Error {
        Error {
            pos: self.pos,
            reason: reason.as_ref().to_string(),
        }
    }

    fn error_at<S: AsRef<str>>(&self, pos: usize, reason: S) -> Error {
        Error {
            pos,
            reason: reason.as_ref().to_string(),
        }
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

    pub fn next_token(&mut self) -> Result<Option<PosTok>> {
        if let Some(pos_tok) = self.next.pop_back() {
            return Ok(Some(pos_tok));
        }

        self.skip_whitespace();
        if let Some(pos_tok) = self.next.pop_back() {
            return Ok(Some(pos_tok));
        }

        match self.scan_token()? {
            Some((pos, tok)) => {
                self.pos += tok.length();
                self.prev = Some(tok.clone());
                Ok(Some((pos, tok)))
            }
            None => Ok(None),
        }
    }

    /// return next Token and position
    pub fn scan_token(&mut self) -> Result<Option<PosTok>> {
        let current = self.pos;

        // scan 3 char
        if let Some(next3) = self.source.get(self.pos..self.pos + 3) {
            if let Some(tok) = Operator::from_str(next3).ok() {
                return Ok(Some((current, tok.into())));
            }
        }

        if let Some(next2) = self.source.get(self.pos..self.pos + 2) {
            if matches!(next2, "//") {
                let comment = self.scan_line_comment();
                return Ok(Some((current, Token::Comment(comment.trim().to_string()))));
            }

            if matches!(next2, "/*") {
                let comment = self.scan_general_comment()?;
                return Ok(Some((current, Token::Comment(comment))));
            }

            if let Some(tok) = Operator::from_str(next2).ok() {
                return Ok(Some((current, tok.into())));
            }
        }

        let ch = match self.source.get(self.pos..self.pos + 1) {
            None => return Ok(None),
            Some(next1) => match Operator::from_str(next1).ok() {
                Some(tok) => return Ok(Some((current, tok.into()))),
                None => next1.chars().nth(0).unwrap(),
            },
        };

        Ok(match ch {
            '"' | '`' => Some((
                current,
                Token::Literal(LitKind::String, self.scan_lit_string()?),
            )),
            '\'' => Some((
                current,
                Token::Literal(LitKind::Char, self.scan_lit_rune()?),
            )),
            ch if is_letter(ch) => {
                // see https://golang.org/ref/spec#Characters
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
        })
    }

    /// scan an identify
    /// caller must ensure that the first character is a unicode letter
    /// caller should check if identify is a keyword
    fn scan_identify(&mut self) -> String {
        self.source
            .chars()
            .skip(self.pos)
            .take_while(|&ch| is_letter(ch) || is_unicode_digit(ch))
            .collect()
    }

    fn scan_rune(&mut self, pos: usize) -> Result<String> {
        let mut chars = self.source.chars().skip(pos);
        let (next1, next2) = (chars.next(), chars.next());

        // must match a valid character
        let must_be = |ch: Option<char>, valid: fn(char) -> bool| match ch {
            Some(ch) if valid(ch) => Ok(ch),
            Some(_) => Err(self.error("illegal rune literal")),
            None => Err(self.error("literal not terminated")),
        };

        // take exactly N valid character
        let mut match_n = |n, valid| {
            (0..)
                .take(n)
                .map(|_| must_be(chars.next(), valid))
                .collect::<Result<Vec<char>>>()
        };

        // return normal character and error directly
        let es_sequence = match next1 {
            Some('\\') => match next2 {
                Some('x') => match_n(2, is_hex_digit)?,
                Some('u') => match_n(4, is_hex_digit)?,
                Some('U') => match_n(8, is_hex_digit)?,
                Some(ch) if is_octal_digit(ch) => match_n(2, is_octal_digit)?,
                Some(ch) if is_escaped_char(ch) => return Ok(format!("\\{}", ch)),
                Some(_) => return Err(self.error("unknown escape sequence")),
                None => return Err(self.error("literal not terminated")),
            },
            Some(ch) if is_unicode_char(ch) => return Ok(String::from(ch)),
            None => return Err(self.error_at(pos, "literal not terminated")),
            Some(_) => return Err(self.error_at(pos, "unexpected character")),
        };

        let es_sequence = [vec![next1.unwrap(), next2.unwrap()], es_sequence].concat();
        match es_sequence.get(1).unwrap() {
            'x' | 'u' | 'U' => Some((16, &es_sequence[2..])),
            _ => Some((8, &es_sequence[1..])), // here must be octal_digit
        }
        .and_then(|(radix, sequence)| {
            // a valid rust char must be a valid go rune
            // hence we do not check char ranges
            // see comment for `is_unicode_char`
            char::from_u32(
                u32::from_str_radix(&String::from_iter(sequence), radix)
                    .expect("here must be a valid u32"),
            )
        })
        .ok_or(self.error("invalid Unicode code point"))?;

        Ok(es_sequence.iter().collect())
    }

    fn scan_lit_rune(&mut self) -> Result<String> {
        let start_at = self.pos;
        assert_eq!(self.source.get(start_at..start_at + 1), Some("'"));
        let rune = self.scan_rune(start_at + 1)?;
        let next = start_at + 1 + rune.len();
        match self.source.get(next..next + 1) {
            Some("'") => Ok(format!("'{}'", rune)),
            Some(_) => Err(self.error_at(next, "rune literal expect termination")),
            None => Err(self.error_at(next, "rune literal not termination")),
        }
    }

    fn scan_lit_string(&mut self) -> Result<String> {
        let quote = self.source.chars().skip(self.pos).next().unwrap();
        let lit = match quote {
            '`' => self
                .source
                .chars()
                .skip(self.pos + 1)
                .take_while(|&ch| ch != '`' && (is_unicode_char(ch) || is_newline(ch)))
                .collect::<String>(),
            '"' => {
                let mut index = self.pos + 1;
                let mut lit = String::new();
                while self.source.chars().skip(index).next() != Some('"') {
                    let rune = self.scan_rune(index)?;
                    index += rune.chars().count();
                    lit = lit.add(rune.as_str());
                }
                lit
            }
            _ => unreachable!(),
        };

        let offset = self.pos + 1 + lit.chars().count();
        match self.source.chars().skip(offset).next() {
            Some(next) if next == quote => Ok(format!("{}{}{}", quote, lit, quote)),
            _ => Err(self.error_at(offset, "string literal not terminated")),
        }
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
    fn scan_general_comment(&mut self) -> Result<String> {
        assert_eq!("/*", &self.source[self.pos..self.pos + 2]);
        match self.source[self.pos..].find("*/") {
            None => Err(self.error("comment no termination '*/'")),
            Some(pos) => {
                let end = self.pos + pos + 2;
                let comments = self.source.get(self.pos..end).unwrap().to_string();
                for (index, ch) in comments.chars().enumerate() {
                    if ch == '\n' {
                        self.add_line(self.pos + index + 1)
                    }
                }

                Ok(comments)
            }
        }
    }
}

/// here are some difference from the golang specification of [Characters](https://golang.org/ref/spec#Characters)
/// go's `unicode_char` is an arbitrary Unicode code point except newline
/// but rust's char is a [unicode scalar value](https://www.unicode.org/glossary/#unicode_scalar_value)
fn is_unicode_char(c: char) -> bool {
    !is_newline(c)
}

fn is_newline(c: char) -> bool {
    c == '\u{000A}'
}

fn is_unicode_letter(c: char) -> bool {
    GeneralCategory::of(c).is_letter()
}

fn is_unicode_digit(c: char) -> bool {
    matches!(GeneralCategory::of(c), GeneralCategory::DecimalNumber)
}

fn is_letter(c: char) -> bool {
    is_unicode_letter(c) || c == '_'
}

fn is_octal_digit(c: char) -> bool {
    matches!(c, '0'..='7')
}

fn is_hex_digit(c: char) -> bool {
    c.is_ascii_hexdigit()
}

fn is_escaped_char(c: char) -> bool {
    ['a', 'b', 'f', 'n', 'r', 't', 'v', '\\', '\'', '"'].contains(&c)
}

#[cfg(test)]
mod test {
    use super::Scanner;

    #[test]
    fn scan_lit_rune() {
        let rune = |s| Scanner::new(s).scan_lit_rune();
        assert!(rune(r#"'a'"#).is_ok());
        assert!(rune(r#"'ä'"#).is_ok());
        assert!(rune(r#"'本'"#).is_ok());
        assert!(rune(r#"'\t'"#).is_ok());
        assert!(rune(r#"'\000'"#).is_ok());
        assert!(rune(r#"'\007'"#).is_ok());
        assert!(rune(r#"'\377'"#).is_ok());
        assert!(rune(r#"'\x07'"#).is_ok());
        assert!(rune(r#"'\xff'"#).is_ok());
        assert!(rune(r#"'\u12e4'"#).is_ok());
        assert!(rune(r#"'\U00101234'"#).is_ok());
        assert!(rune(r#"'\''"#).is_ok());

        assert!(rune(r#"'aa'"#).is_err());
        assert!(rune(r#"'\xa'"#).is_err());
        assert!(rune(r#"'\0'"#).is_err());
        assert!(rune(r#"'\uDFFF'"#).is_err());
        assert!(rune(r#"'\U00110000'"#).is_err());
    }

    #[test]
    fn scan_lit_string() {
        let lit_str = |s| Scanner::new(s).scan_lit_string();

        assert!(lit_str("`abc`").is_ok());
        assert!(lit_str("`\\n\n\\n`").is_ok());
        assert!(lit_str(r#""\n""#).is_ok());
        assert!(lit_str(r#""\"""#).is_ok());
        assert!(lit_str(r#""Hello, world!\n""#).is_ok());
        assert!(lit_str(r#""日本語""#).is_ok());
        assert!(lit_str(r#""\u65e5本\U00008a9e""#).is_ok());
        assert!(lit_str(r#""\xff\u00FF""#).is_ok());

        assert!(lit_str(r#""\uD800""#).is_err());
        assert!(lit_str(r#""\U00110000""#).is_err());
    }

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
        while let Some(_) = scanner.next_token().unwrap() {}
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
    fn get_line_info() {
        let mut scanner = Scanner::default();
        scanner.lines = vec![10, 20, 30];
        assert_eq!(scanner.line_info(5), (1, 5));
        assert_eq!(scanner.line_info(20), (2, 0));
        assert_eq!(scanner.line_info(50), (3, 20));
    }
}
