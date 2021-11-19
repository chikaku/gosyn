use crate::token::Operator;
use crate::token::Token;
use crate::{Keyword, LitKind};
use std::collections::VecDeque;
use std::fmt::{Debug, Formatter};
use std::str::FromStr;
use unic_ucd_category::GeneralCategory;

pub type Pos = usize;
pub type PosTok = (Pos, Token);

pub struct Error {
    pub pos: Pos,
    pub reason: &'static str,
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

    fn error(&self, reason: &'static str) -> Error {
        Error {
            reason,
            pos: self.pos,
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
                Token::Literal(LitKind::String, self.scan_lit_string()),
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

    fn scan_lit_rune(&mut self) -> Result<String> {
        let mut chars = self.source.chars().skip(self.pos);
        assert_eq!(chars.next(), Some('\''));
        let mut values = vec!['\''];

        let (next1, next2) = (chars.next(), chars.next());
        next1.is_some().then(|| values.push(next1.unwrap()));
        next2.is_some().then(|| values.push(next2.unwrap()));

        // must match a valid character or return error
        let must_be = |ch: Option<char>, valid: fn(char) -> bool| match ch {
            Some(ch) if valid(ch) => Ok(ch),
            Some(_) => Err(self.error("illegal rune literal")),
            None => Err(self.error("rune literal not terminated")),
        };

        // take exactly N valid chatacter
        let mut match_n = |n, valid| {
            (0..)
                .take(n)
                .map(|_| must_be(chars.next(), valid))
                .collect::<Result<Vec<char>>>()
        };

        match next1 {
            Some('\\') => {
                match next2 {
                    Some('x') => values.extend(match_n(2, is_hex_digit)?),
                    Some('u') => values.extend(match_n(4, is_hex_digit)?),
                    Some('U') => values.extend(match_n(8, is_hex_digit)?),
                    Some('a' | 'b' | 'f' | 'n' | 'r' | 't' | 'v' | '\\' | '\'' | '"') => {}
                    Some(ch) if is_octal_digit(ch) => values.extend(match_n(2, is_octal_digit)?),
                    Some(_) => return Err(self.error("unknown escape sequence")),
                    None => return Err(self.error("rune literal not terminated")),
                };
                // expect last `'` for escape sequence
                values.extend(match_n(1, |c| c == '\'')?)
            }
            // nexe2 has been pushed at the beginning
            // we will assert it in the end
            Some(ch) if is_unicode_char(ch) => {}
            elsech @ _ => must_be(elsech, |_| false).map(|_| ())?,
        }

        // check escape sequence for valid unicode code point
        if let Some(radix) = match values.get(1..3) {
            Some(['\\', 'x' | 'u' | 'U']) => Some(16),
            Some(['\\', n]) if is_octal_digit(*n) => Some(8),
            _ => None,
        } {
            // a valid rust char must be a valid go rune
            // hence we do not check char ranges
            // see comment for `is_unicode_char`
            char::from_u32(
                u32::from_str_radix(&String::from_iter(&values[3..values.len() - 1]), radix)
                    .expect("here must be a valid u32"),
            )
            .ok_or(self.error("invalid Unicode code point"))?;
        }

        must_be(values.last().map(|&c| c), |ch| ch == '\'')?;
        Ok(String::from_iter(values))
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
    fn scan_general_comment(&mut self) -> Result<String> {
        assert_eq!("/*", &self.source[self.pos..self.pos + 2]);
        match self.source[self.pos..].find("*/") {
            None => Err(Error {
                pos: self.pos,
                reason: "comment no termination '*/'",
            }),
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
    c != '\n'
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

    #[test]
    fn scan_lit_string() {
        let mut scanner = Scanner::new("\"123\"`2312\n123\"123`");
        assert_eq!(&scanner.scan_lit_string(), "\"123\"");
        scanner.pos += 5;
        assert_eq!(&scanner.scan_lit_string(), "`2312\n123\"123`");
    }
}
