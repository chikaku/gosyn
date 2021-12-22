use crate::token::Operator;
use crate::token::Token;
use crate::{Keyword, LitKind};
use std::collections::VecDeque;
use std::str::FromStr;

use unic_ucd_category::GeneralCategory;

pub type Pos = usize;
pub type PosTok = (Pos, Token);

#[derive(PartialEq, Debug)]
pub struct Error {
    pub pos: Pos,
    pub reason: String,
}

pub type Result<T> = core::result::Result<T, Error>;

#[derive(Default)]
pub struct Scanner {
    pub pos: usize,
    index: usize,
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

    fn next_char(&mut self, skp: usize) -> Option<char> {
        let source = &self.source[self.index..];
        source.chars().skip(skp).next().to_owned()
    }

    fn next_nchar(&mut self, n: usize) -> String {
        let source = &self.source[self.index..];
        source.chars().take(n).collect()
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
        while let Some(ch) = self.next_char(0) {
            if ch.is_whitespace() {
                if ch == '\n' {
                    self.add_line(self.pos + 1);
                    self.try_insert_semicolon(self.pos);
                    self.prev = Some(Operator::SemiColon.into());
                }

                skipped += 1;
                self.pos += 1;
                self.index += 1;
                continue;
            }

            break;
        }
        skipped
    }

    pub fn next_token(&mut self) -> Result<Option<PosTok>> {
        if let Some(pos_tok) = self.next.pop_back() {
            return Ok(Some(pos_tok));
        }

        self.skip_whitespace();
        if let Some(pos_tok) = self.next.pop_back() {
            return Ok(Some(pos_tok));
        }

        Ok(match self.index >= self.source.len() {
            true => None,
            false => {
                let current = self.pos;
                let tok = self.scan_token()?;
                self.add_token_cross_line(&tok);
                self.index += tok.len();
                self.pos += tok.char_count();
                self.prev = Some(tok.clone());
                Some((current, tok))
            }
        })
    }

    fn add_token_cross_line(&mut self, tok: &Token) {
        match tok {
            Token::Comment(text) | Token::Literal(.., text) => {
                for (index, ch) in text.chars().enumerate() {
                    if ch == '\n' {
                        self.add_line(self.pos + index + 1)
                    }
                }
            }
            _ => {}
        }
    }

    /// return next Token
    pub fn scan_token(&mut self) -> Result<Token> {
        if let Some(op) = Operator::from_str(&self.next_nchar(3)).ok() {
            return Ok(op.into());
        }

        if let Some(tok) = match self.next_nchar(2).as_str() {
            "//" => Some(Token::Comment(self.scan_line_comment())),
            "/*" => Some(Token::Comment(self.scan_general_comment()?)), // TODO: add line info
            two => Operator::from_str(two).ok().map(|op| op.into()),
        } {
            return Ok(tok);
        }

        // caller make sure here is at least one character
        let next0_char = self.next_char(0).unwrap();
        let next1_is_digits = matches!(self.next_char(1), Some('0'..='9'));
        let next0_char_op = Operator::from_str(&next0_char.to_string()).ok();

        Ok(match next0_char {
            c if is_decimal_digit(c) => self.scan_lit_number()?,
            '.' if next1_is_digits => self.scan_lit_number()?,
            '\'' => Token::Literal(LitKind::Char, self.scan_lit_rune()?),
            '"' | '`' => Token::Literal(LitKind::String, self.scan_lit_string()?),
            ch if is_letter(ch) => {
                let identifier = self.scan_identifier();
                match Keyword::from_str(&identifier) {
                    Ok(word) => Token::Keyword(word),
                    _ => Token::Literal(LitKind::Ident, identifier),
                }
            }
            other => match next0_char_op {
                Some(op) => op.into(),
                _ => return Err(self.error(format!("unresolved character {:?}", other))),
            },
        })
    }

    /// Scan line comment from `//` to `\n`
    fn scan_line_comment(&mut self) -> String {
        self.source[self.index..]
            .chars()
            .take_while(|&ch| ch != '\n')
            .collect()
    }

    /// Scan general comment from `/*` to `*/`
    fn scan_general_comment(&mut self) -> Result<String> {
        let source = &self.source[self.index..];
        assert_eq!(&source[0..2], "/*");

        let mut result = String::from("/*");
        let mut chars = source.chars().skip(2).peekable();
        while let Some(ch) = chars.next() {
            result.push(ch);
            if ch == '*' && chars.peek() == Some(&'/') {
                result.push('/');
                break;
            }
        }

        match result.ends_with("*/") {
            true => Ok(result),
            false => Err(self.error("comment no termination '*/'")),
        }
    }

    /// scan an identifier
    /// caller must ensure that the first character is a unicode letter
    /// caller should check if identify is a keyword
    fn scan_identifier(&mut self) -> String {
        self.source[self.index..]
            .chars()
            .take_while(|&ch| is_letter(ch) || is_unicode_digit(ch))
            .collect()
    }

    fn scan_rune(&mut self, index: usize) -> Result<String> {
        let source = &self.source[index..];
        let mut chars = source.chars();
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
            None => return Err(self.error_at(self.pos, "literal not terminated")),
            Some(_) => return Err(self.error_at(self.pos, "unexpected character")),
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
        let source = &self.source[self.index..];
        assert_eq!(&source[0..1], "'");
        let rune = self.scan_rune(self.index + 1)?;
        let index = self.index + 1 + rune.len();
        match self.source.get(index..index + 1) {
            Some("'") => Ok(format!("'{}'", rune)),
            Some(_) => Err(self.error_at(self.pos, "rune literal expect termination")),
            None => Err(self.error_at(self.pos, "rune literal not termination")),
        }
    }

    fn scan_lit_string(&mut self) -> Result<String> {
        let source = &self.source[self.index..];
        let mut chars = source.chars();

        let mut result = String::new();
        let quote = chars.next().unwrap();
        result.push(quote);

        if quote == '`' {
            while let Some(ch) = chars.next() {
                result.push(ch);
                if ch == quote {
                    break;
                }
            }
        } else {
            let quote = quote.to_string();
            let mut index = self.index + 1;
            while chars.next().is_some() {
                let rune = self.scan_rune(index)?;
                index += rune.len();
                result.push_str(&rune);
                chars = self.source[index..].chars();
                if rune == quote {
                    break;
                }
            }
        }

        let offset = self.pos + result.chars().count();
        match result.ends_with(quote) {
            true => Ok(result),
            _ => Err(self.error_at(offset, "string literal not terminated")),
        }
    }

    fn scan_digits(&mut self, n: usize, valid: fn(char) -> bool) -> String {
        self.source[self.index + n..]
            .chars()
            .scan(true, |state, item| {
                (item != '_' || *state).then(|| {
                    *state = item != '_';
                    item
                })
            })
            .take_while(|&ch| ch == '_' || valid(ch))
            .collect()
    }

    fn scan_lit_number(&mut self) -> Result<Token> {
        let chars = self.source[self.index..].chars();
        let next2 = chars.take(2).collect::<String>().to_owned();

        // integer part
        let (radix, int_part) = self
            .next_char(0)
            .and_then(|ch| match ch {
                '.' => None,
                _ => Some(match next2.as_str() {
                    "0b" | "oB" => (2, next2 + &self.scan_digits(2, is_binary_digit)),
                    "0o" | "0O" => (8, next2 + &self.scan_digits(2, is_decimal_digit)),
                    "0x" | "0X" => (16, next2 + &self.scan_digits(2, is_hex_digit)),
                    _ => (10, self.scan_digits(0, is_decimal_digit)),
                }),
            })
            .unwrap_or((10, String::new()));

        if int_part.ends_with("_") {
            return Err(self.error_at(
                self.pos + int_part.len(),
                "'_' must separate successive digits",
            ));
        }

        let skipped = int_part.len();
        let fac_part = (self.next_char(skipped) == Some('.'))
            .then(|| match radix {
                2 | 8 => Err(self.error_at(self.pos + skipped, "invalid radix point")),
                16 => Ok(".".to_owned() + &self.scan_digits(skipped + 1, is_hex_digit)),
                _ => Ok(".".to_owned() + &self.scan_digits(skipped + 1, is_decimal_digit)),
            })
            .unwrap_or(Ok(String::new()))?;

        if fac_part.starts_with("._") || fac_part.ends_with("_") {
            return Err(self.error_at(self.pos + skipped, "'_' must separate successive digits"));
        }

        let next1 = self.next_char(skipped);
        let skipped = int_part.len() + fac_part.len();
        if int_part.len() + fac_part.len() == 0 {
            return Err(self.error_at(self.pos + skipped, "invalid radix point"));
        } else if radix == 16 && (int_part.len() == 2) && (fac_part.len() == 1) {
            return Err(self.error_at(self.pos + skipped, "mantissa has no digits"));
        } else if matches!(next1, Some('e' | 'E')) && radix != 10 {
            return Err(self.error_at(self.pos + skipped, "E exponent requires decimal mantissa"));
        } else if matches!(next1, Some('p' | 'P')) && radix != 16 {
            return Err(self.error_at(
                self.pos + skipped,
                "P exponent requires hexadecimal mantissa",
            ));
        };

        let mut skipped = int_part.len() + fac_part.len();
        let exp_part = self
            .next_char(skipped)
            .and_then(|exp| {
                matches!(exp, 'e' | 'E' | 'p' | 'P').then(|| {
                    (match self.next_char(skipped + 1) {
                        Some(signed @ ('+' | '-')) => {
                            skipped += 2;
                            format!("{}{}", exp, signed)
                        }
                        _ => {
                            skipped += 1;
                            format!("{}", exp)
                        }
                    }) + &self.scan_digits(
                        skipped,
                        if radix == 16 {
                            is_hex_digit
                        } else {
                            is_decimal_digit
                        },
                    )
                })
            })
            .unwrap_or(String::new());

        if radix == 16 && fac_part.len() > 0 && exp_part.len() == 0 {
            return Err(self.error_at(
                self.pos + skipped + exp_part.len(),
                "mantissa has no digits",
            ));
        }

        if exp_part
            .chars()
            .skip(1) // skip e|E|p|P
            .skip_while(|&ch| ch == '+' || ch == '-')
            .next()
            == Some('_')
            || exp_part.ends_with("_")
        {
            return Err(self.error_at(
                self.pos + skipped + exp_part.len(),
                "'_' must separate successive digits",
            ));
        }

        skipped += exp_part.len();
        let num_part = [int_part, fac_part, exp_part].concat();
        if self.next_char(skipped) == Some('i') {
            Ok(Token::Literal(LitKind::Imag, num_part + "i"))
        } else if num_part.find('.').is_some() {
            Ok(Token::Literal(LitKind::Float, num_part))
        } else {
            Ok(Token::Literal(LitKind::Integer, num_part))
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

fn is_binary_digit(c: char) -> bool {
    matches!(c, '0'..='1')
}

fn is_octal_digit(c: char) -> bool {
    matches!(c, '0'..='7')
}

fn is_decimal_digit(c: char) -> bool {
    matches!(c, '0'..='9')
}

fn is_hex_digit(c: char) -> bool {
    matches!(c, '0'..='9' | 'a'..='f' | 'A'..='F')
}

fn is_escaped_char(c: char) -> bool {
    ['a', 'b', 'f', 'n', 'r', 't', 'v', '\\', '\'', '"'].contains(&c)
}

#[cfg(test)]
mod tests {
    use super::Scanner;
    use crate::{token::Token, Operator};

    #[test]
    fn insert_semicolon() {
        let mut scan = Scanner::new("return//\nreturn");
        scan.next_token().unwrap();
        let next = scan.next_token().unwrap();
        assert_eq!(next.unwrap().1, Token::Operator(Operator::SemiColon));
    }

    #[test]
    fn scan_text() {
        let mut scan = Scanner::new("'一', '二', '三'");
        assert!(scan.next_token().is_ok());
        assert!(scan.next_token().is_ok());
        assert!(scan.next_token().is_ok());
        assert!(scan.next_token().is_ok());
        assert!(scan.next_token().is_ok());

        let mut scan = Scanner::new("n%9");
        assert!(scan.next_token().is_ok());
        assert!(scan.next_token().is_ok());
        assert!(scan.next_token().is_ok());
    }

    #[test]
    fn scan_lit_number() {
        let numeric = |s| Scanner::new(s).scan_lit_number();
        assert!(numeric("1").is_ok());
        assert!(numeric("42").is_ok());
        assert!(numeric("4_2").is_ok());
        assert!(numeric("0600").is_ok());
        assert!(numeric("0_600").is_ok());
        assert!(numeric("0o600").is_ok());
        assert!(numeric("0O600").is_ok());
        assert!(numeric("0xBadFace").is_ok());
        assert!(numeric("0xBad_Face").is_ok());
        assert!(numeric("0x_67_7a_2f_cc_40_c6").is_ok());
        assert!(numeric("170141183460469231731687303715884105727").is_ok());
        assert!(numeric("170_141183_460469_231731_687303_715884_105727").is_ok());

        assert!(numeric("42_").is_err());
        assert!(numeric("4__2").is_err());
        assert!(numeric("0_xBadFace").is_err());

        assert!(numeric("0.").is_ok());
        assert!(numeric("1E6").is_ok());
        assert!(numeric(".25").is_ok());
        assert!(numeric("1_5.").is_ok());
        assert!(numeric("72.40").is_ok());
        assert!(numeric("1.e+0").is_ok());
        assert!(numeric("072.40").is_ok());
        assert!(numeric("2.71828").is_ok());
        assert!(numeric(".12345E+5").is_ok());
        assert!(numeric("0.15e+0_2").is_ok());
        assert!(numeric("6.67428e-11").is_ok());

        assert!(numeric("0x1p-2").is_ok());
        assert!(numeric("0x2.p10").is_ok());
        assert!(numeric("0X.8p-0").is_ok());
        assert!(numeric("0x15e-2").is_ok());
        assert!(numeric("0x1.Fp+0").is_ok());
        assert!(numeric("0X_1FFFP-16").is_ok());

        assert!(numeric("1p-2").is_err());
        assert!(numeric("1_.5").is_err());
        assert!(numeric("1._5").is_err());
        assert!(numeric("0x.p1").is_err());
        assert!(numeric("1.5_e1").is_err());
        assert!(numeric("1.5e_1").is_err());
        assert!(numeric("1.5e1_").is_err());
        assert!(numeric("1.5e+_1").is_err());
        assert!(numeric("0x1.5e-2").is_err());

        assert!(numeric("0i").is_ok());
        assert!(numeric("0.i").is_ok());
        assert!(numeric("1E6i").is_ok());
        assert!(numeric(".25i").is_ok());
        assert!(numeric("0123i").is_ok());
        assert!(numeric("0o123i").is_ok());
        assert!(numeric("0xabci").is_ok());
        assert!(numeric("1.e+0i").is_ok());
        assert!(numeric("2.71828i").is_ok());
        assert!(numeric("0x1p-2i ").is_ok());
        assert!(numeric(".12345E+5i").is_ok());
        assert!(numeric("6.67428e-11i").is_ok());
    }

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
        assert!(lit_str(r#""\n""#).is_ok());
        assert!(lit_str(r#""\"""#).is_ok());
        assert!(lit_str(r#""日本語""#).is_ok());
        assert!(lit_str("`\\n\n\\n`").is_ok());
        assert!(lit_str(r#""\xff\u00FF""#).is_ok());
        assert!(lit_str(r#""Hello, world!\n""#).is_ok());
        assert!(lit_str(r#""\u65e5本\U00008a9e""#).is_ok());

        assert!(lit_str(r#""\uD800""#).is_err());
        assert!(lit_str(r#""\U00110000""#).is_err());
    }

    #[test]
    fn scan_comment() {
        let mut comments = Scanner::new("// 注释\r\n//123\n/*注释*/");

        let next = comments.next_token().map(|x| x.map(|(_, tok)| tok));
        assert_eq!(next, Ok(Some(Token::Comment(String::from("// 注释\r")))));
        let next = comments.next_token().map(|x| x.map(|(_, tok)| tok));
        assert_eq!(next, Ok(Some(Token::Comment(String::from("//123")))));
        let next = comments.next_token().map(|x| x.map(|(_, tok)| tok));
        assert_eq!(next, Ok(Some(Token::Comment(String::from("/*注释*/")))));
    }

    #[test]
    fn scan_line_info() {
        let code = "package main 代码 \n/*😃\n注释*/\n\n//🎃\n\n";
        let mut scanner = Scanner::new(code);
        while let Ok(Some(_)) = scanner.next_token() {}
        let mut lines = scanner.lines.iter();
        assert_eq!(lines.next(), Some(&17));
        assert_eq!(lines.next(), Some(&21));
        assert_eq!(lines.next(), Some(&26));
        assert_eq!(lines.next(), Some(&27));
        assert_eq!(lines.next(), Some(&31));
        assert_eq!(lines.next(), Some(&32));
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
