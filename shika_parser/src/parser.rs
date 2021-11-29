use crate::ast;
use crate::ast::{BasicLit, Expression, Ident};
use crate::ast::{ChanMode, VarSpec};
use crate::scanner::{PosTok, Scanner};
use crate::token;
use crate::token::IntoKind;
use crate::token::{Keyword, LitKind, Operator, Token};
use crate::Error;
use crate::Result;
use crate::{Pos, TokenKind};
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::rc::Rc;

#[derive(Default)]
pub struct Parser {
    path: PathBuf,
    scan: Scanner,

    current: Option<PosTok>,
    comments: Vec<Rc<ast::Comment>>,
    lead_comments: Vec<Rc<ast::Comment>>,
}

impl Parser {
    pub fn from_str<S: AsRef<str>>(s: S) -> Self {
        let mut parser = Self::default();
        parser.path = PathBuf::from("<input>");
        parser.scan = Scanner::new(s);
        parser.next().expect("unpexected new Parser error");

        parser
    }

    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let mut source = String::new();
        File::open(path.as_ref())?.read_to_string(&mut source)?;

        let mut parser = Parser::default();
        parser.path = PathBuf::from(path.as_ref());
        parser.scan = Scanner::new(source);
        parser.next()?;

        Ok(parser)
    }
}

impl Parser {
    fn unexpected<K: IntoKind>(&self, expect: Vec<K>, actual: Option<PosTok>) -> Error {
        let (pos, actual) = actual
            .map(|(pos, tok)| (pos, Some(tok)))
            .unwrap_or((self.scan.position(), None));

        let expect = expect.iter().map(|&x| x.into()).collect();
        Error::UnexpectedToken {
            expect,
            actual,
            path: self.path.clone(),
            location: self.scan.line_info(pos),
        }
    }

    fn else_error_at<S: AsRef<str>>(&self, pos: Pos, reason: S) -> Error {
        Error::Else {
            path: self.path.clone(),
            location: self.scan.line_info(pos),
            reason: reason.as_ref().to_string(),
        }
    }

    fn else_error<S: AsRef<str>>(&self, reason: S) -> Error {
        self.else_error_at(self.scan.position(), reason)
    }

    fn expect<K: IntoKind>(&mut self, expect: K) -> Result<()> {
        if let Some((_, tok)) = &self.current {
            if tok.kind() == expect.into() {
                self.next()?;
                return Ok(());
            }
        }

        Err(self.unexpected(vec![expect.into()], self.current.to_owned()))
    }

    fn current_is<K: IntoKind>(&self, expect: K) -> bool {
        match &self.current {
            Some((_, tok)) => tok.kind() == expect.into(),
            _ => false,
        }
    }

    fn get_current(&self) -> Result<PosTok> {
        self.current
            .to_owned()
            .ok_or(self.else_error("unexpecred EOF"))
    }

    /// skip while current equal to expect
    fn skipped<K: IntoKind>(&mut self, expect: K) -> Result<bool> {
        self.current_is(expect)
            .then(|| self.next().map(|_| true))
            .unwrap_or(Ok(false))
    }

    fn expect_none_or<K: IntoKind>(&mut self, expect: K) -> Result<bool> {
        match self.current.to_owned() {
            None => Ok(true),
            Some((_, actual)) if actual.kind() == expect.into() => {
                self.next()?;
                Ok(false)
            }
            other @ _ => Err(self.unexpected(vec![expect.into()], other)),
        }
    }

    /// parse current token as an ident
    fn parse_ident(&mut self) -> Result<ast::Ident> {
        match self.current.to_owned() {
            Some((pos, Token::Literal(LitKind::Ident, name))) => {
                self.next()?;
                Ok(ast::Ident { pos, name })
            }
            other @ _ => Err(self.unexpected(vec![LitKind::Ident], other)),
        }
    }

    /// parse current token as package name
    /// which is an ident but can not be '_'
    fn parse_pkg_name(&mut self) -> Result<ast::Ident> {
        let ast::Ident { pos, name } = self.parse_ident()?;
        (name != "_")
            .then_some(ast::Ident { pos, name })
            .ok_or(self.else_error_at(pos, "package name can't be blank"))
    }

    /// expect next to be a string literal and go to next
    fn expect_string_literal(&mut self) -> Result<ast::StringLit> {
        match self.next_owned()? {
            Some((pos, Token::Literal(LitKind::String, value))) => {
                self.next()?;
                Ok(ast::StringLit { pos, value })
            }
            other @ _ => Err(self.unexpected(vec![LitKind::String], other)),
        }
    }

    fn parse_ident_list(&mut self) -> Result<Vec<ast::Ident>> {
        let mut result = vec![self.parse_ident()?];
        while self.current_is(Operator::Comma) {
            self.next()?;
            result.push(self.parse_ident()?);
        }

        Ok(result)
    }

    fn scan_next(&mut self) -> Result<Option<PosTok>> {
        self.scan
            .next_token()
            .map_err(|serr| self.else_error_at(serr.pos, serr.reason))
    }

    fn next(&mut self) -> Result<Option<&PosTok>> {
        let mut pos_tok = self.scan_next()?;
        while let Some((pos, Token::Comment(text))) = pos_tok {
            let comment = Rc::new(ast::Comment { pos, text });
            self.comments.push(comment.clone());
            self.lead_comments.push(comment.clone());
            if self.scan.skip_whitespace() > 0 {
                self.lead_comments.clear();
            }

            pos_tok = self.scan_next()?;
        }

        self.current = pos_tok;
        Ok(self.current.as_ref())
    }

    fn next_owned(&mut self) -> Result<Option<PosTok>> {
        Ok(match self.next()? {
            None => None,
            Some(pk) => Some(pk.to_owned()),
        })
    }

    pub fn parse_package(&mut self) -> Result<ast::Ident> {
        self.expect(Keyword::Package)?;
        self.parse_pkg_name()
    }

    pub fn parse_file(&mut self) -> Result<ast::File> {
        let mut file = ast::File::default();
        file.path = self.path.clone();

        file.name = self.parse_package()?;
        file.document.append(&mut self.lead_comments);
        self.expect_none_or(Operator::SemiColon)?;

        // match Import declaration
        file.imports.extend(self.parse_imports()?);

        loop {
            self.skipped(Operator::SemiColon)?;
            let (_, tok) = self.get_current()?;
            match tok {
                token::VAR => {
                    self.parse_var()?;
                }
                _ => unimplemented!(),
            }
        }
    }

    pub fn parse_imports(&mut self) -> Result<Vec<ast::Import>> {
        let mut imports = vec![];
        while self.current_is(Keyword::Import) {
            self.next()?;
            match self.current_is(Operator::ParenLeft) {
                true => imports.extend(self.parse_import_group()?),
                false => imports.push(self.parse_import_sepc()?),
            }
            self.skipped(Operator::SemiColon)?;
        }

        Ok(imports)
    }

    /// parse import group like
    /// ```go
    /// import (
    ///     net "x/net"
    ///     sys "x/sys"
    /// )
    /// ```
    fn parse_import_group(&mut self) -> Result<Vec<ast::Import>> {
        // come here only because we met a ( so need go next
        // current must be ParenLeft
        self.next()?;
        let mut imports = vec![];
        while !self.current_is(Operator::ParenRight) {
            imports.push(self.parse_import_sepc()?);
            self.skipped(Operator::SemiColon)?;
        }

        Ok(imports)
    }

    fn parse_import_sepc(&mut self) -> Result<ast::Import> {
        let mut docs = Vec::new();
        docs.append(&mut self.lead_comments);

        let exp_list: Vec<TokenKind> = vec![
            Operator::Period.into(),
            LitKind::Ident.into(),
            LitKind::String.into(),
        ];

        let (name, path) = match self.current.to_owned() {
            Some((pos, Token::Literal(LitKind::Ident, name))) => (
                Some(ast::Ident { pos, name }),
                self.expect_string_literal()?.into(),
            ),
            Some((pos, Token::Operator(Operator::Period))) => {
                let name = String::from(".");
                (
                    Some(ast::Ident { pos, name }),
                    self.expect_string_literal()?.into(),
                )
            }
            Some((pos, Token::Literal(LitKind::String, value))) => {
                self.next()?;
                (None, ast::StringLit { pos, value })
            }
            other @ _ => return Err(self.unexpected(exp_list, other)),
        };

        Ok(ast::Import { docs, name, path })
    }

    fn parse_var(&mut self) -> Result<Vec<VarSpec>> {
        let mut vars = vec![];
        if self.skipped(Keyword::Var)? {
            if self.skipped(Operator::ParenLeft)? {
                while !self.current_is(Operator::ParenRight) {
                    vars.push(self.parse_var_spec()?);
                    self.skipped(Operator::SemiColon)?;
                }
                return Ok(vars);
            }

            vars.push(self.parse_var_spec()?);
            self.skipped(Operator::SemiColon)?;
        }

        Ok(vars)
    }

    fn parse_var_spec(&mut self) -> Result<ast::VarSpec> {
        let mut spec = ast::VarSpec::default();
        spec.name = self.parse_ident_list()?;
        if !self.skipped(Operator::Assign)? {
            spec.typ = Some(self.parse_type()?);
        }

        if self.skipped(Operator::Assign)? {
            // TODO: expect ExpressionList
        }

        // TODO: should expect something ?
        Ok(spec)
    }

    pub fn parse_type(&mut self) -> Result<ast::Type> {
        let (pos, tok) = self.get_current()?;
        match tok {
            Token::Literal(LitKind::Ident, name) => match name.as_str() {
                "_" => Err(self.else_error_at(pos, "type name can not be blank")),
                _ => {
                    self.next()?;
                    let id0 = ast::Ident { pos, name };
                    Ok(if self.skipped(Operator::Period)? {
                        ast::Type::PkgNamed(id0, self.parse_ident()?)
                    } else {
                        ast::Type::Named(id0.into())
                    })
                }
            },
            token::LPAREN => {
                self.next()?;
                let typ = self.parse_type()?;
                self.expect(Operator::ParenRight)?;
                return Ok(typ);
            }
            token::LBARACK => {
                self.next()?;
                if self.skipped(Operator::BarackRight)? {
                    let elem_type = self.parse_type()?;
                    return Ok(ast::Type::Slice(Box::new(elem_type)));
                }

                // Array Type
                // TODO: expect Expression
                unimplemented!()
            }
            token::MAP => {
                self.next()?;
                self.expect(Operator::BarackLeft)?;
                let key_type = Box::new(self.parse_type()?);
                self.expect(Operator::BarackRight)?;
                let val_type = Box::new(self.parse_type()?);
                Ok(ast::Type::Map(key_type, val_type))
            }
            token::CHAN => {
                self.next()?;
                let ch_mode = match self.skipped(Operator::Arrow)? {
                    true => ChanMode::Send,
                    false => ChanMode::Double,
                };

                let ch_type = Box::new(self.parse_type()?);
                Ok(ast::Type::Channel(ch_mode, ch_type))
            }
            token::ARROW => {
                self.next()?;
                Ok(ast::Type::Channel(
                    ChanMode::Receive,
                    Box::new(self.parse_type()?),
                ))
            }
            token::STAR => Ok(ast::Type::Pointer(Box::new(self.parse_type()?))),
            t @ _ => {
                Err(self.else_error_at(pos, format!("expect a type representation found {:?}", t)))
            }
        }
    }

    pub fn parse_expr(&mut self) -> Result<ast::Expression> {
        self.parse_binary_expr()
    }

    fn parse_binary_expr(&mut self) -> Result<ast::Expression> {
        self.parse_unary_expr()
    }

    fn parse_unary_expr(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current()?;
        match tok {
            Token::Operator(
                op
                @ (Operator::Add | Operator::Sub | Operator::Not | Operator::Xor | Operator::And),
            ) => Ok(ast::Expression::Unary {
                pos,
                operator: op,
                operand: Box::new(self.parse_unary_expr()?),
            }),
            token::ARROW => {
                // TODO: handle <- chan int(nil)
                unimplemented!()
            }
            token::STAR => Ok(Expression::Star {
                pos,
                right: Box::new(self.parse_unary_expr()?),
            }),
            _ => self.parse_primary_expr(),
        }
    }

    fn parse_primary_expr(&mut self) -> Result<ast::Expression> {
        let operand = self.parse_operand()?;
        match self.next()? {
            Some((_, token::PERIOD)) => match self.next_owned()? {
                // TODO: check type or expr
                Some((pos, Token::Literal(LitKind::Ident, name))) => Ok(Expression::Selector {
                    left: Box::new(operand),
                    right: ast::Ident { pos, name },
                }),
                // TODO: check type
                Some((_, token::LPAREN)) => {
                    self.next()?;
                    let typ = (!self.current_is(Keyword::Type)).then_some(self.parse_type()?);
                    self.expect(Operator::ParenRight)?;
                    Ok(Expression::TypeAssert {
                        left: Box::new(operand),
                        assert: Box::new(typ),
                    })
                }
                _ => Err(self.else_error("expect selector or type assertion")),
            },
            // Some((_, BARACK_LEFT)) => {}
            // Some((_, PAREN_LEFT)) => {}
            // Some((_, BRACE_LEFT)) => {}
            _ => unimplemented!(),
        }
    }

    fn parse_operand(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current()?;
        Ok(match tok {
            Token::Literal(LitKind::Ident, name) => Expression::Ident(Ident { pos, name }),
            Token::Literal(kind, value) => Expression::BasicLit(BasicLit { pos, kind, value }),
            token::LPAREN => {
                self.next()?;
                let expr = self.parse_expr()?;
                self.expect(Operator::ParenRight)?;
                Expression::Paren {
                    pos: (pos, self.scan.position() - 1),
                    expr: Box::new(expr),
                }
            }
            token::FUNC => Expression::Function {
                pos,
                func: Box::new(self.parse_func_lit()?),
            },
            _ => Expression::Type {
                pos,
                // TODO: this is a type
                // treat type as an expression?
                typ: Box::new(self.parse_type()?),
            },
        })
    }

    /// function literal is an anonymous function
    fn parse_func_lit(&mut self) -> Result<ast::Function> {
        self.expect(Keyword::Func)?;
        let (input, output) = self.parse_func_signature()?;
        self.current_is(Operator::BraceLeft)
            .then(|| self.parse_func_body());

        Ok(ast::Function {
            input,
            output,
            name: None,
        })
    }

    fn parse_func_body(&self) {
        unimplemented!()
    }

    fn parse_func_signature(&mut self) -> Result<(Vec<ast::Params>, Vec<ast::Params>)> {
        let input = self.parse_params_list()?;
        let output = match self.current {
            Some((_, Token::Operator(Operator::ParenLeft))) => self.parse_params_list()?,
            None | Some((_, Token::Operator(Operator::SemiColon))) => vec![ast::Params {
                name: None,
                typ: (Box::new(self.parse_type()?), false),
            }],
            _ => vec![],
        };

        Ok((input, output))
    }

    /// parse params list like  
    /// `(a, b int, c bool, d int...)`
    fn parse_params_list(&mut self) -> Result<Vec<ast::Params>> {
        let mut params = vec![];
        self.expect(Operator::ParenLeft)?;
        while !self.current_is(Operator::ParenRight) {
            params.extend(self.parse_param_decl()?);
            self.skipped(Operator::Comma)?;
        }

        for (index, param) in params.iter().enumerate() {
            if param.typ.1 && index != params.len() - 1 {
                // TODO: locate the type position
                return Err(self.else_error("can only use ... with final parameter in list"));
            }
        }

        Ok(params)
    }

    fn parse_param_decl(&mut self) -> Result<Vec<ast::Params>> {
        let (pos, tok) = self.get_current()?;
        match tok {
            Token::Literal(LitKind::Ident, name) => {
                self.next()?;
                let mut ident_list = vec![];
                ident_list.push(ast::Ident { pos, name });
                loop {
                    match self.get_current()? {
                        // T, pkg.?
                        (_, Token::Operator(Operator::Period)) => {
                            let id = self.parse_ident()?;
                            let pkg = ident_list.pop().unwrap();
                            let mut typ_list = ident_list
                                .into_iter()
                                .map(|id| ast::Params {
                                    name: None,
                                    typ: (Box::new(ast::Type::Named(id)), false),
                                })
                                .collect::<Vec<_>>();
                            typ_list.push(ast::Params {
                                name: None,
                                typ: (Box::new(ast::Type::PkgNamed(pkg, id)), false),
                            });
                            return Ok(typ_list);
                        }
                        // a, b, ?
                        (_, Token::Operator(Operator::Comma)) => {
                            self.next()?;
                            // T1, T2, ...T3
                            if self.skipped(Operator::Ellipsis)? {
                                let mut typ_list = ident_list
                                    .into_iter()
                                    .map(|id| ast::Params {
                                        name: None,
                                        typ: (Box::new(ast::Type::Named(id)), false),
                                    })
                                    .collect::<Vec<_>>();
                                typ_list.push(ast::Params {
                                    name: None,
                                    typ: (Box::new(self.parse_type()?), true),
                                });
                                return Ok(typ_list);
                            }

                            // a, b, c
                            ident_list.push(self.parse_ident()?);
                        }
                        // a, b ...?
                        (_, Token::Operator(Operator::Ellipsis)) => {
                            self.next()?;
                            return Ok(vec![ast::Params {
                                name: ident_list.pop(),
                                typ: (Box::new(self.parse_type()?), true),
                            }]);
                        }
                        // a, b)
                        (_, Token::Operator(Operator::ParenRight)) => {
                            return Ok(ident_list
                                .into_iter()
                                .map(|id| ast::Params {
                                    name: None,
                                    typ: (Box::new(ast::Type::Named(id)), false),
                                })
                                .collect::<Vec<_>>())
                        }
                        // a, b func... | a, b struct...
                        _ => {
                            let typ = Box::new(self.parse_type()?);
                            return Ok(ident_list
                                .into_iter()
                                .map(|id| ast::Params {
                                    name: Some(id),
                                    typ: (typ.clone(), false),
                                })
                                .collect());
                        }
                    }
                }
            }
            // (...T)
            Token::Operator(Operator::Ellipsis) => Ok(vec![ast::Params {
                name: None,
                typ: (Box::new(self.parse_type()?), true),
            }]),
            // ()
            Token::Operator(Operator::ParenRight) => Ok(vec![]),
            _ => Ok(vec![ast::Params {
                name: None,
                typ: (Box::new(self.parse_type()?), false),
            }]),
        }
    }
}

#[cfg(test)]
mod test {
    use std::assert_matches::assert_matches;

    use crate::ast::{ChanMode, Type};
    use crate::parser::Parser;

    #[test]
    fn parse_func_lit() {
        let func = |s| Parser::from_str(s).parse_func_lit();

        assert!(func("func()").is_ok());
        assert!(func("func(x int) int").is_ok());
        assert!(func("func(a, _ int, z float32) bool").is_ok());
        assert!(func("func(a, b int, z float32) (bool)").is_ok());
        assert!(func("func(prefix string, values ...int)").is_ok());
        assert!(func("func(int, int, float64) (float64, *[]int)").is_ok());
        assert!(func("func(n int) func(p *T)").is_ok());
    }

    #[test]
    fn parse_param_list() {
        let params = |s| Parser::from_str(s).parse_params_list();

        assert!(params("()").is_ok());
        assert!(params("(bool)").is_ok());
        assert!(params("(a bool)").is_ok());
        assert!(params("(a ...bool)").is_ok());
        assert!(params("(a, b, c bool)").is_ok());
        assert!(params("(int, int, bool)").is_ok());
        assert!(params("(a, b int, c bool)").is_ok());
        assert!(params("(int, bool, ...int)").is_ok());
        assert!(params("(a, _ int, z float32)").is_ok());
        assert!(params("(a, b int, z float32)").is_ok());
        assert!(params("(prefix string, values ...int)").is_ok());
        assert!(params("(a, b int, z float64, opt ...T)").is_ok());

        assert!(params("(,)").is_err());
        assert!(params("(...)").is_err());
        assert!(params("(a, ...)").is_err());
        assert!(params("(...int, bool)").is_err());
        assert!(params("(...int, ...bool)").is_err());
    }

    const VAR_CODE: &'static str = r#"
    var x1 int
    var x2, x3 int
    var x4 = 1
    var x5, x6 = 1, 2
    var x7 int = 1
    var x8, x9 int = 1, 2
    
    var (
        x10      int
        x11, x12 int = 3, 4;
        x15, x16     = 7, 8;
    )
    
    var (x17 int = 9; x18 int = 10);
    var (x19=11;x20 int=12;);
    "#;

    #[test]
    fn parse_var() {
        let vars = |s| Parser::from_str(s).parse_var();

        assert!(vars(VAR_CODE).is_ok());
    }

    #[test]
    fn parse_type() {
        let type_of = |x| Parser::from_str(x).parse_type().ok();

        assert_matches!(type_of("int"), Some(Type::Named(_)));
        assert_matches!(type_of("int"), Some(Type::Named(_)));
        assert_matches!(type_of("((int))"), Some(Type::Named(_)));
        assert_matches!(type_of("a.b;"), Some(Type::PkgNamed(..)));
        assert_matches!(type_of("[]int;"), Some(Type::Slice(..)));
        assert_matches!(type_of("map[int]map[int]int;"), Some(Type::Map(..)));

        assert_matches!(
            type_of("chan int;"),
            Some(Type::Channel(ChanMode::Double, ..))
        );

        assert_matches!(
            type_of("<-chan <- chan int;"),
            Some(Type::Channel(ChanMode::Receive, ..))
        );
    }

    #[test]
    fn parse_imports() {
        let imps = |s: &str| Parser::from_str(s).parse_imports();

        assert!(imps("import ()").is_ok());
        assert!(imps("import `aa`").is_ok());
        assert!(imps("import (\n\n)").is_ok());
        assert!(imps(r#"import "liba""#).is_ok());
        assert!(imps(r#"import . "libb""#).is_ok());
        assert!(imps(r#"import _ "libc""#).is_ok());
        assert!(imps(r#"import d "libd""#).is_ok());
        assert!(imps("import (\"a\"\n. \"b\"\n_ \"c\"\nd \"d\")").is_ok());

        assert!(imps("import _").is_err());
        assert!(imps("import _ _").is_err());
        assert!(imps("import . ()").is_err());
    }

    #[test]
    fn parse_package() {
        let pkg = |s| Parser::from_str(s).parse_package();

        assert!(pkg("package main").is_ok());
        assert!(pkg("package\n\nmain").is_ok());

        assert!(pkg("\n\n").is_err());
        assert!(pkg("package _").is_err());
        assert!(pkg("package\n_").is_err());
        assert!(pkg("package package").is_err());
    }
}
