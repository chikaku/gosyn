use crate::ast;
use crate::ast::{BasicLit, ChanMode, ChannelType, Spec};
use crate::scanner::Scanner;
use crate::token;
use crate::token::{IntoKind, Keyword, LitKind, Operator, Token, TokenKind};
use crate::Error;
use crate::Pos;
use crate::PosTok;
use crate::Result;

use std::borrow::Borrow;
use std::fs;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::vec;

#[derive(Default)]
pub struct Parser {
    path: PathBuf,
    scan: Scanner,
    comments: Vec<Rc<ast::Comment>>, // all comments

    expr_level: i32,
    lead_comments: Vec<Rc<ast::Comment>>,
    current: Option<PosTok>,
}

impl Parser {
    /// parse input source to `ast::File`, path will be \<input\>
    pub fn from<S: AsRef<str>>(s: S) -> Self {
        let mut parser = Parser {
            scan: Scanner::new(s),
            path: PathBuf::from("<input>"),
            ..Default::default()
        };

        parser.next().expect("unexpected new Parser error");
        parser
    }

    /// read file content and parse to `ast::File`
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let source = fs::read_to_string(path.as_ref())?;
        let mut parser = Parser {
            scan: Scanner::new(source),
            path: path.as_ref().into(),
            ..Default::default()
        };

        parser.next()?;
        Ok(parser)
    }
}

impl Parser {
    fn unexpected<K: IntoKind>(&self, expect: &[K], actual: Option<PosTok>) -> Error {
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

    fn expect<K: IntoKind>(&mut self, expect: K) -> Result<usize> {
        if let Some((pos, tok)) = self.current.as_ref() {
            if tok.is(expect) {
                let pos = *pos;
                self.next()?;
                return Ok(pos);
            }
        }

        let current = self.current.take();
        Err(self.unexpected(&[expect.into()], current))
    }

    /// skip while current equal to expect
    fn skipped<K: IntoKind>(&mut self, expect: K) -> Result<bool> {
        if let Some((_, tok)) = &self.current {
            if tok.is(expect) {
                self.next()?;
                return Ok(true);
            }
        }

        Ok(false)
    }

    fn current_is<K: IntoKind>(&self, expect: K) -> bool {
        match &self.current {
            Some((_, tok)) => tok.is(expect),
            None => false,
        }
    }

    fn current_not<K: IntoKind>(&self, expect: K) -> bool {
        !self.current_is(expect)
    }

    fn current_kind(&self) -> TokenKind {
        self.current
            .as_ref()
            .map(|(_, tok)| tok.kind())
            .expect("unexpected EOF")
    }

    fn current_pos(&self) -> usize {
        self.current
            .as_ref()
            .map(|(pos, _)| *pos)
            .unwrap_or_else(|| self.scan.position())
    }

    fn preback(&self) -> ((usize, usize), Option<PosTok>) {
        (self.scan.preback(), self.current.clone())
    }

    fn goback(&mut self, pre: ((usize, usize), Option<PosTok>)) {
        self.scan.goback(pre.0);
        self.current = pre.1;
    }

    fn get_current(&self) -> (usize, &Token) {
        self.current
            .as_ref()
            .map(|(pos, tok)| (*pos, tok))
            .expect("unexpected EOF")
    }

    fn scan_next(&mut self) -> Result<Option<PosTok>> {
        self.scan
            .next_token()
            .map_err(|e| self.else_error_at(e.pos, e.reason))
    }

    fn next(&mut self) -> Result<Option<&PosTok>> {
        let mut line = 0;
        let mut pos_tok = self.scan_next()?;
        while let Some((pos, Token::Comment(text))) = pos_tok {
            if self.scan.line_info(pos).0 > line + 1 {
                self.lead_comments.clear();
            }

            let ended = self.scan.position();
            line = self.scan.line_info(ended).0;
            let comment = Rc::new(ast::Comment { pos, text });
            self.comments.push(comment.clone());
            self.lead_comments.push(comment.clone());
            pos_tok = self.scan_next()?;
        }

        self.current = pos_tok;
        Ok(self.current.as_ref())
    }

    fn drain_comments(&mut self) -> Vec<Rc<ast::Comment>> {
        self.lead_comments.drain(0..).collect()
    }
}

impl Parser {
    fn parse_ident(&mut self) -> Result<ast::Ident> {
        let current = self.current.take();
        if let Some((pos, Token::Literal(LitKind::Ident, name))) = current {
            self.next()?;
            return Ok(ast::Ident { pos, name });
        }

        Err(self.unexpected(&[LitKind::Ident], current))
    }

    fn parse_ident_list(&mut self) -> Result<Vec<ast::Ident>> {
        let mut result = vec![self.parse_ident()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.parse_ident()?);
        }

        Ok(result)
    }

    fn parse_string_literal(&mut self) -> Result<ast::StringLit> {
        let current = self.current.take();
        if let Some((pos, Token::Literal(LitKind::String, value))) = current {
            self.next()?;
            return Ok(ast::StringLit { pos, value });
        }

        Err(self.unexpected(&[LitKind::String], current))
    }
}

impl Parser {
    /// parse source into golang file
    /// including imports and `type`, `var`, `const` declarations
    pub fn parse_file(&mut self) -> Result<ast::File> {
        let mut file = ast::File {
            path: self.path.clone(),
            ..Default::default()
        };

        file.docs = self.drain_comments();
        file.pkg_name = self.parse_package()?;
        self.skipped(Operator::SemiColon)?;

        // match Import declaration
        // ignore import relative pragma
        while self.current_is(Keyword::Import) {
            file.imports.extend(self.parse_import_decl()?);
            self.skipped(Operator::SemiColon)?;
        }

        let decl_key = &[Keyword::Func, Keyword::Var, Keyword::Type, Keyword::Const];
        // match declaration keyword
        while let Some((_, tok)) = &self.current {
            file.decl.push(match *tok {
                token::FUNC => ast::Declaration::Function(self.parse_func_decl()?),
                token::VAR => ast::Declaration::Variable(self.parse_decl(Parser::parse_var_spec)?),
                token::TYPE => ast::Declaration::Type(self.parse_decl(Parser::parse_type_spec)?),
                token::CONST => ast::Declaration::Const(self.parse_decl(Parser::parse_const_spec)?),
                _ => {
                    let current = self.current.take();
                    return Err(self.unexpected(decl_key, current));
                }
            });
        }

        file.comments.extend(self.comments.drain(0..));
        Ok(file)
    }

    /// parse current token as package name
    /// which is an ident but can not be '_'
    fn parse_package(&mut self) -> Result<ast::Ident> {
        self.expect(Keyword::Package)?;
        let ast::Ident { pos, name } = self.parse_ident()?;
        (name != "_")
            .then_some(ast::Ident { pos, name })
            .ok_or_else(|| self.else_error_at(pos, "package name can't be blank"))
    }

    fn parse_import_decl(&mut self) -> Result<Vec<ast::Import>> {
        self.expect(Keyword::Import)?;
        match self.skipped(Operator::ParenLeft)? {
            false => Ok(vec![self.parse_import_spec()?]),
            true => {
                let mut imports = vec![];
                while !self.current_is(Operator::ParenRight) {
                    imports.push(self.parse_import_spec()?);
                    self.skipped(Operator::SemiColon)?;
                }

                self.expect(Operator::ParenRight)?;
                Ok(imports)
            }
        }
    }

    fn parse_import_spec(&mut self) -> Result<ast::Import> {
        let exp_list: &[TokenKind] = &[
            Operator::Period.into(),
            LitKind::Ident.into(),
            LitKind::String.into(),
        ];

        let (pos, tok) = self.current.take().unwrap();
        self.next()?;

        let (name, path) = match tok {
            Token::Literal(LitKind::Ident, name) => {
                (Some(ast::Ident { pos, name }), self.parse_string_literal()?)
            }
            Token::Operator(Operator::Period) => {
                let name = String::from(".");
                (Some(ast::Ident { pos, name }), self.parse_string_literal()?)
            }
            Token::Literal(LitKind::String, value) => {
                self.next()?;
                (None, ast::StringLit { pos, value })
            }
            other => return Err(self.unexpected(exp_list, Some((pos, other)))),
        };

        Ok(ast::Import { name, path })
    }

    fn parse_func_decl(&mut self) -> Result<ast::FuncDecl> {
        let docs = self.drain_comments();
        let pos = self.expect(Keyword::Func)?;
        let recv = self
            .current_is(Operator::ParenLeft)
            .then(|| self.parse_params())
            .map_or(Ok(None), |x| x.map(Some))?;

        let name = self.parse_ident()?;
        let typ_params = (recv.is_none() && self.current_is(Operator::BarackLeft))
            .then(|| self.parse_type_parameters())
            .unwrap_or(Ok(Default::default()))?;

        let typ = ast::FuncType {
            pos,
            typ_params,
            params: self.parse_params()?,
            result: self.parse_result()?,
        };

        let body = self
            .current_is(Operator::BraceLeft)
            .then(|| self.parse_block_stmt())
            .map_or(Ok(None), |x| x.map(Some))?;

        self.skipped(Operator::SemiColon)?;
        Ok(ast::FuncDecl { docs, name, typ, recv, body })
    }

    fn parse_decl<S: Spec, F: FnMut(&mut Parser, usize) -> Result<S>>(
        &mut self,
        mut parse_spec: F,
    ) -> Result<ast::Decl<S>> {
        let mut specs = vec![];
        let pos0 = self.current_pos();
        let docs = self.drain_comments();

        self.next()?;
        if self.current_is(Operator::ParenLeft) {
            let mut index = 0;
            let left = self.expect(Operator::ParenLeft)?;
            while !self.current_is(Operator::ParenRight) {
                // index for check first iota in const spec
                specs.push(parse_spec(self, index)?);
                self.skipped(Operator::SemiColon)?;
                index += 1;
            }
            let right = self.expect(Operator::ParenRight)?;
            let pos1 = Some((left, right));
            self.skipped(Operator::SemiColon)?;
            return Ok(ast::Decl { docs, pos0, specs, pos1 });
        }

        let pos1 = None;
        specs.push(parse_spec(self, 0)?.with_docs(docs));
        self.skipped(Operator::SemiColon)?;
        Ok(ast::Decl { docs: vec![], pos0, specs, pos1 })
    }

    fn parse_type_spec(&mut self, _: usize) -> Result<ast::TypeSpec> {
        let docs = self.drain_comments();
        let name = self.parse_ident()?;

        let params = match self.current_is(Operator::BarackLeft) {
            true => self.parse_type_parameters()?,
            false => Default::default(),
        };

        let alias = self.skipped(Operator::Assign)?;
        let typ = self.parse_type()?;

        Ok(ast::TypeSpec { docs, alias, name, params, typ })
    }

    fn parse_var_spec(&mut self, _: usize) -> Result<ast::VarSpec> {
        let mut spec = ast::VarSpec {
            docs: self.drain_comments(),
            name: self.parse_ident_list()?,
            ..Default::default()
        };

        match self.skipped(Operator::Assign)? {
            true => spec.values = self.parse_expr_list()?,
            false => {
                spec.typ = Some(self.parse_type()?);
                if self.skipped(Operator::Assign)? {
                    spec.values = self.parse_expr_list()?;
                }
            }
        }

        if spec.typ.is_none() && spec.values.is_empty() {
            let pos = self.current_pos();
            Err(self.else_error_at(pos, "mission variable type or initialization"))
        } else {
            Ok(spec)
        }
    }

    fn parse_const_spec(&mut self, index: usize) -> Result<ast::ConstSpec> {
        let mut spec = ast::ConstSpec {
            docs: self.drain_comments(),
            name: self.parse_ident_list()?,
            ..Default::default()
        };

        match self.skipped(Operator::Assign)? {
            true => spec.values = self.parse_expr_list()?,
            false => {
                if self.current_is(LitKind::Ident) {
                    spec.typ = Some(self.parse_type()?);
                    self.expect(Operator::Assign)?;
                    spec.values = self.parse_expr_list()?;
                }
            }
        }

        if spec.values.is_empty() && (spec.typ.is_some() || index == 0) {
            let pos = self.current_pos();
            Err(self.else_error_at(pos, "mission constant value"))
        } else {
            Ok(spec)
        }
    }

    fn parse_type_list(&mut self) -> Result<Vec<ast::Expression>> {
        let mut result = vec![self.parse_type()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.parse_type()?);
        }

        Ok(result)
    }

    fn parse_type(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current();
        match tok {
            Token::Literal(LitKind::Ident, _) => {
                let name = self.parse_type_name()?;
                if self.current_is(Operator::BarackLeft) {
                    let pos0 = self.expect(Operator::BarackLeft)?;
                    let typ_list = self.parse_type_list()?;
                    let pos1 = self.expect(Operator::BarackRight)?;

                    return Ok(ast::Expression::Index(ast::Index {
                        pos: (pos0, pos1),
                        left: Box::new(ast::Expression::Ident(name)),
                        index: Box::new(ast::Expression::List(typ_list)),
                    }));
                }

                Ok(ast::Expression::Type(ast::Type::Ident(name)))
            }
            &token::FUNC => self
                .parse_func_type()
                .map(|x| ast::Expression::Type(ast::Type::Function(x))),
            &token::STRUCT => self
                .parse_struct_type()
                .map(|x| ast::Expression::Type(ast::Type::Struct(x))),
            &token::INTERFACE => self.parse_interface_type().map(ast::Expression::Type),
            &token::LPAREN => {
                self.next()?;
                let typ = self.parse_type()?;
                self.expect(Operator::ParenRight)?;
                Ok(typ)
            }
            &token::LBARACK => {
                self.next()?;
                if self.current_is(Operator::BarackRight) {
                    let pos = (pos, self.expect(Operator::BarackRight)?);
                    let typ = Box::new(self.parse_type()?);
                    return Ok(ast::Expression::Type(ast::Type::Slice(ast::SliceType {
                        pos,
                        typ,
                    })));
                }

                let len = Box::new(self.parse_array_len()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let typ = Box::new(self.parse_type()?);
                let pos = (pos, pos1);
                Ok(ast::Expression::Type(ast::Type::Array(ast::ArrayType {
                    len,
                    typ,
                    pos,
                })))
            }
            &token::MAP => {
                self.next()?;
                let pos0 = self.expect(Operator::BarackLeft)?;
                let key = Box::new(self.parse_type()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let val = Box::new(self.parse_type()?);
                let pos = (pos0, pos1);
                Ok(ast::Expression::Type(ast::Type::Map(ast::MapType {
                    pos,
                    key,
                    val,
                })))
            }
            &token::CHAN => {
                self.next()?;
                let pos1 = self.current_pos();
                let dir = self.skipped(Operator::Arrow)?.then_some(ChanMode::Send);
                let typ = Box::new(self.parse_type()?);
                let pos = (pos, pos1);
                Ok(ast::Expression::Type(ast::Type::Channel(
                    ast::ChannelType { pos, dir, typ },
                )))
            }
            &token::ARROW => {
                self.next()?;
                let pos1 = self.expect(Keyword::Chan)?;
                let typ = Box::new(self.parse_type()?);
                let pos = (pos, pos1);
                let dir = Some(ChanMode::Recv);
                Ok(ast::Expression::Type(ast::Type::Channel(
                    ast::ChannelType { pos, dir, typ },
                )))
            }
            &token::STAR => {
                self.next()?;
                let typ = Box::new(self.parse_type()?);
                Ok(ast::Expression::Type(ast::Type::Pointer(
                    ast::PointerType { pos, typ },
                )))
            }
            t => {
                Err(self.else_error_at(pos, format!("expect a type representation found {:?}", t)))
            }
        }
    }

    fn parse_type_name(&mut self) -> Result<ast::TypeName> {
        let current = self.current.take();
        if let Some((pos, Token::Literal(LitKind::Ident, name))) = current {
            if name == "_" {
                return Err(self.else_error_at(pos, "type name can not be blank"));
            }

            let next1 = self.next()?;
            let id0 = ast::Ident { pos, name };
            return match next1 {
                Some(&(_, token::PERIOD)) => {
                    self.next()?;
                    let pkg = Some(id0);
                    let name = self.parse_ident()?;
                    Ok(ast::TypeName { pkg, name })
                }
                _ => Ok(id0.into()),
            };
        }

        let pos = self.scan.position();
        Err(self.else_error_at(pos, "expect type name"))
    }

    #[allow(dead_code)]
    fn parse_type_parameters(&mut self) -> Result<ast::FieldList> {
        let mut fs = ast::FieldList::default();
        let pos0 = self.expect(Operator::BarackLeft)?;

        while !self.current_is(Operator::BarackRight) {
            fs.list.push(ast::Field {
                name: self.parse_ident_list()?,
                typ: self.parse_type_elem()?,
                tag: None,
            });
            self.skipped(Operator::Comma)?;
        }

        let pos1 = self.expect(Operator::BarackRight)?;
        fs.pos = Some((pos0, pos1));
        Ok(fs)
    }

    #[inline]
    fn parse_func_type(&mut self) -> Result<ast::FuncType> {
        Ok(ast::FuncType {
            pos: self.expect(Keyword::Func)?,
            typ_params: Default::default(),
            params: self.parse_params()?,
            result: self.parse_result()?,
        })
    }

    fn parse_struct_type(&mut self) -> Result<ast::StructType> {
        self.expect(Keyword::Struct)?;
        let pos1 = self.expect(Operator::BraceLeft)?;

        let mut fields = vec![];
        while !self.current_is(Operator::BraceRight) {
            let (name, typ) = match self.current_kind() {
                TokenKind::Literal(LitKind::Ident) => {
                    let mut id_list = self.parse_ident_list()?;
                    match id_list.len() {
                        1 => match self.current_kind() {
                            // { sort.Interface }
                            TokenKind::Operator(Operator::Period) => {
                                self.next()?;
                                (
                                    vec![],
                                    ast::Expression::Type(ast::Type::Ident(ast::TypeName {
                                        pkg: id_list.pop(),
                                        name: self.parse_ident()?,
                                    })),
                                )
                            }
                            // { T "tag" } | { T; } | { T }
                            TokenKind::Literal(LitKind::String)
                            | TokenKind::Operator(Operator::SemiColon | Operator::BraceRight) => (
                                vec![],
                                ast::Expression::Type(ast::Type::Ident(
                                    id_list.pop().unwrap().into(),
                                )),
                            ),
                            TokenKind::Operator(Operator::BarackLeft) => {
                                // TODO: a.b[T]
                                let pos0 = self.expect(Operator::BarackLeft)?;
                                let mut exp_list = vec![];
                                if !self.current_is(Operator::BarackRight) {
                                    exp_list.push(self.parse_expr()?);
                                    while self.current_is(Operator::Comma) {
                                        exp_list.push(self.parse_expr()?);
                                    }
                                }

                                let pos = (pos0, self.expect(Operator::BarackRight)?);
                                match exp_list.len() {
                                    0 => {
                                        // a []P
                                        let typ = Box::new(self.parse_type()?);
                                        (
                                            id_list,
                                            ast::Expression::Type(ast::Type::Slice(
                                                ast::SliceType { pos, typ },
                                            )),
                                        )
                                    }
                                    1 => {
                                        let start = self.preback();
                                        match self.parse_type() {
                                            Ok(typ) => {
                                                // a [x]P
                                                let typ = Box::new(typ);
                                                let len = Box::new(exp_list.pop().unwrap());
                                                (
                                                    id_list,
                                                    ast::Expression::Type(ast::Type::Array(
                                                        ast::ArrayType { pos, len, typ },
                                                    )),
                                                )
                                            }
                                            Err(_) => {
                                                // a[X]
                                                self.goback(start);
                                                let id0 = id_list.pop().unwrap();
                                                let left = Box::new(ast::Expression::Ident(
                                                    ast::TypeName { pkg: None, name: id0 },
                                                ));
                                                let index = Box::new(exp_list.pop().unwrap());
                                                (
                                                    vec![],
                                                    ast::Expression::Index(ast::Index {
                                                        pos,
                                                        left,
                                                        index,
                                                    }),
                                                )
                                            }
                                        }
                                    }
                                    _ => {
                                        let id0 = id_list.pop().unwrap();
                                        let left =
                                            Box::new(ast::Expression::Ident(ast::TypeName {
                                                pkg: None,
                                                name: id0,
                                            }));
                                        let indices = exp_list;
                                        (
                                            vec![],
                                            ast::Expression::IndexList(ast::IndexList {
                                                pos,
                                                left,
                                                indices,
                                            }),
                                        )
                                    }
                                }
                            }
                            // { name ?T }
                            _ => {
                                let typ = self.parse_type()?;
                                self.skipped(Operator::SemiColon)?;
                                (id_list, typ)
                            }
                        },
                        // { a, b, c ?T }
                        _ => (id_list, self.parse_type()?),
                    }
                }
                // { T }
                _ => (vec![], ast::Expression::Type(self.parse_embed_field()?)),
            };

            let current = self.current.take();
            let tag = if let Some((pos, Token::Literal(LitKind::String, value))) = current {
                self.next()?;
                Some(ast::StringLit { pos, value })
            } else {
                self.current = current;
                None
            };

            self.skipped(Operator::SemiColon)?;
            fields.push(ast::Field { name, typ, tag })
        }

        let pos2 = self.expect(Operator::BraceRight)?;
        Ok(ast::StructType { fields, pos: (pos1, pos2) })
    }

    // InterfaceType  = "interface" "{" { InterfaceElem ";" } "}" .
    // InterfaceElem  = MethodElem | TypeElem .
    fn parse_interface_type(&mut self) -> Result<ast::Type> {
        let pos = self.expect(Keyword::Interface)?;
        let pos1 = self.expect(Operator::BraceLeft)?;

        let mut methods = ast::FieldList::default();
        while !self.current_is(Operator::BraceRight) {
            let start = self.preback();
            if self.current_is(LitKind::Ident) {
                // try parse method name first
                if let Ok(field) = self.parse_method_elem() {
                    methods.list.push(field);
                    continue;
                }
            }

            self.goback(start);
            methods.list.push(ast::Field {
                tag: None,
                name: vec![],
                typ: self.parse_type_elem()?,
            });
            if !self.current_is(Operator::BraceRight) {
                self.expect(Operator::SemiColon)?;
            }
        }

        methods.pos = Some((pos1, self.expect(Operator::BraceRight)?));
        Ok(ast::Type::Interface(ast::InterfaceType { pos, methods }))
    }

    // MethodElem  = MethodName Signature .
    // MethodName  = identifier .
    fn parse_method_elem(&mut self) -> Result<ast::Field> {
        let id = self.parse_type_name()?;
        if id.pkg.is_some() || !self.current_is(Operator::ParenLeft) {
            if !self.current_is(Operator::BraceRight) {
                self.expect(Operator::SemiColon)?;
            }

            return Ok(id.into());
        }

        let typ = ast::Type::Function(ast::FuncType {
            params: self.parse_params()?,
            result: self.parse_result()?,
            ..Default::default()
        });

        if !self.current_is(Operator::BraceRight) {
            self.expect(Operator::SemiColon)?;
        }

        Ok(ast::Field {
            tag: None,
            name: vec![id.name],
            typ: ast::Expression::Type(typ),
        })
    }

    // TypeElem       = TypeTerm { "|" TypeTerm } .
    // TypeTerm       = Type | UnderlyingType .
    // UnderlyingType = "~" Type .
    fn parse_type_elem(&mut self) -> Result<ast::Expression> {
        let mut term = self.parse_type_term()?;
        while self.current_is(Operator::Or) {
            let pos = self.expect(Operator::Or)?;
            let right = self.parse_type_term()?;
            term = ast::Expression::Binary(ast::BinaryExpression {
                pos,
                op: Operator::Or,
                left: Box::new(term),
                right: Box::new(right),
            })
        }

        Ok(term)
    }

    fn parse_type_term(&mut self) -> Result<ast::Expression> {
        let pos = self.current_pos();
        let under_type = self.skipped(Operator::Tiled)?;
        let typ = self.parse_type()?;
        Ok(match under_type {
            false => typ,
            true => ast::Expression::Unary(ast::UnaryExpression {
                pos,
                op: Operator::Tiled,
                right: Box::new(typ),
            }),
        })
    }

    #[inline]
    fn parse_array_len(&mut self) -> Result<ast::Expression> {
        let pos = self.current_pos();
        let ellipsis = ast::Ellipsis { pos, elt: None };
        match self.skipped(Operator::Ellipsis)? {
            true => Ok(ast::Expression::Ellipsis(ellipsis)),
            false => self.parse_next_level_expr(),
        }
    }

    #[inline]
    fn parse_embed_field(&mut self) -> Result<ast::Type> {
        let pos = self.current_pos();
        if !self.skipped(Operator::Star)? {
            let name = self.parse_type_name()?;
            return Ok(ast::Type::Ident(name));
        }

        let name = self.parse_type_name()?;
        let typ = Box::new(ast::Expression::Type(ast::Type::Ident(name)));
        let pointer = ast::PointerType { pos, typ };
        Ok(ast::Type::Pointer(pointer))
    }

    #[inline]
    fn parse_expr_list(&mut self) -> Result<Vec<ast::Expression>> {
        let mut result = vec![self.parse_expr()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.parse_expr()?);
        }

        Ok(result)
    }

    #[inline]
    fn parse_next_level_expr(&mut self) -> Result<ast::Expression> {
        self.expr_level += 1;
        let expr = self.parse_expr();
        self.expr_level -= 1;
        expr
    }

    /// parse source into golang Expression
    pub fn parse_expr(&mut self) -> Result<ast::Expression> {
        self.parse_binary_expr(1)
    }

    fn parse_binary_expr(&mut self, prec: usize) -> Result<ast::Expression> {
        let mut expr = self.parse_unary_expr()?;
        while let Some((perc1, op)) = self.current.as_ref().and_then(|(_, tok)| match tok {
            Token::Operator(op) => (op.precedence() >= prec).then_some((op.precedence(), *op)),
            _ => None,
        }) {
            expr = ast::Expression::Binary(ast::BinaryExpression {
                op,
                pos: self.expect(op)?,
                left: Box::new(expr),
                right: Box::new(self.parse_binary_expr(perc1 + 1)?),
            })
        }

        Ok(expr)
    }

    fn parse_unary_expr(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current();
        Ok(match *tok {
            Token::Operator(
                op
                @ (Operator::Add | Operator::Sub | Operator::Not | Operator::Xor | Operator::And),
            ) => {
                self.next()?;
                let right = Box::new(self.parse_unary_expr()?);
                ast::Expression::Unary(ast::UnaryExpression { pos, op, right })
            }
            token::ARROW => {
                self.next()?;
                match self.parse_unary_expr()? {
                    // <- CHAN_TYPE => <-chan T
                    ast::Expression::Type(ast::Type::Channel(typ)) => {
                        let chan_type = self.reset_chan_arrow(pos, typ)?;
                        ast::Expression::Type(ast::Type::Channel(chan_type))
                    }
                    // receive message
                    expr => {
                        let op = Operator::Arrow;
                        let right = Box::new(expr);
                        ast::Expression::Unary(ast::UnaryExpression { pos, op, right })
                    }
                }
            }
            token::STAR => {
                self.next()?;
                let right = Box::new(self.parse_unary_expr()?);
                ast::Expression::Star(ast::StarExpression { pos, right })
            }
            _ => self.parse_primary_expr()?,
        })
    }

    /// reset the channel direction of expression `<- chan_typ`
    fn reset_chan_arrow(&mut self, pos: usize, mut typ: ChannelType) -> Result<ast::ChannelType> {
        match typ.dir {
            Some(ast::ChanMode::Recv) => {
                // <- <-chan T
                Err(self.unexpected(&[Keyword::Chan], Some((typ.pos.1, token::ARROW))))
            }
            None => {
                // <- chan T
                typ.pos = (typ.pos.0, pos);
                typ.dir = Some(ast::ChanMode::Recv);
                Ok(typ)
            }
            Some(ast::ChanMode::Send) => {
                // <- chan<- T
                match *typ.typ {
                    // <-chan <-chan T
                    ast::Expression::Type(ast::Type::Channel(chan_type)) => {
                        let chan_type = self.reset_chan_arrow(typ.pos.1, chan_type)?;
                        typ.typ = Box::new(ast::Expression::Type(ast::Type::Channel(chan_type)));
                        typ.dir = Some(ast::ChanMode::Recv);
                        typ.pos = (typ.pos.0, pos);
                        Ok(typ)
                    }
                    // <-chan <-expr
                    _ => Err(self.else_error_at(typ.pos.1, "expect channel type")),
                }
            }
        }
    }

    /// follow by https://go.dev/ref/spec#Primary_expressions
    fn parse_primary_expr(&mut self) -> Result<ast::Expression> {
        // (operand, could continue forward)
        let mut expr = (self.parse_operand()?, true);
        while self.current.is_some() && expr.1 {
            expr = self.parse_operand_right(expr.0)?;
        }

        Ok(expr.0)
    }

    /// follow by https://go.dev/ref/spec#Operands
    /// an operand may be a literal, ident, function or expression
    fn parse_operand(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.current.take().unwrap();
        Ok(match tok {
            Token::Keyword(Keyword::Func) => {
                self.current = Some((pos, tok));
                ast::Expression::FuncLit(self.parse_func_lit()?)
            }
            Token::Literal(LitKind::Ident, name) => {
                self.next()?;
                let name = ast::Ident { pos, name };
                ast::Expression::Ident(ast::TypeName { name, pkg: None })
            }
            Token::Literal(kind, value) => {
                self.next()?;
                ast::Expression::BasicLit(BasicLit { pos, kind, value })
            }
            Token::Operator(Operator::ParenLeft) => {
                self.next()?;
                let expr = self.parse_next_level_expr()?;
                self.expect(Operator::ParenRight)?;
                expr
            }
            _ => {
                self.current = Some((pos, tok));
                self.parse_type()?
            }
        })
    }

    fn parse_operand_right(&mut self, left: ast::Expression) -> Result<(ast::Expression, bool)> {
        let left = Box::new(left);
        let (pos, tok) = self.get_current();

        match *tok {
            token::PERIOD => {
                let pos = self.expect(Operator::Period)?;
                Ok((
                    match self.current_kind() {
                        token::KIND_IDENT => {
                            let right = self.parse_ident()?;
                            ast::Expression::Selector(ast::Selector { pos, right, left })
                        }
                        token::KIND_LPAREN => {
                            self.next()?;
                            let right = match self.skipped(Keyword::Type)? {
                                false => Some(Box::new(self.parse_type()?)),
                                true => None,
                            };

                            let pos = (pos, self.expect(Operator::ParenRight)?);
                            ast::Expression::TypeAssert(ast::TypeAssertion { pos, right, left })
                        }
                        _ => {
                            let current = self.current.take();
                            let expect = &[token::KIND_IDENT, token::KIND_LPAREN];
                            return Err(self.unexpected(expect, current));
                        }
                    },
                    true,
                ))
            }
            token::LBARACK => {
                let (op, mut index) = self.parse_slice_index_or_type_inst()?;
                let pos1 = self.expect(Operator::BarackRight)?;
                let pos = (pos, pos1);

                Ok((
                    match op {
                        None => {
                            let index = Box::new(index.pop().unwrap().unwrap());
                            ast::Expression::Index(ast::Index { pos, left, index })
                        }
                        Some(Operator::Comma) => {
                            let indices = index.into_iter().flatten().collect();
                            ast::Expression::IndexList(ast::IndexList { pos, left, indices })
                        }
                        Some(Operator::Colon) => {
                            let len = index.len();
                            let i3 = index.pop().unwrap_or(None).map(Box::new);
                            let i2 = index.pop().unwrap_or(None).map(Box::new);
                            let i1 = index.pop().unwrap_or(None).map(Box::new);

                            let index = match len {
                                3 => [i1, i2, i3],
                                2 => [i2, i3, None],
                                1 => [i3, None, None],
                                _ => unreachable!(),
                            };

                            ast::Expression::Slice(ast::Slice { pos, left, index })
                        }
                        _ => unreachable!(),
                    },
                    true,
                ))
            }
            token::LPAREN => {
                self.next()?;
                let mut args = vec![];
                while self.current_not(Operator::ParenRight) && self.current_not(Operator::Ellipsis)
                {
                    args.push(self.parse_next_level_expr()?);
                    self.skipped(Operator::Comma)?;
                }

                let current_pos = self.current_pos();
                let ellipsis = self.skipped(Operator::Ellipsis)?.then_some(current_pos);
                self.skipped(Operator::Comma)?; // (a, b...,)
                let pos = (pos, self.expect(Operator::ParenRight)?);
                Ok((
                    ast::Expression::Call(ast::Call { pos, args, left, ellipsis }),
                    true,
                ))
            }
            token::LBRACE => Ok(match self.check_brace(left.borrow()) {
                false => (*left, false),
                true => {
                    let typ = left;
                    let val = self.parse_lit_value()?;
                    (
                        ast::Expression::CompositeLit(ast::CompositeLit { typ, val }),
                        true,
                    )
                }
            }),
            _ => Ok((*left, false)),
        }
    }

    /// check if brace is belong to current expression
    fn check_brace(&self, expr: &ast::Expression) -> bool {
        match expr {
            ast::Expression::Type(
                ast::Type::Struct(..)
                | ast::Type::Map(..)
                | ast::Type::Array(..)
                | ast::Type::Slice(..),
            ) => true,
            ast::Expression::Ident(..)
            | ast::Expression::IndexList(..) // map[k, v]{}
            | ast::Expression::Selector(..)
            | ast::Expression::Index(..) => self.expr_level >= 0,
            _ => false,
        }
    }

    fn parse_slice_index_or_type_inst(
        &mut self,
    ) -> Result<(Option<Operator>, Vec<Option<ast::Expression>>)> {
        self.next()?;

        let mut colon = 0;
        let mut index = vec![];

        if self.skipped(Operator::Colon)? {
            colon += 1;
            index.push(None);
            if self.current_is(Operator::BarackRight) {
                return Ok((Some(Operator::Colon), index));
            }
        }

        // [:... [...
        index.push(Some(self.parse_next_level_expr()?));
        if self.current_is(Operator::BarackRight) {
            let op = (colon > 0).then(|| Operator::Colon);
            return Ok((op, index));
        }

        match self.get_current().1 {
            &token::COMMA => {
                // [a, ...
                while self.skipped(Operator::Comma)? {
                    index.push(Some(self.parse_next_level_expr()?));
                }
                Ok((Some(Operator::Comma), index))
            }
            // [:a:... [a:...
            &token::COLON => {
                self.next()?;
                if self.current_is(Operator::BarackRight) {
                    return Ok((Some(Operator::Colon), index)); // [:a] [a:]
                }

                index.push(Some(self.parse_next_level_expr()?));
                if self.current_is(Operator::BarackRight) {
                    return Ok((Some(Operator::Colon), index)); // [:a:b] [a:b]
                }

                if index.len() == 3 {
                    let pos = self.current_pos();
                    return Err(self.else_error_at(pos, "expect ] in slice [:a:b..."));
                }

                self.expect(Operator::Colon)?;
                index.push(Some(self.parse_next_level_expr()?));
                Ok((Some(Operator::Colon), index))
            }
            _ => {
                let current = self.current.take();
                Err(self.unexpected(&[Operator::Colon, Operator::Comma], current))
            }
        }
    }

    fn parse_lit_value(&mut self) -> Result<ast::LiteralValue> {
        let mut values = vec![];
        self.expr_level += 1;
        let pos0 = self.expect(Operator::BraceLeft)?;
        while !self.current_is(Operator::BraceRight) {
            values.push(self.parse_element()?);
            self.skipped(Operator::Comma)?;
        }

        self.expr_level -= 1;
        let pos1 = self.expect(Operator::BraceRight)?;
        let pos = (pos0, pos1);
        Ok(ast::LiteralValue { pos, values })
    }

    fn parse_element(&mut self) -> Result<ast::KeyedElement> {
        let key = self.parse_element_value()?;
        match self.skipped(Operator::Colon)? {
            true => {
                let key = Some(key);
                let val = self.parse_element_value()?;
                Ok(ast::KeyedElement { key, val })
            }
            false => Ok(ast::KeyedElement { key: None, val: key }),
        }
    }

    fn parse_element_value(&mut self) -> Result<ast::Element> {
        Ok(match self.current_is(Operator::BraceLeft) {
            true => ast::Element::LitValue(self.parse_lit_value()?),
            false => ast::Element::Expr(self.parse_expr()?),
        })
    }

    /// function literal is an anonymous function
    fn parse_func_lit(&mut self) -> Result<ast::FuncLit> {
        let typ = self.parse_func_type()?;
        let body = self
            .current_is(Operator::BraceLeft)
            .then(|| self.parse_block_stmt())
            .map_or(Ok(None), |x| x.map(Some))?;

        Ok(ast::FuncLit { typ, body })
    }

    /// parse params list like  
    /// `(a, b int, c bool, d int...)`
    fn parse_params(&mut self) -> Result<ast::FieldList> {
        let mut list = vec![];
        let pos1 = self.expect(Operator::ParenLeft)?;
        while !self.current_is(Operator::ParenRight) {
            list.extend(self.parse_param_decl()?);
            self.skipped(Operator::Comma)?;
        }

        let pos2 = self.expect(Operator::ParenRight)?;
        let pos = Some((pos1, pos2));
        let params = ast::FieldList { pos, list };
        self.check_field_list(params, true)
    }

    fn parse_result(&mut self) -> Result<ast::FieldList> {
        let result = match self.current {
            Some((_, token::LPAREN)) => self.parse_params()?,
            None | Some((_, token::LBRACE | token::SEMICOLON)) => ast::FieldList::default(),
            _ => match self.parse_type() {
                Ok(typ) => ast::FieldList {
                    pos: None,
                    list: vec![ast::Field { name: vec![], tag: None, typ }],
                },
                Err(_) => ast::FieldList::default(),
            },
        };

        self.check_field_list(result, false)
    }

    /// parse a group params with same type, or a ident type list
    /// return when ensure one type
    fn parse_param_decl(&mut self) -> Result<Vec<ast::Field>> {
        // let (pos, tok) = self.get_current()?;
        let (pos, tok) = self.current.take().unwrap();
        match tok {
            Token::Literal(LitKind::Ident, name) => {
                self.next()?;
                let mut ident_list = vec![];
                ident_list.push(ast::Ident { pos, name });
                loop {
                    return match self.current.as_ref().map(|(_, tok)| tok) {
                        // T, pkg.?
                        Some(&Token::Operator(Operator::Period)) => {
                            self.next()?;
                            let name = self.parse_ident()?;
                            let pkg = ident_list.pop();

                            let mut typ_list = ident_list
                                .into_iter()
                                .map(|id| id.into())
                                .collect::<Vec<_>>();

                            typ_list.push((ast::TypeName { pkg, name }).into());
                            Ok(typ_list)
                        }
                        // a, b, ?
                        Some(&Token::Operator(Operator::Comma)) => {
                            self.next()?;
                            // a, b, c
                            if self.current_is(LitKind::Ident) {
                                ident_list.push(self.parse_ident()?);
                                continue;
                            }

                            let mut type_list = ident_list
                                .into_iter()
                                .map(|id| id.into())
                                .collect::<Vec<ast::Field>>();

                            if self.current_not(Operator::ParenRight) {
                                let typ = match self.current_is(Operator::Ellipsis) {
                                    false => self.parse_type()?,
                                    true => {
                                        let pos = self.expect(Operator::Ellipsis)?;
                                        let elt = Some(Box::new(self.parse_type()?));
                                        ast::Expression::Ellipsis(ast::Ellipsis { pos, elt })
                                    }
                                };

                                type_list.push(ast::Field { name: vec![], tag: None, typ });
                            }

                            Ok(type_list)
                        }
                        // a, b ...?
                        Some(&Token::Operator(Operator::Ellipsis)) => {
                            let pos = self.expect(Operator::Ellipsis)?;
                            let elt = Some(Box::new(self.parse_type()?));
                            let typ = ast::Expression::Ellipsis(ast::Ellipsis { pos, elt });

                            if ident_list.len() > 1 {
                                return Err(
                                    self.else_error_at(pos, "mixed named and unnamed parameters")
                                );
                            }

                            let name = ident_list;
                            let field = ast::Field { name, typ, tag: None };
                            Ok(vec![field])
                        }
                        // a, b)
                        Some(&Token::Operator(Operator::ParenRight)) => {
                            Ok(ident_list.into_iter().map(|id| id.into()).collect())
                        }
                        // a, b func... | a, b struct...
                        _ => {
                            let typ = self.parse_type()?;
                            Ok(vec![ast::Field { typ, name: ident_list, tag: None }])
                        }
                    };
                }
            }
            // (...T)
            Token::Operator(Operator::Ellipsis) => {
                self.next()?;
                let elt = Some(Box::new(self.parse_type()?));
                Ok(vec![ast::Ellipsis { pos, elt }.into()])
            }
            // ()
            Token::Operator(Operator::ParenRight) => {
                self.current = Some((pos, tok));
                Ok(vec![])
            }
            _ => {
                self.current = Some((pos, tok));
                Ok(vec![ast::Field {
                    name: vec![],
                    typ: self.parse_type()?,
                    tag: None,
                }])
            }
        }
    }

    fn check_field_list(&self, f: ast::FieldList, trailing: bool) -> Result<ast::FieldList> {
        if f.list.is_empty() {
            return Ok(f);
        }

        let named = !f.list.first().unwrap().name.is_empty();
        for (index, field) in f.list.iter().enumerate() {
            if !field.name.is_empty() != named {
                return Err(self.else_error_at(f.pos(), "mixed named and unnamed parameters"));
            }

            if matches!(field.typ, ast::Expression::Ellipsis(..))
                && (index != f.list.len() - 1 || !trailing)
            {
                return Err(
                    self.else_error_at(f.pos(), "can only use ... with final parameter in list")
                );
            }
        }

        Ok(f)
    }

    fn parse_stmt_list(&mut self) -> Result<Vec<ast::Statement>> {
        let mut result = vec![];
        loop {
            match &self.current {
                None | Some((_, token::CASE | token::DEFAULT | token::RBRACE)) => {
                    return Ok(result)
                }
                _ => result.push(self.parse_stmt()?),
            }
        }
    }

    /// parse source into golang Statement
    pub fn parse_stmt(&mut self) -> Result<ast::Statement> {
        let (pos, tok) = self.get_current();
        match tok {
            Token::Literal(..)
            | Token::Keyword(
                Keyword::Func | Keyword::Struct | Keyword::Map | Keyword::Chan | Keyword::Interface,
            )
            | Token::Operator(
                Operator::Add
                | Operator::Sub
                | Operator::Star
                | Operator::Xor
                | Operator::Arrow
                | Operator::Not
                | Operator::ParenLeft
                | Operator::BarackLeft,
            ) => self
                .parse_simple_stmt()
                .and_then(|stmt| self.skipped(Operator::SemiColon).and(Ok(stmt))),
            &token::VAR | &token::TYPE | &token::CONST => {
                self.parse_decl_stmt().map(ast::Statement::Declaration)
            }
            Token::Operator(Operator::BraceLeft) => {
                self.parse_block_stmt().map(ast::Statement::Block)
            }
            Token::Keyword(Keyword::Go) => self.parse_go_stmt().map(ast::Statement::Go),
            Token::Keyword(Keyword::Defer) => self.parse_defer_stmt().map(ast::Statement::Defer),
            Token::Keyword(Keyword::Return) => self.parse_return_stmt().map(ast::Statement::Return),
            Token::Keyword(Keyword::If) => self.parse_if_stmt().map(ast::Statement::If),
            Token::Keyword(Keyword::Switch) => self.parse_switch_stmt(),
            Token::Keyword(Keyword::Select) => self.parse_select_stmt().map(ast::Statement::Select),
            Token::Keyword(Keyword::For) => self.parse_for_stmt(),
            Token::Operator(Operator::SemiColon) => {
                self.next()?;
                Ok(ast::Statement::Empty(ast::EmptyStmt { pos }))
            }
            Token::Operator(Operator::BraceRight) => {
                Ok(ast::Statement::Empty(ast::EmptyStmt { pos }))
            }
            &Token::Keyword(
                key @ (Keyword::Break | Keyword::FallThrough | Keyword::Continue | Keyword::Goto),
            ) => self.parse_branch_stmt(key).map(ast::Statement::Branch),
            _ => Err(self.else_error_at(pos, "expect statement")),
        }
    }

    fn parse_range_expr(&mut self) -> Result<ast::RangeExpr> {
        let pos = self.expect(Keyword::Range)?;
        let right = Box::new(self.parse_expr()?);
        Ok(ast::RangeExpr { pos, right })
    }

    fn parse_simple_stmt(&mut self) -> Result<ast::Statement> {
        let left = self.parse_expr_list()?;
        let (pos, tok) = self.get_current();

        Ok(match tok {
            &Token::Operator(
                op @ (Operator::Define
                | Operator::Assign
                | Operator::AddAssign
                | Operator::SubAssign
                | Operator::MulAssign
                | Operator::QuoAssign
                | Operator::RemAssign
                | Operator::AndAssign
                | Operator::OrAssign
                | Operator::XorAssign
                | Operator::ShlAssign
                | Operator::ShrAssign
                | Operator::AndNotAssign),
            ) => {
                self.next()?;
                let is_range = self.current_is(Keyword::Range);
                let is_assign = op == Operator::Assign || op == Operator::Define;
                let right = match is_range && is_assign {
                    true => vec![ast::Expression::Range(self.parse_range_expr()?)],
                    false => self.parse_expr_list()?,
                };

                if op == Operator::Define {
                    self.check_assign_stmt(&left)?;
                }

                return Ok(ast::Statement::Assign(ast::AssignStmt {
                    op,
                    pos,
                    left,
                    right,
                }));
            }
            _ => {
                let expr = self.check_single_expr(left)?;
                match *self.get_current().1 {
                    token::COLON => match expr {
                        ast::Expression::Ident(id) if id.pkg.is_none() => {
                            self.next()?;
                            let name = id.name;
                            let stmt = Box::new(self.parse_stmt()?);
                            ast::Statement::Label(ast::LabeledStmt { pos, name, stmt })
                        }
                        _ => return Err(self.else_error_at(pos, "illegal label declaration")),
                    },
                    token::ARROW => {
                        self.next()?;
                        let value = self.parse_expr()?;
                        ast::Statement::Send(ast::SendStmt { pos, chan: expr, value })
                    }
                    Token::Operator(op @ (Operator::Inc | Operator::Dec)) => {
                        self.next()?;
                        ast::Statement::IncDec(ast::IncDecStmt { pos, expr, op })
                    }
                    _ => ast::Statement::Expr(ast::ExprStmt { expr }),
                }
            }
        })
    }

    fn check_single_expr(&mut self, mut list: Vec<ast::Expression>) -> Result<ast::Expression> {
        if let Some(expr) = list.pop() {
            if list.is_empty() {
                return Ok(expr);
            }
        }

        Err(self.else_error_at(
            list.first()
                .map(|expr| expr.pos())
                .unwrap_or_else(|| self.current_pos()),
            "expect single expression",
        ))
    }

    fn check_assign_stmt(&mut self, list: &Vec<ast::Expression>) -> Result<()> {
        for expr in list {
            match expr {
                ast::Expression::Ident(id) if id.pkg.is_none() => continue,
                _ => {
                    return Err(
                        self.else_error_at(expr.pos(), "expect identifier on left side of :=")
                    )
                }
            }
        }

        Ok(())
    }

    fn parse_decl_stmt(&mut self) -> Result<ast::DeclStmt> {
        Ok(match self.current.as_ref().map(|(_, tok)| tok) {
            Some(&token::VAR) => ast::DeclStmt::Variable(self.parse_decl(Parser::parse_var_spec)?),
            Some(&token::TYPE) => ast::DeclStmt::Type(self.parse_decl(Parser::parse_type_spec)?),
            Some(&token::CONST) => ast::DeclStmt::Const(self.parse_decl(Parser::parse_const_spec)?),
            _ => unreachable!("must call at var | const | type"),
        })
    }

    fn parse_block_stmt(&mut self) -> Result<ast::BlockStmt> {
        let mut list = vec![];
        self.expr_level += 1;
        let pos0 = self.expect(Operator::BraceLeft)?;
        while !self.current_is(Operator::BraceRight) {
            list.push(self.parse_stmt()?);
        }

        self.expr_level -= 1;
        let pos = (pos0, self.expect(Operator::BraceRight)?);
        Ok(ast::BlockStmt { pos, list })
    }

    fn parse_go_stmt(&mut self) -> Result<ast::GoStmt> {
        let pos = self.expect(Keyword::Go)?;
        match self.parse_expr()? {
            ast::Expression::Call(call) => {
                // { go f() } with no semicolon
                self.skipped(Operator::SemiColon)?;
                Ok(ast::GoStmt { pos, call })
            }
            _ => Err(self.else_error_at(pos + 2, "must be invoked function after go")),
        }
    }

    fn parse_defer_stmt(&mut self) -> Result<ast::DeferStmt> {
        let pos = self.expect(Keyword::Defer)?;
        match self.parse_expr()? {
            ast::Expression::Call(call) => {
                self.expect(Operator::SemiColon)?;
                Ok(ast::DeferStmt { pos, call })
            }
            _ => Err(self.else_error_at(pos + 2, "must be invoked function after go")),
        }
    }

    fn parse_return_stmt(&mut self) -> Result<ast::ReturnStmt> {
        let pos = self.expect(Keyword::Return)?;
        let ret = (self.current_not(Operator::SemiColon) && self.current_not(Operator::BraceRight))
            .then(|| self.parse_expr_list())
            .unwrap_or(Ok(vec![]))?;

        self.skipped(Operator::SemiColon)?;
        Ok(ast::ReturnStmt { pos, ret })
    }

    fn parse_branch_stmt(&mut self, key: Keyword) -> Result<ast::BranchStmt> {
        let pos = self.expect(key)?;
        let ident = ((key != Keyword::FallThrough) && self.current_is(token::KIND_IDENT))
            .then(|| self.parse_ident())
            .map_or(Ok(None), |r| r.map(Some))?;

        self.skipped(Operator::SemiColon)?;
        Ok(ast::BranchStmt { pos, key, ident })
    }

    /// parse if statement like
    /// `if _, ok := m[k]; ok { ... }`
    /// `if a > 1 {}`
    fn parse_if_stmt(&mut self) -> Result<ast::IfStmt> {
        let pos = self.expect(Keyword::If)?;
        let (init, cond) = self.parse_if_header()?;
        let body = self.parse_block_stmt()?;

        let else_: Option<Box<ast::Statement>> = self
            .skipped(Keyword::Else)?
            .then(|| match self.current.as_ref() {
                Some((_, token::IF)) => self.parse_if_stmt().map(ast::Statement::If),
                Some((_, token::LBRACE)) => {
                    let block = self.parse_block_stmt()?;
                    self.expect(Operator::SemiColon)?;
                    Ok(ast::Statement::Block(block))
                }
                _ => Err(self.else_error("expect else or if statement")),
            })
            .map_or(Ok(None), |r| r.map(|r| Some(Box::new(r))))?;

        if else_.is_none() {
            self.skipped(Operator::SemiColon)?;
        }

        Ok(ast::IfStmt { pos, init, cond, body, else_ })
    }

    fn parse_if_header(&mut self) -> Result<(Option<Box<ast::Statement>>, ast::Expression)> {
        if self.current_is(Operator::BraceLeft) {
            return Err(self.else_error("mission condition in if statement"));
        }

        let prev_level = self.expr_level;
        self.expr_level = -1;

        let init = self
            .current_not(Operator::SemiColon)
            .then(|| match self.current_is(Keyword::Var) {
                false => self.parse_simple_stmt(),
                true => Err(self.else_error("var declaration not allowed in if statement")),
            })
            .map_or(Ok(None), |r| r.map(Some))?;

        let cond = self
            .current_not(Operator::BraceLeft)
            .then(|| {
                self.expect(Operator::SemiColon)?;
                self.parse_simple_stmt()
            })
            .map_or(Ok(None), |r| r.map(Some))?;

        let (init, cond) = match (init, cond) {
            (Some(init), Some(cond)) => (Some(init), cond),
            (Some(init), None) => (None, init),
            (None, Some(cond)) => (None, cond),
            (None, None) => return Err(self.else_error("mission cond in if statement")),
        };

        let cond = match cond {
            ast::Statement::Expr(s) => s.expr,
            _ => return Err(self.else_error("cond must be boolean expression")),
        };

        self.expr_level = prev_level;
        Ok((init.map(Box::new), cond))
    }

    fn parse_switch_stmt(&mut self) -> Result<ast::Statement> {
        let pos = self.expect(Keyword::Switch)?;
        let (mut init, mut tag) = (None, None);

        let prev_level = self.expr_level;
        self.expr_level = -1;

        if self.current_not(Operator::BraceLeft) {
            tag = self
                .current_not(Operator::SemiColon)
                .then(|| self.parse_simple_stmt())
                .map_or(Ok(None), |r| r.map(Some))?;

            if self.skipped(Operator::SemiColon)? {
                init = tag;
            }

            tag = self
                .current_not(Operator::BraceLeft)
                .then(|| self.parse_simple_stmt())
                .map_or(Ok(None), |r| r.map(Some))?;
        };

        self.expr_level = prev_level;
        let init = init.map(Box::new);
        let type_assert = self.check_switch_type_assert(&tag)?;
        let block = self.parse_case_block(type_assert)?;

        Ok(match type_assert {
            true => {
                let tag = tag.map(Box::new);
                ast::Statement::TypeSwitch(ast::TypeSwitchStmt { pos, init, tag, block })
            }
            false => {
                let tag = match tag {
                    None => None,
                    Some(ast::Statement::Expr(s)) => Some(s.expr),
                    _ => return Err(self.else_error("switch tag must be an expression")),
                };

                ast::Statement::Switch(ast::SwitchStmt { pos, init, tag, block })
            }
        })
    }

    fn parse_case_block(&mut self, type_assert: bool) -> Result<ast::CaseBlock> {
        let mut body = vec![];
        let pos = self.expect(Operator::BraceLeft)?;
        while self.current_not(Operator::BraceRight) {
            let ((pos, tok), list) = match self.current.as_ref() {
                Some((_, token::CASE)) => (
                    (self.expect(Keyword::Case)?, Keyword::Case),
                    match type_assert {
                        true => self.parse_type_list()?,
                        false => self.parse_expr_list()?,
                    },
                ),
                _ => ((self.expect(Keyword::Default)?, Keyword::Default), vec![]),
            };

            let pos = (pos, self.expect(Operator::Colon)?);
            let body_ = self.parse_stmt_list()?.into_iter().map(Box::new).collect();
            body.push(ast::CaseClause { tok, pos, list, body: body_ });
        }

        let pos = (pos, self.expect(Operator::BraceRight)?);
        Ok(ast::CaseBlock { pos, body })
    }

    fn check_switch_type_assert(&mut self, tag: &Option<ast::Statement>) -> Result<bool> {
        Ok(match tag {
            Some(ast::Statement::Expr(ast::ExprStmt {
                expr: ast::Expression::TypeAssert(..),
            })) => true,
            Some(ast::Statement::Assign(assign)) => {
                assign.left.len() == 1
                    && assign.right.len() == 1
                    && matches!(assign.right.first(), Some(ast::Expression::TypeAssert(..)))
                    && match assign.op {
                        Operator::Define => true,
                        Operator::Assign => {
                            return Err(self.else_error_at(assign.pos, "expect := found ="))
                        }
                        _ => unreachable!(),
                    }
            }
            _ => false,
        })
    }

    fn parse_select_stmt(&mut self) -> Result<ast::SelectStmt> {
        let pos = self.expect(Keyword::Select)?;
        let body = self.parse_comm_block()?;
        Ok(ast::SelectStmt { pos, body })
    }

    fn parse_comm_stmt(&mut self) -> Result<ast::Statement> {
        let list = self.parse_expr_list()?;
        Ok(match self.current.as_ref() {
            Some((pos, token::ARROW)) => {
                let pos = *pos;
                self.next()?;
                let value = self.parse_expr()?;
                let chan = self.check_single_expr(list)?;
                ast::Statement::Send(ast::SendStmt { pos, chan, value })
            }
            Some((pos, Token::Operator(op @ (Operator::Define | Operator::Assign)))) => {
                if list.len() > 2 {
                    return Err(self.else_error("expect 1 or 2 expression"));
                };

                let op = *op;
                let pos = *pos;
                self.next()?;
                let left = list;

                if op == Operator::Define {
                    self.check_assign_stmt(&left)?;
                }

                let right = vec![self.parse_expr()?];
                ast::Statement::Assign(ast::AssignStmt { pos, op, left, right })
            }
            _ => {
                let expr = self.check_single_expr(list)?;
                ast::Statement::Expr(ast::ExprStmt { expr })
            }
        })
    }

    fn parse_comm_block(&mut self) -> Result<ast::CommBlock> {
        let mut body = vec![];
        let pos = self.expect(Operator::BraceLeft)?;
        while self.current_not(Operator::BraceRight) {
            let pos = self.current_pos();
            let (comm, tok) = match self.current.as_ref() {
                Some((_, token::CASE)) => {
                    self.expect(Keyword::Case)?;
                    let stmt = self.parse_comm_stmt()?;
                    (Some(Box::new(stmt)), Keyword::Case)
                }
                _ => {
                    self.expect(Keyword::Default)?;
                    (None, Keyword::Default)
                }
            };

            let pos = (pos, self.expect(Operator::Colon)?);
            let body_ = self.parse_stmt_list()?.into_iter().map(Box::new).collect();
            body.push(ast::CommClause { pos, tok, comm, body: body_ });
        }

        let pos = (pos, self.expect(Operator::BraceRight)?);
        Ok(ast::CommBlock { pos, body })
    }

    fn parse_for_stmt(&mut self) -> Result<ast::Statement> {
        let pos = self.expect(Keyword::For)?;

        let prev_level = self.expr_level;
        self.expr_level = -1;

        if self.current_is(Keyword::Range) {
            let pos = (pos, self.expect(Keyword::Range)?);
            let expr = self.parse_expr()?;
            self.expr_level = prev_level;
            let body = self.parse_block_stmt()?;

            // for range
            return Ok(ast::Statement::Range(ast::RangeStmt {
                op: None,
                key: None,
                value: None,
                pos,
                expr,
                body,
            }));
        }

        if self.current_is(Operator::BraceLeft) {
            // for {
            self.expr_level = prev_level;
            let body = self.parse_block_stmt()?;
            return Ok(ast::Statement::For(ast::ForStmt {
                pos,
                body,
                init: None,
                cond: None,
                post: None,
            }));
        }

        let mut cond = None;
        if self.current_not(Operator::SemiColon) {
            cond = match self.parse_simple_stmt()? {
                ast::Statement::Assign(mut assign) if assign.is_range() => {
                    if assign.left.len() > 2 {
                        return Err(self.else_error_at(assign.pos, "expect at most 2 expression"));
                    }

                    let mut left = assign.left.into_iter();
                    let key = left.next();
                    let value = left.next();
                    let op = Some((assign.pos, assign.op));

                    let (pos1, expr) = match assign.right.pop() {
                        Some(ast::Expression::Range(ast::RangeExpr { pos, right })) => (pos, right),
                        _ => unreachable!(),
                    };

                    let expr = *expr;
                    let pos = (pos, pos1);
                    self.expr_level = prev_level;
                    let body = self.parse_block_stmt()?;
                    return Ok(ast::Statement::Range(ast::RangeStmt {
                        pos,
                        key,
                        value,
                        op,
                        expr,
                        body,
                    }));
                }
                stmt => Some(Box::new(stmt)),
            };
        };

        let mut init = None;
        let mut post = None;
        if self.current_is(Operator::SemiColon) {
            self.next()?;
            init = cond;
            cond = None;

            if self.current_not(Operator::SemiColon) {
                cond = Some(Box::new(self.parse_simple_stmt()?));
            }

            self.expect(Operator::SemiColon)?;
            if self.current_not(Operator::BraceLeft) {
                post = Some(Box::new(self.parse_simple_stmt()?));
            }
        }

        self.expr_level = prev_level;
        let body = self.parse_block_stmt()?;
        Ok(ast::Statement::For(ast::ForStmt {
            pos,
            init,
            cond,
            post,
            body,
        }))
    }
}

#[cfg(test)]
mod test {
    use crate::ast::{self, ChanMode, ChannelType, Declaration, Type};
    use crate::parser::Parser;
    use crate::Result;

    #[test]
    fn parse_package() -> Result<()> {
        let pkg = |s| Parser::from(s).parse_package();

        pkg("package main")?;
        pkg("package\n\nmain")?;

        assert!(pkg("\n\n").is_err());
        assert!(pkg("package _").is_err());
        assert!(pkg("package\n_").is_err());
        assert!(pkg("package package").is_err());

        Ok(())
    }

    #[test]
    fn parse_imports() -> Result<()> {
        let import = |s: &str| Parser::from(s).parse_import_decl();

        import("import ()")?;
        import("import `aa`")?;
        import("import (\n\n)")?;
        import(r#"import "liba""#)?;
        import(r#"import . "libb""#)?;
        import(r#"import _ "libc""#)?;
        import(r#"import d "libd""#)?;

        assert!(import("import _").is_err());
        assert!(import("import _ _").is_err());
        assert!(import("import . ()").is_err());

        Ok(())
    }

    #[test]
    fn parse_type() -> Result<()> {
        let type_of = |x| Parser::from(x).parse_type();

        assert!(matches!(
            type_of("int")?,
            ast::Expression::Type(Type::Ident(_)),
        ));
        assert!(matches!(
            type_of("int")?,
            ast::Expression::Type(Type::Ident(_)),
        ));
        assert!(matches!(
            type_of("int")?,
            ast::Expression::Type(Type::Ident(_)),
        ));
        assert!(matches!(
            type_of("((int))")?,
            ast::Expression::Type(Type::Ident(_)),
        ));

        assert!(matches!(
            type_of("a.b;")?,
            ast::Expression::Type(Type::Ident(_)),
        ));
        assert!(matches!(
            type_of("[]int;")?,
            ast::Expression::Type(Type::Slice(..))
        ));
        assert!(matches!(
            type_of("map[int]map[int]int;")?,
            ast::Expression::Type(Type::Map(..)),
        ));
        assert!(matches!(
            type_of("chan int;")?,
            ast::Expression::Type(Type::Channel(..)),
        ));

        assert!(matches!(
            type_of("<-chan <- chan int;")?,
            ast::Expression::Type(Type::Channel(ChannelType { dir: Some(ChanMode::Recv), .. })),
        ));

        assert!(matches!(
            type_of("chan<- int;")?,
            ast::Expression::Type(Type::Channel(ChannelType { dir: Some(ChanMode::Send), .. })),
        ));

        Ok(())
    }

    #[test]
    fn parse_decl() -> Result<()> {
        let vars = |s| Parser::from(s).parse_decl(Parser::parse_var_spec);

        vars("var a int")?;
        vars("var a = 1")?;
        vars("var a, b int")?;
        vars("var b = x.AB.A")?;
        vars("var a, b = 1, 2")?;
        vars("var a, b = result()")?;
        vars("var a, b int = 1, 2")?;
        vars("var (a = 1; b int = 2)")?;
        vars("var (a int; b, c int = 2, 3; e, f = 5, 6)")?;

        assert!(vars("var a, b;").is_err());

        let consts = |s| Parser::from(s).parse_decl(Parser::parse_const_spec);

        consts("const a = 1")?;
        consts("const a int64 = 1")?;
        consts("const a, b int64 = 1, 2")?;
        consts("const (a = iota; b; c;)")?;
        consts("const (a = 1; b, c = 2, 3)")?;

        assert!(consts("const a int64;").is_err());

        Ok(())
    }

    #[test]
    fn parse_func_decl() -> Result<()> {
        let func = |s| Parser::from(s).parse_func_decl();

        func("func f() { go f1() }")?;
        func("func (m *M) Print() { fmt.Print(m.message)}")?;
        func("func a(w t1, r *t2, e chan<- t3) {x <- t4{c: c, t: t};}")?;
        func("func min[T any](x, y T) T { return Min(x, y) }")?;
        func("func min[](x, y T) T { return Min(x, y) }")?;
        func("func min[T ~int|~float64](x, y T) T { return Min(x, y) }")?;
        func("func min[P any]() {}")?;
        func("func min[S interface{ ~[]byte|string }]() {}")?;
        func("func min[S ~[]E, E any]() {}")?;
        func("func min[_ any]() {}")?;
        func("func min[P Constraint[int]]() {}")?;
        func("func (s *SL[K, V]) It() M[K, V] { return &S[K, V]{a.b.c[0], nil} }")?;

        Ok(())
    }

    #[test]
    fn parse_type_decl() -> Result<()> {
        let typ = |s| Parser::from(s).parse_decl(Parser::parse_type_spec);

        typ("type p[T any] struct {a[T]}")?;

        Ok(())
    }

    #[test]
    fn parse_param_and_result() -> Result<()> {
        let params = |s| Parser::from(s).parse_params();

        params("()")?;
        params("(bool)")?;
        params("(a bool)")?;
        params("(func())")?;
        params("(a,\n b,\n)")?;
        params("(a ...bool)")?;
        params("(a, b, c bool)")?;
        params("(a.b, c.d) e.f")?;
        params("(int, int, bool)")?;
        params("(a, b int, c bool)")?;
        params("(int, bool, ...int)")?;
        params("(a, _ int, z float32)")?;
        params("(a, b int, z float32)")?;
        params("(prefix string, values ...int)")?;
        params("(a, b int, z float64, opt ...T)")?;

        assert!(params("(,)").is_err());
        assert!(params("(...)").is_err());
        assert!(params("(a, ...)").is_err());
        assert!(params("(...int, bool)").is_err());
        assert!(params("(...int, ...bool)").is_err());
        assert!(params("(a, b, c, d ...int)").is_err());

        let ret_params = |s| Parser::from(s).parse_result();

        ret_params("(int)")?;
        ret_params("(a int)")?;
        ret_params("(int, bool)")?;
        ret_params("(a int, b bool)")?;

        assert!(ret_params("(...bool)").is_err());
        assert!(ret_params("(a int, bool)").is_err());
        assert!(ret_params("(...bool, int)").is_err());

        Ok(())
    }

    #[test]
    fn parse_expr() -> Result<()> {
        let expr = |s| Parser::from(s).parse_expr();

        expr("a + b")?;
        expr("a % b")?;
        expr("a + b * c + d")?;
        expr("a * b + c * d")?;

        expr("call()")?;
        expr("call(1)")?;
        expr("call(1, 2)")?;
        expr("call(1, a...)")?;
        expr("call(a, b...)")?;
        expr("call(a, x.M()%99)")?;
        expr("call(a, b,)")?;

        expr("x.(int)")?;
        expr("x.(type)")?;
        expr("struct{}")?;

        expr("<-chan chan int")?;
        expr("<-chan chan<- int")?;
        expr("<-chan <-chan <-chan int")?;

        assert!(expr("<-chan <-chan <- int").is_err());

        Ok(())
    }

    #[test]
    fn parse_operand() -> Result<()> {
        let operand = |s| Parser::from(s).parse_operand();

        operand("a.b")?;
        operand("`Hola`")?;
        operand("[10]string{}")?;
        operand("[6]int{1, 2, 3, 5}")?;
        operand("[...]string{`Sat`, `Sun`}")?;
        operand("[][]Point{{{0, 1}, {1, 2}}}")?;
        operand("[...]Point{{1.5, -3.5}, {0, 0}}")?;
        operand("map[string]Point{`orig`: {0, 0}}")?;
        operand("map[Point]string{{0, 0}: `orig`}")?;

        Ok(())
    }

    #[test]
    fn parse_slice_index() -> Result<()> {
        let slice = |s| Parser::from(s).parse_slice_index_or_type_inst();

        slice("[a]")?;
        slice("[:]")?;
        slice("[a:]")?;
        slice("[:a]")?;
        slice("[a:b]")?;
        slice("[:a:b]")?;
        slice("[a:b:c]")?;

        assert!(slice("[]").is_err());
        assert!(slice("[::]").is_err());
        assert!(slice("[a::b]").is_err());
        assert!(slice("[a:b:]").is_err());

        Ok(())
    }

    #[test]
    fn parse_interface_type() -> Result<()> {
        let interface = |s| Parser::from(s).parse_interface_type();

        interface("interface{}")?;
        interface("interface{Close() error}")?;
        interface("interface{Show(int) string}")?;
        interface("interface{Show(...int) string}")?;
        interface("interface {os.FileInfo; String() string}")?;
        interface("interface {Publish(string, []byte) error}")?;

        interface("interface {~int}")?;
        interface("interface{ chan int | chan<- string }")?;
        interface("interface{ <-chan int | chan<- int }")?;
        interface("interface {~int; String() string}")?;
        interface("interface {~int | ~string | Bad3}")?;

        interface(
            "
            interface {
                ~[]byte  // the underlying type of []byte is itself
                ~MyInt   // illegal: the underlying type of MyInt is not MyInt
                ~error   // illegal: error is an interface
            }
        ",
        )?;

        interface("
            interface {
                P                // illegal: P is a type parameter
                int | ~P         // illegal: P is a type parameter
                ~int | MyInt     // illegal: the type sets for ~int and MyInt are not disjoint (~int includes MyInt)
                float32 | Float  // overlapping type sets but Float is an interface
            }
        ")?;

        assert!(interface("interface {a b}").is_err());
        assert!(interface("interface {a, b;}").is_err());
        assert!(interface("interface {a | b c}").is_err());
        assert!(interface("interface {a b | c}").is_err());

        Ok(())
    }

    #[test]
    fn parse_struct_type() -> Result<()> {
        let struct_ = |s| Parser::from(s).parse_struct_type();

        struct_("struct {}")?;
        struct_("struct {T1}")?;
        struct_("struct {*T2}")?;
        struct_("struct {P.T3}")?;
        struct_("struct {*P.T4}")?;
        struct_("struct {A *[]int}")?;
        struct_("struct {x, y int}")?;
        struct_("struct {u float32}")?;
        struct_("struct {_ float32}")?;
        struct_("struct {a int; b bool}")?;
        struct_("struct {a int\nb bool}")?;
        struct_("struct {a int ``; b bool}")?;
        struct_("struct {micro uint64 `protobuf:\"1\"`}")?;

        assert!(struct_("struct {*[]a}").is_err());
        assert!(struct_("struct {**T2}").is_err());
        assert!(struct_("struct {a _}").is_err());
        assert!(struct_("struct {a, b}").is_err());
        assert!(struct_("struct {a ...int}").is_err());
        assert!(struct_("struct {a, b int, bool}").is_err());

        Ok(())
    }

    #[test]
    fn parse_func_type() -> Result<()> {
        let func = |s| Parser::from(s).parse_func_type();

        func("func()")?;
        func("func(x int) int")?;
        func("func(n int) func(p *T)")?;
        func("func(a, _ int, z float32) bool")?;
        func("func(a, b int, z float32) (bool)")?;
        func("func(prefix string, values ...int)")?;
        func("func(int, int, float64) (float64, *[]int)")?;
        func("func(int, int, float64) (*a, []b, map[c]d)")?;

        assert!(func("func(...int").is_err());
        assert!(func("func() (...int)").is_err());
        assert!(func("func(a int, bool)").is_err());
        assert!(func("func(int) (...bool, int)").is_err());

        Ok(())
    }

    #[test]
    fn parse_stmt() -> Result<()> {
        let stmt = |s| Parser::from(s).parse_stmt();

        stmt("a <- b{c: c, d: d}")?;
        stmt("if err != nil { return }")?;
        stmt("{ _ = &AnyList{1, '1'} }")?;
        stmt("defer close() //\na = 1;")?;
        stmt("fmt.Sprintf(`123`, rand.Int()%99);")?;
        stmt("Update(a, x...,)")?;
        stmt("return &S[K, V]{a.b.c[0], nil}")?;

        Ok(())
    }

    #[test]
    fn parse_assign_stmt() -> Result<()> {
        let assign = |s| Parser::from(s).parse_simple_stmt();

        assign("x = 1")?;
        assign("*p = f()")?;
        assign("a[i] = 23")?;
        assign("(k) = <-ch")?;
        assign("a[i] <<= 2")?;
        assign("i &^= 1<<n")?;
        assign("t := x.(type)")?;
        assign("t, ok := x.(int)")?;
        assign("f2 := func() { go f1() }")?;
        assign("one, two, three = '一', '二', '三'")?;
        assign("_ = &PeerInfo{time.Now(), '1'}")?;
        assign("_ = AAA{A: 1,}")?;
        assign("_ = m[K, V]{}")?;
        assign("_ = &S[K, V]{a.b.c[0], nil}")?;

        Ok(())
    }

    #[test]
    fn parse_for_stmt() -> Result<()> {
        let stmt = |s| Parser::from(s).parse_for_stmt();

        stmt("for range ch {};")?;
        stmt("for x := range ch {};")?;
        stmt("for _, v := range x {};")?;

        stmt("for {};")?;
        stmt("for loop {};")?;
        stmt("for i := 0; i < 1; {};")?;
        stmt("for i := 0; i < 1; i++ {};")?;
        stmt("for i := 0; i < 10; i = i + n {}")?;

        Ok(())
    }

    #[test]
    fn parse_select_stmt() -> Result<()> {
        let select = |s| Parser::from(s).parse_select_stmt();

        select(
            "select {
            case i1 = <-c1:
            case c2 <- i2:
            case i3, ok := (<-c3):
            case a[f()] = <-c4:
            default:
            }",
        )?;

        Ok(())
    }

    #[test]
    fn parse_switch_stmt() -> Result<()> {
        let switch = |s| Parser::from(s).parse_switch_stmt();

        switch("switch x {}")?;
        switch("switch x;x.(type) {}")?;
        switch("switch prev := r.descsByName[name]; prev.(type) {}")?;
        switch(
            "switch tag {
            default: s3()
            case 0, 1, 2, 3: s1()
            case 4, 5, 6, 7: s2()
            }",
        )?;
        switch(
            "switch x := f(); {
            case x < 0: return -x
            default: return x
            }",
        )?;
        switch(
            "
        switch a := x; c.(type) {
            case nil, *d:
            default:
        
            }",
        )?;

        Ok(())
    }

    #[test]
    fn parse_if_stmt() -> Result<()> {
        let stmt = |s| Parser::from(s).parse_if_stmt();

        stmt("if a > 0 {};")?;
        stmt("if true {{}};")?;
        stmt("if a > 0 && yes {};")?;
        stmt("if x := f(); x > 0 {};")?;
        stmt("if m[struct{ int }{1}] {};")?;
        stmt("if struct{ bool }{true}.bool {};")?;
        stmt("if true {} else if false {} else {};")?;

        assert!(stmt("if true {} else false {};").is_err());

        Ok(())
    }

    #[test]
    fn parse_docs() -> Result<()> {
        static CODE: &str = "
        // comments...

        // docs for file
        package main

        // docs for type declaration
        type empty struct{}

        // comments...

        // docs for variable declaration
        /* 123 */ /* 456 */
        var (
            // docs for spec
            ints = 1
        )

        /* 123 
        
        123
        */
        // docs for function declaration
        func main() {}
        ";

        let mut ast = Parser::from(CODE).parse_file()?;

        assert_eq!(ast.docs.len(), 1);
        while let Some(decl) = ast.decl.pop() {
            match decl {
                Declaration::Const(..) => continue,
                Declaration::Function(x) => assert_eq!(x.docs.len(), 2),
                Declaration::Type(x) => {
                    assert_eq!(x.docs.len(), 0);
                    assert_eq!(x.specs[0].docs.len(), 1)
                }
                Declaration::Variable(x) => {
                    assert_eq!(x.docs.len(), 3);
                    assert_eq!(x.specs[0].docs.len(), 1);
                }
            }
        }

        Ok(())
    }
}
