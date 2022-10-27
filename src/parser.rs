use crate::ast;
use crate::ast::{BasicLit, ChanMode, ChannelType, Spec};
use crate::scanner::Scanner;
use crate::token;
use crate::token::{IntoKind, Keyword, LitKind, Operator, Token, TokenKind};
use crate::Error;
use crate::Pos;
use crate::PosTok;
use crate::Result;

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
    // TODO: add an tok field without pos
    // treat None as token::None
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
    fn identifier(&mut self) -> Result<ast::Ident> {
        let current = self.current.take();
        if let Some((pos, Token::Literal(LitKind::Ident, name))) = current {
            self.next()?;
            return Ok(ast::Ident { pos, name });
        }

        Err(self.unexpected(&[LitKind::Ident], current))
    }

    fn identifier_list(&mut self) -> Result<Vec<ast::Ident>> {
        let mut list = vec![self.identifier()?];
        while self.skipped(Operator::Comma)? {
            list.push(self.identifier()?);
        }

        Ok(list)
    }

    fn string_literal(&mut self) -> Result<ast::StringLit> {
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
            file.decl.push(match tok {
                Token::Keyword(Keyword::Func) => {
                    ast::Declaration::Function(self.parse_func_decl()?)
                }
                Token::Keyword(Keyword::Var) => {
                    ast::Declaration::Variable(self.parse_decl(Parser::parse_var_spec)?)
                }
                Token::Keyword(Keyword::Type) => {
                    ast::Declaration::Type(self.parse_decl(Parser::parse_type_spec)?)
                }
                Token::Keyword(Keyword::Const) => {
                    ast::Declaration::Const(self.parse_decl(Parser::parse_const_spec)?)
                }
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
        let ast::Ident { pos, name } = self.identifier()?;
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
            Operator::Dot.into(),
            LitKind::Ident.into(),
            LitKind::String.into(),
        ];

        let (pos, tok) = self.current.take().unwrap();
        self.next()?;

        let (name, path) = match tok {
            Token::Literal(LitKind::Ident, name) => {
                (Some(ast::Ident { pos, name }), self.string_literal()?)
            }
            Token::Operator(Operator::Dot) => {
                let name = String::from(".");
                (Some(ast::Ident { pos, name }), self.string_literal()?)
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
            .then(|| self.parameters())
            .map_or(Ok(None), |x| x.map(Some))?;

        let name = self.identifier()?;
        let typ_params = (recv.is_none() && self.current_is(Operator::BarackLeft))
            .then(|| self.parse_type_parameters())
            .unwrap_or(Ok((Default::default(), false)))?
            .0; // ignore extra comma

        let typ = ast::FuncType {
            pos,
            typ_params,
            params: self.parameters()?,
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
        let name = self.identifier()?;
        let params = Default::default();
        let pos0 = self.current_pos();
        let start = self.preback();
        let alias = false;

        if !self.skipped(Operator::BarackLeft)? {
            let alias = self.skipped(Operator::Assign)?;
            let typ = self.type_()?;
            return Ok(ast::TypeSpec { docs, alias, name, typ, params });
        }

        fn extract(
            expr: ast::Expression,
            comma: bool,
        ) -> (Option<ast::TypeName>, Option<ast::Expression>) {
            match expr {
                ast::Expression::Ident(id) => (Some(id), None),
                // ast::Expression::Operation(mut bexp) => {
                //     if bexp.op == Operator::Star {
                //         if let ast::Expression::Ident(id) = *bexp.x {
                //             if comma || is_type_elem(&bexp.y.unwrap()) {
                //                 return (
                //                     Some(id),
                //                     Some(ast::Expression::Operation(ast::Operation {
                //                         pos: bexp.pos,
                //                         op: bexp.op,
                //                         x: bexp.y.unwrap(),
                //                         y: None,
                //                     })),
                //                 );
                //             }

                //             bexp.x = Box::new(ast::Expression::Ident(id));
                //         }
                //     }

                //     if bexp.op == Operator::Or {
                //         match extract(*bexp.x, comma || is_type_elem(&bexp.y.unwrap())) {
                //             (Some(id), Some(lhs)) => {
                //                 return (
                //                     Some(id),
                //                     Some(ast::Expression::Operation(ast::Operation {
                //                         pos: bexp.pos,
                //                         op: bexp.op,
                //                         x: Box::new(lhs),
                //                         y: bexp.y,
                //                     })),
                //                 );
                //             }
                //             (Some(id), None) => {
                //                 bexp.x = Box::new(ast::Expression::Ident(id));
                //             }
                //             (None, Some(expr)) => {
                //                 bexp.x = Box::new(expr);
                //             }
                //             _ => unreachable!(),
                //         }
                //     }

                //     return (None, Some(ast::Expression::Operation(bexp)));
                // }
                ast::Expression::Call(mut cexp) => {
                    if let ast::Expression::Ident(id) = *cexp.left {
                        if cexp.args.len() == 1
                            && cexp.ellipsis.is_none()
                            && (comma || is_type_elem(cexp.args.first().unwrap()))
                        {
                            return (Some(id), Some(cexp.args.pop().unwrap()));
                        }

                        cexp.left = Box::new(ast::Expression::Ident(id));
                    }
                    return (None, Some(ast::Expression::Call(cexp)));
                }
                _ => (None, Some(expr)),
            }
        }

        match self.current_kind() {
            TokenKind::Literal(LitKind::Ident) => {
                let start2 = self.preback();
                let expr = self.parse_next_level_expr()?;
                let (pname, ptype) = extract(expr, self.current_is(Operator::Comma));
                if pname.is_some() && (ptype.is_some() || !self.current_is(Operator::BarackRight)) {
                    self.goback(start);
                    let params = self.parameters()?;
                    let alias = self.skipped(Operator::Assign)?;
                    let typ = self.type_()?;
                    return Ok(ast::TypeSpec { docs, alias, name, typ, params });
                }

                self.goback(start2); // TODO: how to avoid this
                let len = Box::new(self.parse_next_level_expr()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let typ = Box::new(self.type_()?);
                let typ = ast::Expression::Type(ast::Type::Array(ast::ArrayType {
                    pos: (pos0, pos1),
                    len,
                    typ,
                }));
                Ok(ast::TypeSpec { docs, alias, name, typ, params })
            }
            TokenKind::Operator(Operator::BarackRight) => {
                let pos1 = self.expect(Operator::BarackRight)?;
                let typ = ast::Expression::Type(ast::Type::Slice(ast::SliceType {
                    pos: (pos0, pos1),
                    typ: Box::new(self.type_()?),
                }));
                Ok(ast::TypeSpec { docs, alias, name, typ, params })
            }
            _ => {
                // array type
                let len = Box::new(self.array_len()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let typ = Box::new(self.type_()?);
                let typ = ast::Expression::Type(ast::Type::Array(ast::ArrayType {
                    pos: (pos0, pos1),
                    len,
                    typ,
                }));
                Ok(ast::TypeSpec { docs, alias, name, typ, params })
            }
        }
    }

    fn parse_var_spec(&mut self, _: usize) -> Result<ast::VarSpec> {
        let mut spec = ast::VarSpec {
            docs: self.drain_comments(),
            name: self.identifier_list()?,
            ..Default::default()
        };

        match self.skipped(Operator::Assign)? {
            true => spec.values = self.parse_expr_list()?,
            false => {
                spec.typ = Some(self.type_()?);
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
            name: self.identifier_list()?,
            ..Default::default()
        };

        match self.skipped(Operator::Assign)? {
            true => spec.values = self.parse_expr_list()?,
            false => {
                if self.current_is(LitKind::Ident) {
                    spec.typ = Some(self.type_()?);
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
        let mut result = vec![self.type_()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.type_()?);
        }

        Ok(result)
    }

    fn type_(&mut self) -> Result<ast::Expression> {
        match self.type_or_none()? {
            Some(typ) => Ok(typ),
            None => Err(self.else_error("expect a type representation")),
        }
    }

    /// parse a comma-separated type list
    /// in some case we found an '[' and it may be a list of type instance
    /// or just an index expression
    /// so we have a parameter `strict`
    /// if not strict, the first element may be a expression
    /// if strict we must have a list of type
    fn type_list(&mut self, strict: bool) -> Result<(ast::Expression, bool)> {
        self.expr_level += 1;
        let expr = match strict {
            true => self.type_()?,
            false => self.parse_expr()?,
        };

        let comma = self.skipped(Operator::Comma)?;
        if comma {
            if let Some(typ) = self.type_or_none()? {
                let mut list = vec![expr, typ];
                while self.skipped(Operator::Comma)? {
                    match self.type_or_none()? {
                        Some(typ) => list.push(typ),
                        None => break,
                    }
                }

                self.expr_level -= 1;
                return Ok((ast::Expression::List(list), true));
            }
        }

        self.expr_level -= 1;
        Ok((expr, comma))
    }

    /// Type      = TypeName [ TypeArgs ] | TypeLit | "(" Type ")" .
    /// TypeName  = identifier | QualifiedIdent .
    /// TypeArgs  = "[" TypeList [ "," ] "]" .
    /// TypeList  = Type { "," Type } .
    /// TypeLit   = ArrayType | StructType | PointerType | FunctionType | InterfaceType |
    ///             SliceType | MapType | ChannelType .
    fn type_or_none(&mut self) -> Result<Option<ast::Expression>> {
        match &self.current {
            Some((_, Token::Operator(Operator::Star))) => {
                let pos = self.expect(Operator::Star)?;
                let typ = Box::new(self.type_()?);
                Ok(Some(ast::Expression::Type(ast::Type::Pointer(
                    ast::PointerType { pos, typ },
                ))))
            }

            Some((_, Token::Operator(Operator::Arrow))) => {
                let pos = self.expect(Operator::Arrow)?;
                let pos1 = self.expect(Keyword::Chan)?;
                let typ = Box::new(self.type_()?);
                let pos = (pos, pos1);
                let dir = Some(ChanMode::Recv);
                Ok(Some(ast::Expression::Type(ast::Type::Channel(
                    ast::ChannelType { pos, dir, typ },
                ))))
            }

            Some((_, Token::Keyword(Keyword::Func))) => {
                let typ = self.func_type()?;
                Ok(Some(ast::Expression::Type(ast::Type::Function(typ))))
            }

            Some((_, Token::Operator(Operator::BarackLeft))) => {
                let pos = self.expect(Operator::BarackLeft)?;
                if self.current_is(Operator::BarackRight) {
                    let pos = (pos, self.expect(Operator::BarackRight)?);
                    let typ = Box::new(self.type_()?);
                    return Ok(Some(ast::Expression::Type(ast::Type::Slice(
                        ast::SliceType { pos, typ },
                    ))));
                }

                let len = Box::new(self.array_len()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let typ = Box::new(self.type_()?);
                let pos = (pos, pos1);
                Ok(Some(ast::Expression::Type(ast::Type::Array(
                    ast::ArrayType { len, typ, pos },
                ))))
            }

            Some((_, Token::Keyword(Keyword::Chan))) => {
                let pos = self.expect(Keyword::Chan)?;
                let pos1 = self.current_pos();
                let dir = self.skipped(Operator::Arrow)?.then_some(ChanMode::Send);
                let typ = Box::new(self.type_()?);
                let pos = (pos, pos1);
                Ok(Some(ast::Expression::Type(ast::Type::Channel(
                    ast::ChannelType { pos, dir, typ },
                ))))
            }

            Some((_, Token::Keyword(Keyword::Map))) => {
                self.next()?;
                let pos0 = self.expect(Operator::BarackLeft)?;
                let key = Box::new(self.type_()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let val = Box::new(self.type_()?);
                let pos = (pos0, pos1);
                Ok(Some(ast::Expression::Type(ast::Type::Map(ast::MapType {
                    pos,
                    key,
                    val,
                }))))
            }

            Some((_, Token::Keyword(Keyword::Struct))) => {
                let typ = self.parse_struct_type()?;
                Ok(Some(ast::Expression::Type(ast::Type::Struct(typ))))
            }

            Some((_, Token::Keyword(Keyword::Interface))) => {
                let typ = self.parse_interface_type()?;
                Ok(Some(ast::Expression::Type(typ)))
            }

            Some((_, Token::Literal(LitKind::Ident, name))) => {
                if name == "_" {
                    return Ok(None);
                }

                let id = self.identifier()?;
                let typ = self.qualified_ident(Some(id))?;
                Ok(Some(typ))
            }

            Some((_, Token::Operator(Operator::ParenLeft))) => {
                self.next()?;
                let typ = self.type_()?;
                self.expect(Operator::ParenRight)?;
                Ok(Some(typ))
            }

            _ => Ok(None),
        }
    }

    fn parse_type_name(&mut self) -> Result<ast::TypeName> {
        if !self.current_is(LitKind::Ident) {
            return Err(self.else_error("expect type name"));
        }

        let id0 = self.identifier()?;
        if self.skipped(Operator::Dot)? {
            let pkg = Some(id0);
            let name = self.identifier()?;
            return Ok(ast::TypeName { pkg, name });
        }

        Ok(id0.into())
    }

    fn parse_type_parameters(&mut self) -> Result<(ast::FieldList, bool)> {
        let mut fs = ast::FieldList::default();
        let pos0 = self.expect(Operator::BarackLeft)?;

        let mut extra_comma = false;
        while !self.current_is(Operator::BarackRight) {
            fs.list.push(ast::Field {
                name: self.identifier_list()?,
                typ: self.parse_type_elem()?,
                tag: None,
            });

            extra_comma = self.skipped(Operator::Comma)?;
        }

        let pos1 = self.expect(Operator::BarackRight)?;
        fs.pos = Some((pos0, pos1));
        Ok((fs, extra_comma))
    }

    fn func_type(&mut self) -> Result<ast::FuncType> {
        // keep this position
        // caller should not consume the keyword
        let pos = self.expect(Keyword::Func)?;

        // TODO: parse type parameters
        if self.current_is(Operator::BarackLeft) {
            unreachable!("func type should have no type parameters for now")
        }

        let params = self.parameters()?;
        let result = self.parse_result()?;
        let typ_params = ast::FieldList::default();

        Ok(ast::FuncType { pos, typ_params, params, result })
    }

    fn parse_struct_type(&mut self) -> Result<ast::StructType> {
        self.expect(Keyword::Struct)?;
        let pos1 = self.expect(Operator::BraceLeft)?;

        let mut fields = vec![];
        while !self.current_is(Operator::BraceRight) {
            let (name, typ) = match self.current_kind() {
                TokenKind::Literal(LitKind::Ident) => {
                    let mut id_list = self.identifier_list()?;
                    match id_list.len() {
                        1 => match self.current_kind() {
                            // { sort.Interface }
                            TokenKind::Operator(Operator::Dot) => {
                                self.next()?;
                                (
                                    vec![],
                                    ast::Expression::Type(ast::Type::Ident(ast::TypeName {
                                        pkg: id_list.pop(),
                                        name: self.identifier()?,
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
                                    while self.skipped(Operator::Comma)? {
                                        exp_list.push(self.parse_expr()?);
                                    }
                                }

                                let pos = (pos0, self.expect(Operator::BarackRight)?);
                                match exp_list.len() {
                                    0 => {
                                        // a []P
                                        let typ = Box::new(self.type_()?);
                                        (
                                            id_list,
                                            ast::Expression::Type(ast::Type::Slice(
                                                ast::SliceType { pos, typ },
                                            )),
                                        )
                                    }
                                    1 => {
                                        let start = self.preback();
                                        match self.type_() {
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
                                let typ = self.type_()?;
                                self.skipped(Operator::SemiColon)?;
                                (id_list, typ)
                            }
                        },
                        // { a, b, c ?T }
                        _ => (id_list, self.type_()?),
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
            params: self.parameters()?,
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
        let mut typ = self.parse_type_term()?;
        while self.current_is(Operator::Or) {
            let op = Operator::Or;
            let pos = self.current_pos();
            self.next()?;

            let x = Box::new(typ);
            let y = Some(Box::new(self.parse_type_term()?));
            let opt = ast::Operation { op, pos, x, y };

            typ = ast::Expression::Operation(opt)
        }

        Ok(typ)
    }

    fn parse_type_term(&mut self) -> Result<ast::Expression> {
        let pos = self.current_pos();
        let under_type = self.skipped(Operator::Tiled)?;
        let typ = self.type_()?;
        Ok(match under_type {
            false => typ,
            true => {
                let op = Operator::Tiled;
                let x = Box::new(typ);
                let opt = ast::Operation { pos, op, x, y: None };
                ast::Expression::Operation(opt)
            }
        })
    }

    fn array_len(&mut self) -> Result<ast::Expression> {
        let pos = self.current_pos();
        let ellipsis = ast::Ellipsis { pos, elt: None };
        match self.skipped(Operator::Ellipsis)? {
            true => Ok(ast::Expression::Ellipsis(ellipsis)),
            false => self.parse_next_level_expr(),
        }
    }

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

    fn parse_expr_list(&mut self) -> Result<Vec<ast::Expression>> {
        let mut result = vec![self.parse_expr()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.parse_expr()?);
        }

        Ok(result)
    }

    fn parse_next_level_expr(&mut self) -> Result<ast::Expression> {
        self.expr_level += 1;
        let expr = self.parse_expr();
        self.expr_level -= 1;
        expr
    }

    /// parse source into golang Expression
    /// Expression = UnaryExpr | Expression binary_op Expression .
    /// UnaryExpr  = PrimaryExpr | unary_op UnaryExpr .
    pub fn expression(&mut self) -> Result<ast::Expression> {
        self.binary_expression(None, 0)
    }

    /// // Expression = UnaryExpr | Expression binary_op Expression .
    fn binary_expression(
        &mut self,
        p: Option<ast::Expression>,
        prec: usize,
    ) -> Result<ast::Expression> {
        let mut x = match p {
            Some(expr) => expr,
            None => self.unray_expression()?,
        };

        loop {
            if let Some((pos, Token::Operator(op))) = self.current {
                let prec2 = op.precedence();
                if prec2 > prec {
                    self.next()?;
                    let x_ = Box::new(x);
                    let y = Some(Box::new(self.binary_expression(None, prec2)?));
                    let opt = ast::Operation { pos, op, x: x_, y };
                    x = ast::Expression::Operation(opt);
                    continue;
                }
            }
            break;
        }

        Ok(x)
    }

    fn unray_expression(&mut self) -> Result<ast::Expression> {
        match self.current {
            Some((
                pos,
                Token::Operator(
                    op @ (Operator::Star
                    | Operator::Add
                    | Operator::Sub
                    | Operator::Not
                    | Operator::Xor
                    | Operator::Tiled),
                ),
            )) => {
                self.next()?;
                let x = Box::new(self.unray_expression()?);
                let opt = ast::Operation { pos, op, x, y: None };
                return Ok(ast::Expression::Operation(opt));
            }

            Some((pos, Token::Operator(op @ Operator::And))) => {
                self.next()?;
                let x = Box::new(unparen(self.unray_expression()?));
                let opt = ast::Operation { pos, op, x, y: None };
                return Ok(ast::Expression::Operation(opt));
            }

            Some((pos, Token::Operator(op @ Operator::Arrow))) => {
                self.next()?;
                match self.unray_expression()? {
                    // convert `<- ChanType` to `<-chan Type`
                    ast::Expression::Type(ast::Type::Channel(typ)) => {
                        let chan_type = self.reset_chan_arrow(pos, typ)?;
                        return Ok(ast::Expression::Type(ast::Type::Channel(chan_type)));
                    }
                    // receive message
                    x => {
                        let x = Box::new(x);
                        let opt = ast::Operation { pos, op, x, y: None };
                        return Ok(ast::Expression::Operation(opt));
                    }
                }
            }

            _ => self.primary_expression(None),
        }
    }

    /// PrimaryExpr =
    /// 	Operand |
    /// 	Conversion |
    /// 	MethodExpr |
    /// 	PrimaryExpr Selector |
    /// 	PrimaryExpr Index |
    /// 	PrimaryExpr Slice |
    /// 	PrimaryExpr TypeAssertion |
    /// 	PrimaryExpr Arguments .
    ///
    ///     Selector       = "." identifier .
    ///     Index          = "[" Expression "]" .
    ///     Slice          = "[" [ Expression ] ":" [ Expression ] "]" |
    ///                      "[" [ Expression ] ":" Expression ":" Expression "]" .
    ///     TypeAssertion  = "." "(" Type ")" .
    ///     Arguments      = "(" [ ( ExpressionList | Type [ "," ExpressionList ] ) [ "..." ] [ "," ] ] ")" .
    fn primary_expression(&mut self, p: Option<ast::Expression>) -> Result<ast::Expression> {
        let mut x = match p {
            Some(expr) => expr,
            None => self.operand()?,
        };

        loop {
            let pos = self.current_pos();

            match &self.current {
                Some((_, Token::Operator(Operator::Dot))) => match self.next()? {
                    Some((_, Token::Literal(LitKind::Ident, _))) => {
                        let left = Box::new(x);
                        let right = self.identifier()?;
                        let sel = ast::Selector { pos, left, right };
                        x = ast::Expression::Selector(sel)
                    }
                    Some((_, Token::Operator(Operator::ParenLeft))) => {
                        self.next()?;
                        let right = match self.skipped(Keyword::Type)? {
                            false => Some(Box::new(self.type_()?)),
                            true => None,
                        };

                        let left = Box::new(x);
                        let pos = (pos, self.expect(Operator::ParenRight)?);
                        let ast = ast::TypeAssertion { pos, right, left };
                        x = ast::Expression::TypeAssert(ast);
                    }
                    _ => return Err(self.else_error("expect name or '('")),
                },

                Some((_, Token::Operator(Operator::BarackLeft))) => {
                    let (op, mut index) = self.parse_slice_index_or_type_inst()?;
                    let pos = (pos, self.expect(Operator::BarackRight)?);
                    let left = Box::new(x);

                    x = match op {
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
                                _ => unreachable!("len should less then 3"),
                            };

                            ast::Expression::Slice(ast::Slice { pos, left, index })
                        }
                        _ => unreachable!("bad operator"),
                    };
                }

                Some((_, Token::Operator(Operator::ParenLeft))) => {
                    self.next()?;
                    let mut args = vec![];
                    while self.current_not(Operator::ParenRight)
                        && self.current_not(Operator::Ellipsis)
                    {
                        args.push(self.parse_next_level_expr()?);
                        self.skipped(Operator::Comma)?;
                    }

                    let left = Box::new(x);
                    let current_pos = self.current_pos();
                    let ellipsis = self.skipped(Operator::Ellipsis)?.then_some(current_pos);
                    self.skipped(Operator::Comma)?; // (a, b...,)

                    let pos = (pos, self.expect(Operator::ParenRight)?);
                    let call = ast::Call { pos, args, left, ellipsis };
                    x = ast::Expression::Call(call);
                }

                Some((_, Token::Operator(Operator::BraceLeft))) => {
                    if !self.check_brace(&x) {
                        break;
                    }

                    let typ = Box::new(x);
                    let val = self.parse_lit_value()?;
                    let lit = ast::CompositeLit { typ, val };
                    x = ast::Expression::CompositeLit(lit);
                }

                _ => break,
            }
        }

        Ok(x)
    }

    /// Operand     = Literal | OperandName [ TypeArgs ] | "(" Expression ")" .
    /// Literal     = BasicLit | CompositeLit | FunctionLit .
    /// BasicLit    = int_lit | float_lit | imaginary_lit | rune_lit | string_lit .
    /// OperandName = identifier | QualifiedIdent .
    fn operand(&mut self) -> Result<ast::Expression> {
        match &self.current {
            Some((_, Token::Literal(LitKind::Ident, _))) => {
                let name = self.identifier()?;
                let id = ast::TypeName { pkg: None, name };
                return Ok(ast::Expression::Ident(id));
            }

            Some((_, Token::Literal(..))) => {
                let lit = self.literal()?;
                return Ok(ast::Expression::BasicLit(lit));
            }

            Some((_, Token::Operator(Operator::ParenLeft))) => {
                let pos = self.current_pos();
                self.next()?;

                let expr = Box::new(self.parse_next_level_expr()?);
                let pos1 = self.expect(Operator::ParenRight)?;
                let pos = (pos, pos1);
                let expr = ast::ParenExpression { pos, expr };
                return Ok(ast::Expression::Paren(expr));
            }

            Some((_, Token::Keyword(Keyword::Func))) => {
                let typ = self.func_type()?;
                if self.current_is(Operator::BraceLeft) {
                    let body = Some(self.func_body()?);
                    let lit = ast::FuncLit { typ, body };
                    return Ok(ast::Expression::FuncLit(lit));
                }

                let typ = ast::Type::Function(typ);
                return Ok(ast::Expression::Type(typ));
            }

            Some((
                _,
                Token::Operator(Operator::BarackLeft)
                | Token::Keyword(Keyword::Chan | Keyword::Map | Keyword::Struct | Keyword::Interface),
            )) => self.type_(),

            _ => Err(self.else_error("expect expression")),
        }
    }

    /// parse source into golang Expression
    pub fn parse_expr(&mut self) -> Result<ast::Expression> {
        self.binary_expression(None, 0)
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

    fn literal(&mut self) -> Result<ast::BasicLit> {
        match self.current.take() {
            Some((pos, Token::Literal(kind, value))) => {
                self.next()?;
                Ok(BasicLit { pos, kind, value })
            }
            _ => Err(self.else_error("expect basic literal")),
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

    fn func_body(&mut self) -> Result<ast::BlockStmt> {
        self.parse_block_stmt()
    }

    fn parse_result(&mut self) -> Result<ast::FieldList> {
        let result = match self.current {
            Some((_, Token::Operator(Operator::ParenLeft))) => self.parameters()?,
            _ => match self.type_or_none()? {
                Some(typ) => ast::FieldList {
                    pos: None,
                    list: vec![typ.into()],
                },
                None => ast::FieldList::default(),
            },
        };

        self.check_field_list(result, false)
    }

    /// Parameters     = "(" [ ParameterList [ "," ] ] ")" .
    /// ParameterList  = ParameterDecl { "," ParameterDecl } .
    fn parameters(&mut self) -> Result<ast::FieldList> {
        let pos0 = self.expect(Operator::ParenLeft)?;

        let mut list = vec![];
        while !self.current_is(Operator::ParenRight) {
            list.extend(self.parse_parameter_decl()?);
            self.skipped(Operator::Comma)?; // extra comma
        }

        let pos = Some((pos0, self.expect(Operator::ParenRight)?));
        let params = ast::FieldList { pos, list };
        self.check_field_list(params, true)
    }

    /// ParameterDecl = [ IdentifierList ] [ "..." ] Type .
    fn parse_parameter_decl(&mut self) -> Result<Vec<ast::Field>> {
        // "..." Type
        if self.current_is(Operator::Ellipsis) {
            let pos = self.expect(Operator::Ellipsis)?;
            let elt = Some(Box::new(self.type_()?));
            let typ = ast::Expression::Ellipsis(ast::Ellipsis { pos, elt });
            return Ok(vec![ast::Field { name: vec![], typ, tag: None }]);
        }

        // Type
        if self.current_not(LitKind::Ident) {
            let typ = self.type_()?;
            return Ok(vec![ast::Field { name: vec![], typ, tag: None }]);
        }

        let mut end_with_comma = false;
        let mut id_list = vec![self.identifier()?];

        loop {
            match self.current_kind() {
                TokenKind::Operator(Operator::ParenRight) => {
                    // Type1, Type2) | Type1, Type2,)
                    return Ok(id_list.into_iter().map(Into::into).collect());
                }
                TokenKind::Operator(Operator::BarackLeft) => {
                    if end_with_comma {
                        // a, b, []
                        let mut list = id_list.into_iter().map(Into::into).collect::<Vec<_>>();
                        list.push(self.type_()?.into());
                        return Ok(list);
                    }

                    match self.array_or_typeargs()? {
                        ast::Expression::Index(mut typ) => {
                            // Type1, Type2[Args]
                            let id = id_list.pop().unwrap();
                            typ.left = Box::new(ast::Expression::Ident(id.into()));
                            let typ = ast::Expression::Index(typ);
                            let field = ast::Field { name: vec![], typ, tag: None };

                            let mut list = id_list.into_iter().map(Into::into).collect::<Vec<_>>();
                            list.push(field);
                            return Ok(list);
                        }
                        typ @ _ => {
                            // a, b [N]T
                            let name = id_list;
                            return Ok(vec![ast::Field { name, typ, tag: None }]);
                        }
                    }
                }
                TokenKind::Operator(Operator::Ellipsis) => {
                    if end_with_comma {
                        // a, b, ...Type
                        let pos = self.expect(Operator::Ellipsis)?;
                        let elt = Some(Box::new(self.type_()?));
                        let typ = ast::Expression::Ellipsis(ast::Ellipsis { pos, elt });

                        let mut list = id_list.into_iter().map(Into::into).collect::<Vec<_>>();
                        list.push(typ.into());
                        return Ok(list);
                    }

                    if id_list.len() > 1 {
                        return Err(self.else_error("ellipsis type should have only one parameter"));
                    }

                    // a ...Type
                    let name = vec![id_list.pop().unwrap()];
                    let pos = self.expect(Operator::Ellipsis)?;
                    let elt = Some(Box::new(self.type_()?));
                    let typ = ast::Ellipsis { pos, elt };
                    let typ = ast::Expression::Ellipsis(typ);
                    return Ok(vec![ast::Field { name, typ, tag: None }]);
                }
                TokenKind::Operator(Operator::Dot) => {
                    if end_with_comma {
                        return Err(self.else_error("unexpected '.' after ','"));
                    }

                    let pkg = id_list.pop();
                    self.expect(Operator::Dot)?;
                    let name = self.identifier()?;
                    let typ = ast::TypeName { pkg, name };
                    let typ = ast::Expression::Ident(typ);

                    let mut list = id_list.into_iter().map(Into::into).collect::<Vec<_>>();
                    list.push(typ.into());
                    return Ok(list);
                }
                TokenKind::Operator(Operator::Comma) => {
                    self.next()?;
                    end_with_comma = true;
                    if self.current_is(LitKind::Ident) {
                        id_list.push(self.identifier()?);
                        end_with_comma = false;
                    }
                }
                _ => {
                    // a, b Type
                    let typ = self.type_()?;
                    let name = id_list;
                    return Ok(vec![ast::Field { name, typ, tag: None }]);
                }
            }
        }
    }

    /// x [n]E or x[n,], x[n1, n2], ...
    /// when we found an '[' it maybe an slice or array type or type args
    /// we will parse type list
    /// if it have not extra comman and have an type after ']' then it must be an array type
    /// if list length greater than 1 then it must be type args
    /// if list have extra comma then it must be type args
    /// else it will be an index expression
    fn array_or_typeargs(&mut self) -> Result<ast::Expression> {
        let pos0 = self.expect(Operator::BarackLeft)?;
        if self.current_is(Operator::BarackRight) {
            let pos = (pos0, self.expect(Operator::BarackRight)?);
            let typ = Box::new(self.type_()?);
            let slice = ast::Type::Slice(ast::SliceType { pos, typ });
            return Ok(ast::Expression::Type(slice));
        }

        let (expr, comma) = self.type_list(false)?;
        let pos1 = self.expect(Operator::BarackRight)?;

        if !comma {
            if let Some(typ) = self.type_or_none()? {
                let array = ast::ArrayType {
                    pos: (pos0, pos1),
                    len: Box::new(expr),
                    typ: Box::new(typ),
                };

                return Ok(ast::Expression::Type(ast::Type::Array(array)));
            }
        }

        Ok(ast::Expression::Index(ast::Index {
            pos: (pos0, pos1),
            left: Box::new(ast::Expression::List(vec![])), // FIXME: this should be None
            index: Box::new(expr),
        }))
    }

    fn qualified_ident(&mut self, name: Option<ast::Ident>) -> Result<ast::Expression> {
        let name = match name {
            Some(name) => name,
            None => self.identifier()?,
        };

        let mut typ = ast::TypeName { pkg: None, name };
        if self.current_is(Operator::Dot) {
            self.expect(Operator::Dot)?;
            typ.pkg = Some(typ.name);
            typ.name = self.identifier()?;
        }

        let typ = ast::Expression::Ident(typ);
        match self.current_is(Operator::BarackLeft) {
            false => Ok(typ),
            true => self.type_instance(typ),
        }
    }

    fn type_instance(&mut self, left: ast::Expression) -> Result<ast::Expression> {
        let pos0 = self.expect(Operator::BarackLeft)?;
        if self.current_is(Operator::BarackRight) {
            return Err(self.else_error("expect type argument list"));
        }

        let (index, _) = self.type_list(true)?;
        let pos = (pos0, self.expect(Operator::BarackRight)?);

        Ok(ast::Expression::Index(ast::Index {
            pos,
            left: Box::new(left),
            index: Box::new(index),
        }))
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
        while !matches!(
            &self.current,
            None | Some((
                _,
                Token::Keyword(Keyword::Case | Keyword::Default)
                    | Token::Operator(Operator::BraceRight),
            ))
        ) {
            result.push(self.parse_stmt()?)
        }

        Ok(result)
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
            Token::Keyword(Keyword::Var | Keyword::Type | Keyword::Const) => {
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
        Ok(match &self.current {
            Some((_, Token::Keyword(Keyword::Var))) => {
                ast::DeclStmt::Variable(self.parse_decl(Parser::parse_var_spec)?)
            }
            Some((_, Token::Keyword(Keyword::Type))) => {
                ast::DeclStmt::Type(self.parse_decl(Parser::parse_type_spec)?)
            }
            Some((_, Token::Keyword(Keyword::Const))) => {
                ast::DeclStmt::Const(self.parse_decl(Parser::parse_const_spec)?)
            }
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
        let ident = ((key != Keyword::FallThrough) && self.current_is(LitKind::Ident))
            .then(|| self.identifier())
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
            .then(|| match &self.current {
                Some((_, Token::Keyword(Keyword::If))) => {
                    let stmt = self.parse_if_stmt()?;
                    Ok(ast::Statement::If(stmt))
                }
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
            let ((pos, tok), list) = match &self.current {
                Some((_, Token::Keyword(Keyword::Case))) => (
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
                Some((_, Token::Keyword(Keyword::Case))) => {
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

fn unparen(expr: ast::Expression) -> ast::Expression {
    match expr {
        ast::Expression::Paren(x) => *x.expr,
        _ => expr,
    }
}

fn is_type_elem(expr: &ast::Expression) -> bool {
    match expr {
        ast::Expression::Type(
            ast::Type::Array(..)
            | ast::Type::Struct(..)
            | ast::Type::Function(..)
            | ast::Type::Interface(..)
            | ast::Type::Slice(..)
            | ast::Type::Map(..)
            | ast::Type::Channel(..),
        ) => true,
        ast::Expression::Paren(p) => is_type_elem(&p.expr),
        _ => false,
    }
}

#[cfg(test)]
mod test {
    use crate::ast::Declaration;
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

        func("func a()")?;
        func("func a(x int) int")?;
        func("func (S[T]) Bar()")?;
        func("func min[P any]()")?;
        func("func min[_ any]()")?;
        func("func f() { go f1() }")?;
        func("func f(n int) func(p *T)")?;
        func("func h[T Ordered](a []T)")?;
        func("func min[S ~[]E, E any]()")?;
        func("func min[P Constraint[int]]()")?;
        func("func f(a, _ int, z float32) bool")?;
        func("func f(a, b int, z float32) (bool)")?;
        func("func f(prefix string, values ...int)")?;
        func("func f(int, int, float64) (float64, *[]int)")?;
        func("func min[](x, y T) T { return Min(x, y) }")?;
        func("func min[S interface{ ~[]byte|string }]()")?;
        func("func f(int, int, float64) (*a, []b, map[c]d)")?;
        func("func (m *M) Print() { fmt.Print(m.message)}")?;
        func("func min[T any](x, y T) T { return Min(x, y) }")?;
        func("func a(w t1, r *t2, e chan<- t3) {x <- t4{c: c, t: t};}")?;
        func("func min[T ~int|~float64](x, y T) T { return Min(x, y) }")?;
        func("func (t *T) f(a *u) *s {return &t[(ptr(u.P(a))>>3)%size].root}")?;
        func("func (s *SL[K, V]) It() M[K, V] { return &S[K, V]{a.b.c[0], nil} }")?;

        assert!(func("func(...int").is_err());
        assert!(func("func() (...int)").is_err());
        assert!(func("func(a int, bool)").is_err());
        assert!(func("func(int) (...bool, int)").is_err());

        Ok(())
    }

    #[test]
    fn parse_type_decl() -> Result<()> {
        let typ = |s| Parser::from(s).parse_decl(Parser::parse_type_spec);

        typ("type n [2]int")?;
        typ("type a [sz(k{})]T")?;
        typ("type p[T any] struct {a[T]}")?;
        typ("type S[T int | string] struct { F T }")?;
        typ("type S[K Order, V any] struct {SL[K, V]}")?;
        typ("type S[T int | complex128, PT *T] struct {F PT}")?;
        typ("type S[E ~int | ~complex128, T ~*E] struct {F T}")?;
        typ("type S[T ~int | ~string, PT ~int | ~string | ~*T] struct {F T}")?;
        typ("type S[T int | *bool, PT *T | float64, PPT *PT | string] struct {F PPT}")?;

        Ok(())
    }

    #[test]
    fn parse_parameters() -> Result<()> {
        let params = |s| Parser::from(s).parameters();

        params("()")?;
        params("(S[T])")?;
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
        let operand = |s| Parser::from(s).operand();

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
    fn parse_func_type() -> Result<()> {
        let func = |s| Parser::from(s).func_type();

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
        struct_("struct {a[T]}")?;
        struct_("struct {P.T3}")?;
        struct_("struct {*P.T4}")?;
        struct_("struct {SL[K, V]}")?;
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
        let code: &str = "
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

        let mut ast = Parser::from(code).parse_file()?;

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
