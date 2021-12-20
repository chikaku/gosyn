use crate::ast::ChanMode;
use crate::ast::{self};
use crate::ast::{BasicLit, ChannelType};
use crate::scanner::{PosTok, Scanner};
use crate::token;
use crate::token::IntoKind;
use crate::token::{Keyword, LitKind, Operator, Token};
use crate::Error;
use crate::Result;
use crate::{Pos, TokenKind};
use std::borrow::Borrow;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::rc::Rc;
use std::vec;

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
        parser.next().expect("unexpected new Parser error");

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
        let expect2 = expect.into();
        let pos = self.current_pos();
        self.current_is(expect)
            .then(|| self.next().map(|_| pos))
            // can't use copy of 'expect'
            // CLion bug: Use of moved value 'expect'
            .unwrap_or(Err(self.unexpected(&[expect2], self.current.to_owned())))
    }

    /// skip while current equal to expect
    fn skipped<K: IntoKind>(&mut self, expect: K) -> Result<bool> {
        self.current_is(expect)
            .then(|| self.next().map(|_| true))
            .unwrap_or(Ok(false))
    }

    fn get_current(&self) -> Result<PosTok> {
        self.current
            .to_owned()
            .ok_or(self.else_error("unexpected EOF"))
    }

    fn current_is<K: IntoKind>(&self, expect: K) -> bool {
        self.current
            .as_ref()
            .map(|(_, tok)| tok.kind() == expect.into())
            .unwrap_or_default()
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
            .unwrap_or(self.scan.position())
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
            // TODO: what if there is no whitespace
            if self.scan.skip_whitespace() > 0 {
                self.lead_comments.clear();
            }

            pos_tok = self.scan_next()?;
        }

        self.current = pos_tok;
        Ok(self.current.as_ref())
    }
}

impl Parser {
    fn parse_ident(&mut self) -> Result<ast::Ident> {
        match self.current.to_owned() {
            Some((pos, Token::Literal(LitKind::Ident, name))) => {
                self.next()?;
                Ok(ast::Ident { pos, name })
            }
            other @ _ => Err(self.unexpected(&[LitKind::Ident], other)),
        }
    }

    fn parse_ident_list(&mut self) -> Result<Vec<ast::Ident>> {
        let mut result = vec![self.parse_ident()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.parse_ident()?);
        }

        Ok(result)
    }

    fn parse_string_literal(&mut self) -> Result<ast::StringLit> {
        match self.get_current()? {
            (pos, Token::Literal(LitKind::String, value)) => {
                self.next()?;
                Ok(ast::StringLit { pos, value })
            }
            other @ _ => Err(self.unexpected(&[LitKind::String], Some(other))),
        }
    }
}

impl Parser {
    pub fn parse_file(&mut self) -> Result<ast::File> {
        let mut file = ast::File::default();
        file.path = self.path.clone();

        file.pkg_name = self.parse_package()?;
        file.document.append(&mut self.lead_comments);
        if self.current.is_some() {
            self.expect(Operator::SemiColon)?;
        }

        // match Import declaration
        while self.current_is(Keyword::Import) {
            file.imports.extend(self.parse_import_decl()?);
            self.skipped(Operator::SemiColon)?;
        }

        let decl_key = &[Keyword::Func, Keyword::Var, Keyword::Type, Keyword::Const];
        // match declaration keyword
        while self.current.is_some() {
            let (pos, tok) = self.get_current()?;
            file.decl.push(match tok {
                token::FUNC => self.parse_func_decl()?.into(),
                token::VAR => self.parse_decl(Parser::parse_var_spec)?.into(),
                token::TYPE => self.parse_decl(Parser::parse_type_sepc)?.into(),
                token::CONST => self.parse_decl(Parser::parse_const_sepc)?.into(),
                other @ _ => return Err(self.unexpected(decl_key, Some((pos, other)))),
            });
        }

        Ok(file)
    }

    /// parse current token as package name
    /// which is an ident but can not be '_'
    fn parse_package(&mut self) -> Result<ast::Ident> {
        self.expect(Keyword::Package)?;
        let ast::Ident { pos, name } = self.parse_ident()?;
        (name != "_")
            .then_some(ast::Ident { pos, name })
            .ok_or(self.else_error_at(pos, "package name can't be blank"))
    }

    fn parse_import_decl(&mut self) -> Result<Vec<ast::Import>> {
        self.expect(Keyword::Import)?;
        match self.skipped(Operator::ParenLeft)? {
            false => Ok(vec![self.parse_import_sepc()?]),
            true => {
                let mut imports = vec![];
                while !self.current_is(Operator::ParenRight) {
                    imports.push(self.parse_import_sepc()?);
                    self.skipped(Operator::SemiColon)?;
                }

                self.expect(Operator::ParenRight)?;
                Ok(imports)
            }
        }
    }

    fn parse_import_sepc(&mut self) -> Result<ast::Import> {
        let mut docs = Vec::new();
        docs.append(&mut self.lead_comments);

        let exp_list: &[TokenKind] = &[
            Operator::Period.into(),
            LitKind::Ident.into(),
            LitKind::String.into(),
        ];

        let (pos, tok) = self.get_current()?;
        self.next()?;

        let (name, path) = match tok {
            Token::Literal(LitKind::Ident, name) => (
                Some(ast::Ident { pos, name }),
                self.parse_string_literal()?.into(),
            ),
            Token::Operator(Operator::Period) => {
                let name = String::from(".");
                (
                    Some(ast::Ident { pos, name }),
                    self.parse_string_literal()?.into(),
                )
            }
            Token::Literal(LitKind::String, value) => {
                self.next()?;
                (None, ast::StringLit { pos, value })
            }
            other @ _ => return Err(self.unexpected(exp_list, Some((pos, other)))),
        };

        Ok(ast::Import { docs, name, path })
    }

    fn parse_func_decl(&mut self) -> Result<ast::FuncDecl> {
        self.expect(Keyword::Func)?;
        let recv = self
            .current_is(Operator::ParenLeft)
            .then(|| self.parse_params())
            .map_or(Ok(None), |x| x.map(Some))?;

        let name = self.parse_ident()?;
        let mut typ = ast::FuncType::default();
        typ.params = self.parse_params()?;
        typ.result = self.parse_result()?;

        let body = self
            .current_is(Operator::BraceLeft)
            .then(|| self.parse_block_stmt())
            .map_or(Ok(None), |x| x.map(Some))?;

        self.skipped(Operator::SemiColon)?;
        Ok(ast::FuncDecl { name, typ, recv, body })
    }

    fn parse_decl<T, F: FnMut(&mut Parser) -> Result<T>>(
        &mut self,
        mut parse_spec: F,
    ) -> Result<ast::Decl<T>> {
        let mut specs = vec![];
        let pos0 = self.current_pos();
        self.next()?;

        if self.current_is(Operator::ParenLeft) {
            let left = self.expect(Operator::ParenLeft)?;
            while !self.current_is(Operator::ParenRight) {
                specs.push(parse_spec(self)?);
                self.skipped(Operator::SemiColon)?;
            }
            let right = self.expect(Operator::ParenRight)?;
            let pos1 = Some((left, right));
            self.skipped(Operator::SemiColon)?;
            return Ok(ast::Decl { pos0, specs, pos1 });
        }

        let pos1 = None;
        specs.push(parse_spec(self)?);
        self.skipped(Operator::SemiColon)?;
        Ok(ast::Decl { pos0, specs, pos1 })
    }

    fn parse_type_sepc(&mut self) -> Result<ast::TypeSpec> {
        Ok(ast::TypeSpec {
            docs: vec![],
            name: self.parse_ident()?,
            alias: self.skipped(Operator::Assign)?,
            typ: self.parse_type()?,
        })
    }

    fn parse_var_spec(&mut self) -> Result<ast::VarSpec> {
        let mut spec = ast::VarSpec::default();
        spec.name = self.parse_ident_list()?;
        match self.skipped(Operator::Assign)? {
            true => spec.values = self.parse_expr_list()?,
            false => {
                spec.typ = Some(self.parse_type()?);
                if self.skipped(Operator::Assign)? {
                    spec.values = self.parse_expr_list()?;
                }
            }
        }

        self.check_expr_init(&spec.name, &spec.values).map(|_| spec)
    }

    fn parse_const_sepc(&mut self) -> Result<ast::ConstSpec> {
        let mut spec = ast::ConstSpec::default();
        spec.name = self.parse_ident_list()?;
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

        self.check_expr_init(&spec.name, &spec.values).map(|_| spec)
    }

    #[rustfmt::skip]
    fn check_expr_init<T1, T2>(&self, left: &Vec<T1>, right: &Vec<T2>) -> Result<()> {
        let pos = self.current_pos();
        (right.len() > 0).then(|| match right.len().cmp(&left.len()) {
            std::cmp::Ordering::Equal => Ok(()),
            std::cmp::Ordering::Less => Err(self.else_error_at(pos, "mission init expression")),
            std::cmp::Ordering::Greater => Err(self.else_error_at(pos, "extra init expression")),
        }).unwrap_or(Ok(()))
    }

    fn parse_type_list(&mut self) -> Result<Vec<ast::Expression>> {
        let mut result = vec![self.parse_type()?];
        while self.current_is(Operator::Comma) {
            result.push(self.parse_type()?);
        }

        Ok(result.into_iter().map(|t| t.into()).collect())
    }

    fn parse_type(&mut self) -> Result<ast::Type> {
        let (pos, tok) = self.get_current()?;
        match tok {
            Token::Literal(LitKind::Ident, _) => {
                let name = self.parse_type_name()?;
                Ok(ast::Type::Ident(name))
            }
            token::FUNC => self.parse_func_type().map(|t| t.into()),
            token::STRUCT => self.parse_struct_type().map(ast::Type::from),
            token::INTERFACE => self.parse_interface_type(),
            token::LPAREN => {
                self.next()?;
                let typ = self.parse_type()?;
                self.expect(Operator::ParenRight)?;
                return Ok(typ);
            }
            token::LBARACK => {
                self.next()?;
                if self.current_is(Operator::BarackRight) {
                    let pos = (pos, self.expect(Operator::BarackRight)?);
                    let typ = Box::new(self.parse_type()?);
                    return Ok(ast::SliceType { pos, typ }.into());
                }

                let len = Box::new(self.parse_array_len()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let typ = Box::new(self.parse_type()?);
                let pos = (pos, pos1);
                Ok(ast::ArrayType { len, typ, pos }.into())
            }
            token::MAP => {
                self.next()?;
                let pos0 = self.expect(Operator::BarackLeft)?;
                let key = Box::new(self.parse_type()?);
                let pos1 = self.expect(Operator::BarackRight)?;
                let val = Box::new(self.parse_type()?);
                let pos = (pos0, pos1);
                Ok((ast::MapType { pos, key, val }).into())
            }
            token::CHAN => {
                self.next()?;
                let pos1 = self.current_pos();
                let dir = self.skipped(Operator::Arrow)?.then_some(ChanMode::Send);
                let typ = Box::new(self.parse_type()?);
                let pos = (pos, pos1);
                Ok(ast::ChannelType { pos, dir, typ }.into())
            }
            token::ARROW => {
                self.next()?;
                let pos1 = self.expect(Keyword::Chan)?;
                let typ = Box::new(self.parse_type()?);
                let pos = (pos, pos1);
                let dir = Some(ChanMode::Recv);
                Ok(ast::ChannelType { pos, dir, typ }.into())
            }
            token::STAR => {
                self.next()?;
                let typ = Box::new(self.parse_type()?);
                Ok(ast::PointerType { pos, typ }.into())
            }
            t @ _ => {
                Err(self.else_error_at(pos, format!("expect a type representation found {:?}", t)))
            }
        }
    }

    fn parse_type_name(&mut self) -> Result<ast::TypeName> {
        let (pos, tok) = self.get_current()?;
        match tok {
            Token::Literal(LitKind::Ident, name) => match name.as_str() {
                "_" => Err(self.else_error_at(pos, "type name can not be blank")),
                _ => {
                    self.next()?;
                    let id0 = ast::Ident { pos, name };
                    if !self.skipped(Operator::Period)? {
                        return Ok(id0.into());
                    }

                    Ok(ast::TypeName {
                        pkg: Some(id0),
                        name: self.parse_ident()?,
                    })
                }
            },
            _ => Err(self.else_error_at(pos, "expect type name")),
        }
    }

    fn parse_func_type(&mut self) -> Result<ast::FuncType> {
        let mut typ = ast::FuncType::default();
        typ.pos = self.expect(Keyword::Func)?;
        typ.params = self.parse_params()?;
        typ.result = self.parse_result()?;

        Ok(typ)
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
                                    ast::Type::Ident(ast::TypeName {
                                        pkg: id_list.pop(),
                                        name: self.parse_ident()?,
                                    }),
                                )
                            }
                            // { T "tag" } | { T; } | { T }
                            TokenKind::Literal(LitKind::String)
                            | TokenKind::Operator(Operator::SemiColon | Operator::BraceRight) => {
                                (vec![], ast::Type::Ident(id_list.pop().unwrap().into()))
                            }
                            // { name ?T }
                            _ => (id_list, self.parse_type()?),
                        },
                        // { a, b, c ?T }
                        _ => (id_list, self.parse_type()?),
                    }
                }
                // { T }
                _ => (vec![], self.parse_embed_field()?),
            };

            let tag = match self.get_current()? {
                (pos, Token::Literal(LitKind::String, value)) => {
                    self.next()?;
                    Some(ast::StringLit { pos, value })
                }
                _ => None,
            };

            let typ = typ.into();
            self.skipped(Operator::SemiColon)?;
            fields.push(ast::Field { name, typ, tag })
        }

        let pos2 = self.expect(Operator::BraceRight)?;
        Ok(ast::StructType { fields, pos: (pos1, pos2) })
    }

    fn parse_interface_type(&mut self) -> Result<ast::Type> {
        let mut methods = ast::FieldList::default();
        let pos = self.expect(Keyword::Interface)?;
        let pos1 = self.expect(Operator::BraceLeft)?;
        while !self.current_is(Operator::BraceRight) {
            let id = self.parse_type_name()?;
            if id.pkg.is_some() || !self.current_is(Operator::ParenLeft) {
                // nested interface name
                methods.list.push(id.into());
                continue;
            }

            let mut typ = ast::FuncType::default();
            typ.params = self.parse_params()?;
            typ.result = self.parse_result()?;
            let typ = ast::Type::Function(typ);
            methods.list.push(ast::Field {
                name: vec![id.name],
                typ: typ.into(),
                tag: None,
            });
        }

        methods.pos = Some((pos1, self.expect(Operator::BraceRight)?));
        Ok(ast::InterfaceType { pos, methods }.into())
    }

    fn parse_array_len(&mut self) -> Result<ast::Expression> {
        let pos = self.current_pos();
        match self.skipped(Operator::Ellipsis)? {
            true => Ok(ast::Ellipsis { pos, elt: None }.into()),
            false => self.parse_expr(),
        }
    }

    fn parse_embed_field(&mut self) -> Result<ast::Type> {
        let pos = self.current_pos();
        if !self.skipped(Operator::Star)? {
            let name = self.parse_type_name()?;
            return Ok(name.into());
        }

        let name = self.parse_type_name()?;
        let typ = Box::new(name.into());
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

    pub fn parse_expr(&mut self) -> Result<ast::Expression> {
        self.parse_binary_expr(1, false)
    }

    fn parse_stmt_expr(&mut self) -> Result<ast::Expression> {
        self.parse_binary_expr(1, true)
    }

    fn parse_stmt_expr_list(&mut self) -> Result<Vec<ast::Expression>> {
        let mut result = vec![self.parse_stmt_expr()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.parse_stmt_expr()?);
        }

        Ok(result)
    }

    fn parse_binary_expr(&mut self, prec: usize, stmt: bool) -> Result<ast::Expression> {
        let mut expr = self.parse_unary_expr(stmt)?;
        while let Some((perc1, op)) = self.current.as_ref().and_then(|(_, tok)| match tok {
            Token::Operator(op) => (op.precedence() >= prec).then_some((op.precedence(), *op)),
            _ => None,
        }) {
            expr = ast::BinaryExpression {
                op,
                pos: self.expect(op)?,
                left: Box::new(expr),
                right: Box::new(self.parse_binary_expr(perc1 + 1, stmt)?),
            }
            .into()
        }

        Ok(expr)
    }

    fn parse_unary_expr(&mut self, stmt: bool) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current()?;
        Ok(match tok {
            Token::Operator(
                op
                @ (Operator::Add | Operator::Sub | Operator::Not | Operator::Xor | Operator::And),
            ) => {
                self.next()?;
                let right = Box::new(self.parse_unary_expr(stmt)?);
                ast::UnaryExpression { pos, op, right }.into()
            }
            token::ARROW => {
                self.next()?;
                match self.parse_unary_expr(stmt)? {
                    // <- CHAN_TYPE => <-chan T
                    ast::Expression::Type(ast::Type::Channel(chtyp)) => {
                        let chan_type = self.reset_chan_arrow(pos, chtyp)?;
                        ast::Type::Channel(chan_type).into()
                    }
                    // receive message
                    expr @ _ => {
                        let op = Operator::Arrow.into();
                        let right = Box::new(expr);
                        ast::UnaryExpression { pos, op, right }.into()
                    }
                }
            }
            token::STAR => {
                self.next()?;
                let right = Box::new(self.parse_unary_expr(stmt)?);
                ast::StarExpression { pos, right }.into()
            }
            _ => self.parse_primary_expr(stmt)?.into(),
        })
    }

    /// reset the channel direction of expression `<- chan_typ`
    fn reset_chan_arrow<'a>(
        &mut self,
        pos: usize,
        mut typ: ChannelType,
    ) -> Result<ast::ChannelType> {
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
                    ast::Type::Channel(chan_type) => {
                        let chan_type = self.reset_chan_arrow(typ.pos.1, chan_type)?;
                        typ.typ = Box::new(ast::Type::Channel(chan_type).into());
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
    fn parse_primary_expr(&mut self, stmt: bool) -> Result<ast::Expression> {
        // (operand, could continue forward)
        let mut expr = (self.parse_operand()?, true);
        while self.current.is_some() && expr.1 {
            expr = self.parse_operand_right(expr.0, stmt)?;
        }

        Ok(expr.0)
    }

    /// follow by https://go.dev/ref/spec#Operands
    /// an operand may be a literal, ident, function or expression
    fn parse_operand(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current()?;
        Ok(match tok {
            Token::Keyword(Keyword::Func) => self.parse_func_lit()?.into(),
            Token::Literal(LitKind::Ident, name) => {
                self.next()?;
                let name = ast::Ident { pos, name };
                ast::TypeName { name, pkg: None }.into()
            }
            Token::Literal(kind, value) => {
                self.next()?;
                BasicLit { pos, kind, value }.into()
            }
            Token::Operator(Operator::ParenLeft) => {
                self.next()?;
                let expr = self.parse_expr()?;
                self.expect(Operator::ParenRight)?;
                expr
            }
            _ => self.parse_type()?.into(),
        })
    }

    fn parse_operand_right(
        &mut self,
        left: ast::Expression,
        stmt: bool,
    ) -> Result<(ast::Expression, bool)> {
        let left = Box::new(left);
        let (pos, tok) = self.get_current()?;
        match tok {
            token::PERIOD => {
                let pos = self.expect(Operator::Period)?;
                Ok((
                    match self.current_kind() {
                        token::KIND_IDENT => {
                            let right = self.parse_ident()?;
                            ast::Selector { pos, right, left }.into()
                        }
                        token::KIND_LPAREN => {
                            self.next()?;
                            let right = (!self.skipped(Keyword::Type)?)
                                .then(|| self.parse_type())
                                .map_or(Ok(None), |r| r.map(Some))?;
                            let pos = (pos, self.expect(Operator::ParenRight)?);
                            ast::TypeAssertion { pos, right, left }.into()
                        }
                        _ => {
                            return Err(self.unexpected(
                                &[token::KIND_IDENT, token::KIND_LPAREN],
                                Some(self.get_current()?),
                            ))
                        }
                    },
                    true,
                ))
            }
            token::LBARACK => {
                let (index, is_index) = self.parse_slice()?;
                let pos1 = self.expect(Operator::BarackRight)?;
                let pos = (pos, pos1);
                Ok((
                    match is_index {
                        true => {
                            let [index, ..] = index;
                            let index = index.expect("index should't be empty");
                            ast::Index { pos, left, index }.into()
                        }
                        false => ast::Slice { pos, left, index }.into(),
                    },
                    true,
                ))
            }
            token::LPAREN => {
                self.next()?;
                let args = self
                    .current_not(Operator::ParenRight)
                    .then(|| self.parse_expr_list())
                    .map_or(Ok(vec![]), |r| r)?;

                let current_pos = self.current_pos();
                let ellipsis = self.skipped(Operator::Ellipsis)?.then_some(current_pos);
                let pos = (pos, self.expect(Operator::ParenRight)?);
                Ok((ast::Call { pos, args, left, ellipsis }.into(), true))
            }
            token::LBRACE => Ok(match self.check_brace(left.borrow(), stmt) {
                false => (*left, false),
                true => {
                    let typ = left;
                    let val = self.parse_lit_value()?;
                    (ast::CompositeLit { typ, val }.into(), true)
                }
            }),
            _ => Ok((*left, false)),
        }
    }

    /// check if brace is belong to current expression
    fn check_brace(&self, expr: &ast::Expression, stmt: bool) -> bool {
        match expr {
            ast::Expression::Type(
                ast::Type::Struct(..)
                | ast::Type::Map(..)
                | ast::Type::Array(..)
                | ast::Type::Slice(..),
            ) => true,
            ast::Expression::Ident(..)
            | ast::Expression::Selector(..)
            | ast::Expression::Index(..) => !stmt,
            _ => false,
        }
    }

    fn parse_slice(&mut self) -> Result<([Option<Box<ast::Expression>>; 3], bool)> {
        self.next()?;
        let mut colon = 0;
        let mut index = [None, None, None];

        let first_colon = self.skipped(Operator::Colon)?;
        first_colon.then(|| colon += 1);

        if first_colon && self.current_is(Operator::BarackRight) {
            return Ok((index, false)); // [:]
        }

        // [:... [...
        index[colon] = Some(Box::new(self.parse_expr()?));
        if self.current_is(Operator::BarackRight) {
            return Ok((index, colon == 0)); // [:a] [a]
        }

        // [:a... [a...
        colon += 1;
        self.expect(Operator::Colon)?;
        if colon == 1 && self.current_is(Operator::BarackRight) {
            return Ok((index, false)); // [a:]
        }

        // [:a:... [a:...
        index[colon] = Some(Box::new(self.parse_expr()?));
        if self.current_is(Operator::BarackRight) {
            return Ok((index, false)); // [:a:b] [a:b]
        }

        // [:a:b... [a:b...
        if colon == 2 {
            let pos = self.current_pos();
            return Err(self.else_error_at(pos, "expect ] in slice [:a:b..."));
        }

        // [a:b...]
        self.expect(Operator::Colon)?;
        index[colon + 1] = Some(Box::new(self.parse_expr()?));
        Ok((index, false)) // [a:b:c
    }

    fn parse_lit_value(&mut self) -> Result<ast::LiteralValue> {
        let mut values = vec![];
        let pos0 = self.expect(Operator::BraceLeft)?;
        while !self.current_is(Operator::BraceRight) {
            values.push(self.parse_element()?);
            self.skipped(Operator::Comma)?;
        }

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
            true => self.parse_lit_value()?.into(),
            false => self.parse_expr()?.into(),
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
            _ => {
                let field = self.parse_type()?.into();
                ast::FieldList { pos: None, list: vec![field] }
            }
        };

        self.check_field_list(result, false)
    }

    /// parse a group params with same type, or a ident type list
    /// return when ensure one type
    fn parse_param_decl(&mut self) -> Result<Vec<ast::Field>> {
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
                            let name = self.parse_ident()?;
                            let pkg = ident_list.pop();

                            let mut typ_list = ident_list
                                .into_iter()
                                .map(|id| id.into())
                                .collect::<Vec<_>>();

                            typ_list.push((ast::TypeName { pkg, name }).into());
                            return Ok(typ_list);
                        }
                        // a, b, ?
                        (_, Token::Operator(Operator::Comma)) => {
                            self.next()?;
                            // a, b, c
                            if self.current_is(LitKind::Ident) {
                                ident_list.push(self.parse_ident()?);
                                continue;
                            }

                            let mut type_list = ident_list
                                .into_iter()
                                .map(|id| id.into())
                                .collect::<Vec<_>>();

                            type_list.push(match self.current_is(Operator::Ellipsis) {
                                false => self.parse_type()?.into(),
                                true => {
                                    let pos = self.expect(Operator::Ellipsis)?;
                                    let elt = Some(self.parse_type()?);
                                    ast::Ellipsis { pos, elt }.into()
                                }
                            });

                            return Ok(type_list);
                        }
                        // a, b ...?
                        (_, Token::Operator(Operator::Ellipsis)) => {
                            let pos = self.expect(Operator::Ellipsis)?;
                            let elt = Some(self.parse_type()?);
                            let typ = ast::Ellipsis { pos, elt }.into();

                            if ident_list.len() > 1 {
                                return Err(
                                    self.else_error_at(pos, "mixed named and unnamed parameters")
                                );
                            }

                            let name = ident_list;
                            let field = ast::Field { name, typ, tag: None };
                            return Ok(vec![field]);
                        }
                        // a, b)
                        (_, Token::Operator(Operator::ParenRight)) => {
                            return Ok(ident_list.into_iter().map(|id| id.into()).collect());
                        }
                        // a, b func... | a, b struct...
                        _ => {
                            let typ = self.parse_type()?;
                            return Ok(vec![ast::Field {
                                name: ident_list,
                                typ: typ.into(),
                                tag: None,
                            }]);
                        }
                    }
                }
            }
            // (...T)
            Token::Operator(Operator::Ellipsis) => {
                let pos = self.expect(Operator::Ellipsis)?;
                let elt = Some(self.parse_type()?);
                Ok(vec![ast::Ellipsis { pos, elt }.into()])
            }
            // ()
            Token::Operator(Operator::ParenRight) => Ok(vec![]),
            _ => Ok(vec![self.parse_type()?.into()]),
        }
    }

    fn check_field_list(&self, f: ast::FieldList, trailing: bool) -> Result<ast::FieldList> {
        let named = f.list.first().and_then(|x| Some(x.name.len() > 0));
        if !f.list.iter().all(|f| Some(f.name.len() > 0) == named) {
            return Err(self.else_error_at(f.pos(), "mixed named and unnamed parameters"));
        }

        for (index, field) in f.list.iter().enumerate() {
            if matches!(field.typ, ast::Expression::Ellipsis(..)) {
                if index != f.list.len() - 1 || !trailing {
                    return Err(self
                        .else_error_at(f.pos(), "can only use ... with final parameter in list"));
                }
            }
        }

        Ok(f)
    }

    fn parse_stmt_list(&mut self) -> Result<Vec<ast::Statement>> {
        let mut result = vec![];
        while !matches!(
            self.current.as_ref().map(|(_, tok)| tok),
            None | Some(&token::CASE | &token::DEFAULT | &token::RBRACE)
        ) {
            result.push(self.parse_stmt()?);
        }

        Ok(result)
    }

    fn parse_stmt(&mut self) -> Result<ast::Statement> {
        let (pos, tok) = self.get_current()?;
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
            token::VAR | token::TYPE | token::CONST => self.parse_decl_stmt().map(|d| d.into()),
            Token::Operator(Operator::BraceLeft) => Ok(self.parse_block_stmt()?.into()),
            Token::Keyword(Keyword::Go) => Ok(self.parse_go_stmt()?.into()),
            Token::Keyword(Keyword::Defer) => Ok(self.parse_defer_stmt()?.into()),
            Token::Keyword(Keyword::Return) => Ok(self.parse_return_stmt()?.into()),
            Token::Keyword(Keyword::If) => Ok(self.parse_if_stmt()?.into()),
            Token::Keyword(Keyword::Switch) => Ok(self.parse_switch_stmt()?.into()),
            Token::Keyword(Keyword::Select) => Ok(self.parse_select_stmt()?.into()),
            Token::Keyword(Keyword::For) => self.parse_for_stmt(),
            Token::Operator(Operator::SemiColon) => {
                self.next()?;
                Ok(ast::EmptyStmt { pos }.into())
            }
            Token::Operator(Operator::BraceRight) => Ok(ast::EmptyStmt { pos }.into()),
            Token::Keyword(
                key @ (Keyword::Break | Keyword::FallThrough | Keyword::Continue | Keyword::Goto),
            ) => Ok(self.parse_branch_stmt(key)?.into()),
            _ => Err(self.else_error_at(pos, "expect statement")),
        }
    }

    fn parse_range_expr(&mut self) -> Result<ast::RangeExpr> {
        let pos = self.expect(Keyword::Range)?;
        let right = Box::new(self.parse_stmt_expr()?);
        Ok(ast::RangeExpr { pos, right })
    }

    fn parse_simple_stmt(&mut self) -> Result<ast::Statement> {
        let left = self.parse_stmt_expr_list()?;
        let (pos, tok) = self.get_current()?;
        Ok(match tok {
            Token::Operator(
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
                    true => vec![self.parse_range_expr()?.into()],
                    false => self.parse_expr_list()?,
                };

                if op == Operator::Define {
                    self.check_assign_stmt(&left)?;
                }

                return Ok(ast::AssignStmt { op, pos, left, right }.into());
            }
            tok @ _ => {
                let expr = self.check_single_expr(left)?;
                match tok {
                    token::COLON => match expr {
                        ast::Expression::Ident(ast::TypeName { pkg: None, name }) => {
                            self.next()?;
                            let stmt = Box::new(self.parse_stmt()?);
                            ast::LabeledStmt { pos, name, stmt }.into()
                        }
                        _ => return Err(self.else_error_at(pos, "illegal label declaration")),
                    },
                    token::ARROW => {
                        self.next()?;
                        let value = self.parse_stmt_expr()?;
                        ast::SendStmt { pos, chan: expr, value }.into()
                    }
                    Token::Operator(op @ (Operator::Inc | Operator::Dec)) => {
                        self.next()?;
                        ast::IncDecStmt { pos, expr, op }.into()
                    }
                    _ => ast::ExprStmt { expr }.into(),
                }
            }
        })
    }

    fn check_single_expr(&mut self, list: Vec<ast::Expression>) -> Result<ast::Expression> {
        let pos = list
            .first()
            .map(|expr| expr.pos())
            .unwrap_or(self.current_pos());

        let mut iter = list.into_iter();
        match (iter.next(), iter.next()) {
            (Some(expr), None) => Ok(expr),
            _ => return Err(self.else_error_at(pos, "expect single epxression")),
        }
    }

    fn check_assign_stmt(&mut self, list: &Vec<ast::Expression>) -> Result<()> {
        list.iter()
            .find_map(|expr| {
                (!matches!(
                    expr,
                    ast::Expression::Ident(ast::TypeName { pkg: None, .. })
                ))
                .then_some(Err(
                    self.else_error_at(expr.pos(), "expect identifier on left side of :=")
                ))
            })
            .unwrap_or(Ok(()))
    }

    fn parse_decl_stmt(&mut self) -> Result<ast::DeclStmt> {
        Ok(match self.get_current().map(|(_, tok)| tok)? {
            token::VAR => self.parse_decl(Parser::parse_var_spec)?.into(),
            token::TYPE => self.parse_decl(Parser::parse_type_sepc)?.into(),
            token::CONST => self.parse_decl(Parser::parse_const_sepc)?.into(),
            _ => unreachable!("must call at var | const | type"),
        })
    }

    fn parse_block_stmt(&mut self) -> Result<ast::BlockStmt> {
        let mut list = vec![];
        let pos0 = self.expect(Operator::BraceLeft)?;
        while !self.current_is(Operator::BraceRight) {
            list.push(self.parse_stmt()?);
        }

        let pos = (pos0, self.expect(Operator::BraceRight)?);
        Ok(ast::BlockStmt { pos, list })
    }

    fn parse_go_stmt(&mut self) -> Result<ast::GoStmt> {
        let pos = self.expect(Keyword::Go)?;
        match self.parse_expr()? {
            ast::Expression::Call(call) => {
                self.expect(Operator::SemiColon)?;
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

        self.expect(Operator::SemiColon)?;
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
                Some((_, token::IF)) => Ok(self.parse_if_stmt()?.into()),
                Some((_, token::LBRACE)) => {
                    let block = self.parse_block_stmt()?;
                    self.expect(Operator::SemiColon)?;
                    Ok(block.into())
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

        Ok((init.map(Box::new), cond))
    }

    fn parse_switch_stmt(&mut self) -> Result<ast::Statement> {
        let pos = self.expect(Keyword::Switch)?;
        let (mut init, mut tag) = (None, None);

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

        let init = init.map(Box::new);
        let type_assert = self.check_switch_type_assert(&tag)?;
        let block = self.parse_case_block(type_assert)?;

        Ok(match type_assert {
            true => {
                let tag = tag.map(Box::new);
                ast::TypeSwitchStmt { pos, init, tag, block }.into()
            }
            false => {
                let tag = match tag {
                    None => None,
                    Some(ast::Statement::Expr(s)) => Some(s.expr),
                    _ => return Err(self.else_error("switch tag must be an expression")),
                };

                ast::SwitchStmt { pos, init, tag, block }.into()
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
                        false => self.parse_stmt_expr_list()?,
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
                ast::SendStmt { pos, chan, value }.into()
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
                ast::AssignStmt { pos, op, left, right }.into()
            }
            _ => {
                let expr = self.check_single_expr(list)?;
                ast::ExprStmt { expr }.into()
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
        if self.current_is(Keyword::Range) {
            // for range
            return Ok(ast::RangeStmt {
                op: None,
                key: None,
                value: None,
                pos: (pos, self.expect(Keyword::Range)?),
                expr: self.parse_stmt_expr()?,
                body: self.parse_block_stmt()?,
            }
            .into());
        }

        if self.current_is(Operator::BraceLeft) {
            // for {
            let body = self.parse_block_stmt()?;
            return Ok(ast::ForStmt {
                pos,
                body,
                init: None,
                cond: None,
                post: None,
            }
            .into());
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
                    let body = self.parse_block_stmt()?;
                    return Ok(ast::RangeStmt { pos, key, value, op, expr, body }.into());
                }
                stmt @ _ => Some(Box::new(stmt)),
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

        let body = self.parse_block_stmt()?;
        Ok(ast::ForStmt { pos, init, cond, post, body }.into())
    }
}

#[cfg(test)]
mod test {
    use crate::ast::{ChanMode, ChannelType, Type};
    use crate::parser::Parser;
    use crate::Result;

    #[test]
    fn parse_package() -> Result<()> {
        let pkg = |s| Parser::from_str(s).parse_package();

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
        let import = |s: &str| Parser::from_str(s).parse_import_decl();

        import("import ()")?;
        import("import `aa`")?;
        import("import (\n\n)")?;
        import(r#"import "liba""#)?;
        import(r#"import . "libb""#)?;
        import(r#"import _ "libc""#)?;
        import(r#"import d "libd""#)?;
        import("import (\"a\"\n. \"b\"\n_ \"c\"\nd \"d\")")?;

        assert!(import("import _").is_err());
        assert!(import("import _ _").is_err());
        assert!(import("import . ()").is_err());

        Ok(())
    }

    #[test]
    fn parse_type() -> Result<()> {
        let type_of = |x| Parser::from_str(x).parse_type();

        assert!(matches!(type_of("int")?, Type::Ident(_)));
        assert!(matches!(type_of("int")?, Type::Ident(_)));
        assert!(matches!(type_of("int")?, Type::Ident(_)));
        assert!(matches!(type_of("((int))")?, Type::Ident(_)));

        assert!(matches!(type_of("a.b;")?, Type::Ident(..)));
        assert!(matches!(type_of("[]int;")?, Type::Slice(..)));
        assert!(matches!(type_of("map[int]map[int]int;")?, Type::Map(..),));
        assert!(matches!(type_of("chan int;")?, Type::Channel(..)));

        assert!(matches!(
            type_of("<-chan <- chan int;")?,
            Type::Channel(ChannelType { dir: Some(ChanMode::Recv), .. })
        ));

        assert!(matches!(
            type_of("chan<- int;")?,
            Type::Channel(ChannelType { dir: Some(ChanMode::Send), .. })
        ));

        Ok(())
    }

    #[test]
    fn parse_decl() -> Result<()> {
        let vars = |s| Parser::from_str(s).parse_decl(Parser::parse_var_spec);

        vars("var a int")?;
        vars("var a = 1")?;
        vars("var a, b int")?;
        vars("var a, b = 1, 2")?;
        vars("var a, b int = 1, 2")?;
        vars("var (a = 1; b int = 2)")?;
        vars("var (a int; b, c int = 2, 3; e, f = 5, 6)")?;

        assert!(vars("var a, b;").is_err());

        let consts = |s| Parser::from_str(s).parse_decl(Parser::parse_const_sepc);

        consts("const a = 1")?;
        consts("const a int64 = 1")?;
        consts("const a, b int64 = 1, 2")?;
        consts("const (a = iota; b; c;)")?;
        consts("const (a = 1; b, c = 2, 3)")?;

        assert!(consts("const a int64;").is_err());
        assert!(consts("const (a = iota b, c = iota)").is_err());

        Ok(())
    }

    #[test]
    fn parse_func_decl() -> Result<()> {
        let func = |s| Parser::from_str(s).parse_func_decl();

        func("func (m *M) Print() { fmt.Print(m.message)}")?;

        Ok(())
    }

    #[test]
    fn parse_param_and_result() -> Result<()> {
        let params = |s| Parser::from_str(s).parse_params();

        params("()")?;
        params("(bool)")?;
        params("(a bool)")?;
        params("(a ...bool)")?;
        params("(a, b, c bool)")?;
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

        let ret_params = |s| Parser::from_str(s).parse_result();

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
        let expr = |s| Parser::from_str(s).parse_expr();

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
        let operand = |s| Parser::from_str(s).parse_operand();

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
        let slice = |s| Parser::from_str(s).parse_slice();

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
        let interface = |s| Parser::from_str(s).parse_interface_type();

        interface("interface{}")?;
        interface("interface{Close() error}")?;
        interface("interface{Show(int) string}")?;
        interface("interface{Show(...int) string}")?;

        assert!(interface("interface {a, b;}").is_err());

        Ok(())
    }

    #[test]
    fn parse_struct_type() -> Result<()> {
        let struct_ = |s| Parser::from_str(s).parse_struct_type();

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
        struct_("struct {microsec  uint64 `protobuf:\"1\"`}")?;

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
        let func = |s| Parser::from_str(s).parse_func_type();

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
        let stmt = |s| Parser::from_str(s).parse_stmt();

        stmt("if err != nil { return }")?;
        stmt("{ _ = &AnyList{1, '1'} }")?;
        stmt("fmt.Sprintf(`123`, rand.Int()%999999);")?;

        Ok(())
    }

    #[test]
    fn parse_assign_stmt() -> Result<()> {
        let assign = |s| Parser::from_str(s).parse_simple_stmt();

        assign("x = 1")?;
        assign("*p = f()")?;
        assign("a[i] = 23")?;
        assign("(k) = <-ch")?;
        assign("a[i] <<= 2")?;
        assign("i &^= 1<<n")?;
        assign("t := x.(type)")?;
        assign("t, ok := x.(int)")?;
        assign("one, two, three = '一', '二', '三'")?;
        assign("_ = &PeerInfo{time.Now(), '1'}")?;
        assign("_ = AAA{A: 1,}")?;

        Ok(())
    }

    #[test]
    fn parse_for_stmt() -> Result<()> {
        let fors = |s| Parser::from_str(s).parse_for_stmt();

        fors("for range ch {};")?;
        fors("for x := range ch {};")?;
        fors("for _, v := range x {};")?;

        fors("for {};")?;
        fors("for loop {};")?;
        fors("for i := 0; i < 1; {};")?;
        fors("for i := 0; i < 1; i++ {};")?;

        Ok(())
    }

    #[test]
    fn parse_select_stmt() -> Result<()> {
        let select = |s| Parser::from_str(s).parse_select_stmt();

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
        let switch = |s| Parser::from_str(s).parse_switch_stmt();

        switch("switch x {}")?;
        switch("switch x;x.(type) {}")?;
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

        Ok(())
    }

    #[test]
    fn parse_if_stmt() -> Result<()> {
        let condstmt = |s| Parser::from_str(s).parse_if_stmt();

        condstmt("if a > 0 {};")?;
        condstmt("if true {{}};")?;
        condstmt("if a > 0 && yes {};")?;
        condstmt("if x := f(); x > 0 {};")?;
        condstmt("if m[struct{ int }{1}] {};")?;
        condstmt("if struct{ bool }{true}.bool {};")?;
        condstmt("if true {} else if false {} else {};")?;

        assert!(condstmt("if true {} else false {};").is_err());

        Ok(())
    }
}
