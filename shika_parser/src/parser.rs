use crate::ast;
use crate::ast::ChanMode;
use crate::ast::{BasicLit, ChannelType, Declaration};
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

    fn expect<K: IntoKind>(&mut self, expect: K) -> Result<usize> {
        if let Some((pos, tok)) = &self.current {
            if tok.kind() == expect.into() {
                let pos = pos.clone();
                self.next()?;
                return Ok(pos);
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
            .ok_or(self.else_error("unexpected EOF"))
    }

    fn current_kind(&self) -> TokenKind {
        self.current.as_ref().expect("unexpected EOF").1.kind()
    }

    fn current_pos(&self) -> usize {
        self.current.as_ref().map(|(pos, _)| *pos).unwrap_or(0)
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

        let mut vars = vec![];
        let mut types = vec![];
        let mut consts = vec![];
        let mut funcs = vec![];

        loop {
            self.skipped(Operator::SemiColon)?;
            let (_, tok) = self.get_current()?;
            match tok {
                token::VAR => vars.push(self.parse_decl(Parser::parse_var_spec)),
                token::TYPE => types.push(self.parse_decl(Parser::parse_type_sepc)),
                token::CONST => consts.push(self.parse_decl(Parser::parse_const_sepc)),
                token::FUNC => funcs.push(self.parse_func_decl()?),
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

    fn parse_decl<T, F: FnMut(&mut Parser) -> Result<T>>(
        &mut self,
        mut parse_spec: F,
    ) -> Result<Declaration<T>> {
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
            return Ok(Declaration { pos0, specs, pos1 });
        }

        let pos1 = None;
        specs.push(parse_spec(self)?);
        self.skipped(Operator::SemiColon)?;
        Ok(Declaration { pos0, specs, pos1 })
    }

    fn parse_func_decl(&mut self) -> Result<ast::FuncDecl> {
        self.expect(Keyword::Func)?;
        let name = self.parse_ident()?;
        let params = self.parse_func_signature()?;

        Ok(ast::FuncDecl { name, params })
    }

    #[allow(dead_code)]
    fn parse_block(&mut self) -> Result<ast::Block> {
        let pos0 = self.expect(Operator::BraceLeft)?;
        let pos1 = self.expect(Operator::BarackRight)?;
        let pos = (pos0, pos1);
        Ok(ast::Block { pos })
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

        let pos = self.current_pos();
        let value_count = spec.values.len();
        match value_count {
            0 => Ok(spec),
            _ => match value_count.cmp(&spec.name.len()) {
                std::cmp::Ordering::Equal => Ok(spec),
                std::cmp::Ordering::Less => Err(self.else_error_at(pos, "mission init expression")),
                std::cmp::Ordering::Greater => {
                    Err(self.else_error_at(pos, "extra init expression"))
                }
            },
        }
    }

    fn parse_const_sepc(&mut self) -> Result<ast::ConstSpec> {
        let mut spec = ast::ConstSpec::default();
        spec.name = self.parse_ident_list()?;
        match self.skipped(Operator::Assign)? {
            true => spec.values = self.parse_expr_list()?,
            false => {
                if self.current_is(TokenKind::Literal(LitKind::Ident)) {
                    spec.typ = Some(self.parse_type()?);
                    self.expect(Operator::Assign)?;
                    spec.values = self.parse_expr_list()?;
                }
            }
        }

        let pos = self.current_pos();
        let value_count = spec.values.len();
        match value_count {
            0 => Ok(spec),
            _ => match value_count.cmp(&spec.name.len()) {
                std::cmp::Ordering::Equal => Ok(spec),
                std::cmp::Ordering::Less => Err(self.else_error_at(pos, "mission init expression")),
                std::cmp::Ordering::Greater => {
                    Err(self.else_error_at(pos, "extra init expression"))
                }
            },
        }
    }

    fn parse_type_sepc(&mut self) -> Result<ast::TypeSpec> {
        Ok(ast::TypeSpec {
            docs: vec![],
            name: self.parse_ident()?,
            alias: self.skipped(Operator::Assign)?,
            typ: self.parse_type()?,
        })
    }

    pub fn parse_type(&mut self) -> Result<ast::Type> {
        let (pos, tok) = self.get_current()?;
        match tok {
            Token::Literal(LitKind::Ident, _) => {
                let name = self.parse_type_name()?;
                Ok(ast::Type::Ident(name))
            }
            token::FUNC => self.parse_func_type(),
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
                if self.skipped(Operator::BarackRight)? {
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

    fn parse_interface_type(&mut self) -> Result<ast::Type> {
        let mut methods = vec![];
        self.expect(Keyword::Interface)?;

        let pos1 = self.expect(Operator::BraceLeft)?;
        while !self.current_is(Operator::BraceRight) {
            let id = self.parse_type_name()?;
            methods.push(
                if id.pkg.is_some() || !self.current_is(Operator::ParenLeft) {
                    ast::InterfaceElem::Embed(id)
                } else {
                    let (input, output) = self.parse_func_signature()?;
                    ast::InterfaceElem::Method {
                        name: id.name,
                        input,
                        output,
                    }
                },
            )
        }

        let pos = (pos1, self.expect(Operator::BraceRight)?);
        Ok(ast::InterfaceType { pos, methods }.into())
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

            self.skipped(Operator::SemiColon)?;
            fields.push(ast::Field { name, typ, tag })
        }

        let pos2 = self.expect(Operator::BraceRight)?;
        Ok(ast::StructType {
            fields,
            pos: (pos1, pos2),
        })
    }

    fn parse_embed_field(&mut self) -> Result<ast::Type> {
        let pos = self.current_pos();
        let star = self.skipped(Operator::Star)?;
        let type_name = self.parse_type_name()?;
        Ok(match star {
            false => ast::Type::Ident(type_name),
            true => ast::PointerType {
                pos,
                typ: Box::new(type_name.into()),
            }
            .into(),
        })
    }

    fn parse_array_len(&mut self) -> Result<ast::Expression> {
        let pos = self.current_pos();
        match self.skipped(Operator::Ellipsis)? {
            true => Ok(ast::Ellipsis { pos }.into()),
            false => self.parse_expr(),
        }
    }

    fn parse_expr_list(&mut self) -> Result<Vec<ast::Expression>> {
        let mut result = vec![self.parse_expr()?];
        while self.skipped(Operator::Comma)? {
            result.push(self.parse_expr()?);
        }

        Ok(result)
    }

    pub fn parse_expr(&mut self) -> Result<ast::Expression> {
        self.parse_binary_expr(1)
    }

    fn parse_binary_expr(&mut self, prec: usize) -> Result<ast::Expression> {
        let mut expr = self.parse_unary_expr()?;
        while let Some((perc1, op)) = self.current.as_ref().and_then(|(_, tok)| match tok {
            Token::Operator(op) => (op.precedence() >= prec).then_some((op.precedence(), *op)),
            _ => None,
        }) {
            expr = ast::BinaryExpression {
                op,
                pos: self.expect(op)?,
                left: Box::new(expr),
                right: Box::new(self.parse_binary_expr(perc1 + 1)?),
            }
            .into()
        }

        Ok(expr)
    }

    fn parse_unary_expr(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current()?;
        Ok(match tok {
            Token::Operator(
                op
                @ (Operator::Add | Operator::Sub | Operator::Not | Operator::Xor | Operator::And),
            ) => {
                self.next()?;
                let right = Box::new(self.parse_unary_expr()?);
                ast::UnaryExpression { pos, op, right }.into()
            }
            token::ARROW => {
                // channel type or receive expression
                // (<-chan int)(x) | <- message
                self.next()?;
                let expr = self.parse_unary_expr()?;
                let expr2 = expr.clone();
                if let Ok(typ) = expr2.try_into().and_then(|t: ast::Type| t.try_into()) {
                    let chan_type = self.reset_chan_arrow(pos, typ);
                    return Ok(ast::Type::Channel(chan_type?).into());
                }

                let op = Operator::Arrow;
                let right = Box::new(expr);
                ast::UnaryExpression { pos, op, right }.into()
            }
            token::STAR => {
                self.next()?;
                let right = Box::new(self.parse_unary_expr()?);
                ast::StarExpression { pos, right }.into()
            }
            _ => self.parse_primary_expr()?.into(),
        })
    }

    /// reset the channel direction of expression `<- typ` (typ is a channel type)
    fn reset_chan_arrow(&mut self, pos: usize, mut typ: ChannelType) -> Result<ast::ChannelType> {
        match typ.dir {
            Some(ast::ChanMode::Recv) => {
                // <- <-chan T
                Err(self.unexpected(vec![Keyword::Chan], Some((typ.pos.1, token::ARROW))))
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
                        typ.typ = Box::new(self.reset_chan_arrow(typ.pos.1, chan_type)?.into());
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

    fn parse_operand_right(&mut self, left: ast::Expression) -> Result<(ast::Expression, bool)> {
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
                            let right = self
                                .skipped(Keyword::Type)?
                                .then(|| self.parse_type())
                                .map_or(Ok(None), |r| r.map(Some))?;
                            ast::TypeAssertion { right, left }.into()
                        }
                        _ => {
                            return Err(self.unexpected(
                                vec![token::KIND_IDENT, token::KIND_LPAREN],
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
                            let index = index[0].to_owned().expect("index should't be empty");
                            ast::Index { pos, left, index }.into()
                        }
                        false => ast::Slice { pos, left, index }.into(),
                    },
                    true,
                ))
            }
            token::LPAREN => {
                self.next()?;
                let mut args = vec![];
                while !self.current_is(Operator::ParenRight) && !self.current_is(Operator::Ellipsis)
                {
                    args.push(self.parse_expr()?);
                }

                let pos2 = self
                    .current_is(Operator::Ellipsis)
                    .then_some(self.current_pos())
                    .unwrap_or(0);

                let pos1 = self.expect(Operator::ParenRight)?;
                let pos = (pos, pos1, pos2);
                Ok((ast::Call { pos, args, left }.into(), true))
            }
            token::LBRACE => {
                // TODO: check { belongs to block statement
                let typ = left;
                let val = self.parse_lit_value()?;
                Ok((ast::CompositeLit { typ, val }.into(), true))
            }
            _ => Ok((*left, false)),
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

    /// follow by https://go.dev/ref/spec#Operands
    /// an operand may be a literal, ident, function or expression
    fn parse_operand(&mut self) -> Result<ast::Expression> {
        let (pos, tok) = self.get_current()?;
        Ok(match tok {
            Token::Keyword(Keyword::Func) => self.parse_func_lit()?.into(),
            Token::Literal(LitKind::Ident, _) => self.parse_type_name()?.into(),
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

    fn parse_lit_value(&mut self) -> Result<ast::LiteralValue> {
        let mut values = vec![];
        let pos0 = self.expect(Operator::BraceLeft)?;
        if !self.current_is(Operator::BraceRight) {
            values.push(self.parse_element()?);
        }

        while !self.current_is(Operator::BraceRight) {
            self.expect(Operator::Comma)?;
            values.push(self.parse_element()?);
        }

        self.skipped(Operator::Comma)?;
        let pos1 = self.expect(Operator::BraceRight)?;
        let pos = (pos0, pos1);
        Ok(ast::LiteralValue { pos, values })
    }

    fn parse_element_value(&mut self) -> Result<ast::Element> {
        self.current_is(Operator::BraceLeft)
            .then(|| self.parse_lit_value().map(ast::Element::from))
            .or_else(|| Some(self.parse_expr().map(ast::Element::from)))
            .unwrap()
    }

    fn parse_element(&mut self) -> Result<ast::KeyedElement> {
        let key = self.parse_element_value()?;
        match self.skipped(Operator::Colon)? {
            true => {
                let key = Some(key);
                let val = self.parse_element_value()?;
                Ok(ast::KeyedElement { key, val })
            }
            false => Ok(ast::KeyedElement {
                key: None,
                val: key,
            }),
        }
    }

    fn parse_func_type(&mut self) -> Result<ast::Type> {
        let pos = self.expect(Keyword::Func)?;
        let (input, output) = self.parse_func_signature()?;
        Ok(ast::FunctionType { pos, input, output }.into())
    }

    /// function literal is an anonymous function
    fn parse_func_lit(&mut self) -> Result<ast::FunctionLit> {
        self.expect(Keyword::Func)?;
        let (input, output) = self.parse_func_signature()?;
        self.current_is(Operator::BraceLeft)
            .then(|| self.parse_func_body());

        Ok(ast::FunctionLit { input, output })
    }

    fn parse_func_body(&self) {
        unimplemented!()
    }

    fn parse_func_signature(&mut self) -> Result<(Vec<ast::Params>, Vec<ast::Params>)> {
        let input = self.parse_params_list(true)?;
        let output = match self.current {
            None | Some((_, Token::Operator(Operator::SemiColon))) => vec![],
            Some((_, Token::Operator(Operator::ParenLeft))) => self.parse_params_list(false)?,
            _ => vec![ast::Params {
                name: Vec::new(),
                typ: (Box::new(self.parse_type()?), false),
            }],
        };

        Ok((input, output))
    }

    /// parse params list like  
    /// `(a, b int, c bool, d int...)`
    fn parse_params_list(&mut self, is_in: bool) -> Result<Vec<ast::Params>> {
        let mut params = vec![];
        self.expect(Operator::ParenLeft)?;
        while !self.current_is(Operator::ParenRight) {
            params.extend(self.parse_param_decl()?);
            self.skipped(Operator::Comma)?;
        }

        let named = params.first().map_or_else(|| false, |p| p.name.len() > 0);
        self.expect(Operator::ParenRight)?;
        for (index, param) in params.iter().enumerate() {
            if param.typ.1 && (!is_in || index != params.len() - 1) {
                // TODO: locate the type position
                return Err(self.else_error("can only use ... with final parameter in list"));
            }

            if (param.name.len() > 0) != named {
                return Err(self.else_error("mixed named and unnamed parameters"));
            }
        }

        Ok(params)
    }

    /// parse a group params with same type, or a ident type list
    /// return when ensure one type
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
                            let name = self.parse_ident()?;
                            let pkg = ident_list.pop();

                            let mut typ_list = ident_list
                                .into_iter()
                                .map(|id| ast::Params {
                                    name: Vec::new(),
                                    typ: (Box::new(id.into()), false),
                                })
                                .collect::<Vec<_>>();
                            typ_list.push(ast::Params {
                                name: Vec::new(),
                                typ: (Box::new((ast::TypeName { pkg, name }).into()), false),
                            });
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
                                .map(|id| ast::Params {
                                    name: Vec::new(),
                                    typ: (Box::new(ast::Type::Ident(id.into())), false),
                                })
                                .collect::<Vec<_>>();

                            // T1, ...T2 | T1, *T2
                            let ellipsis = self.skipped(Operator::Ellipsis)?;
                            type_list.push(ast::Params {
                                name: Vec::new(),
                                typ: (Box::new(self.parse_type()?), ellipsis),
                            });
                            return Ok(type_list);
                        }
                        // a, b ...?
                        (_, Token::Operator(Operator::Ellipsis)) => {
                            self.next()?;
                            return Ok(vec![ast::Params {
                                name: ident_list,
                                typ: (Box::new(self.parse_type()?), true),
                            }]);
                        }
                        // a, b)
                        (_, Token::Operator(Operator::ParenRight)) => {
                            return Ok(ident_list
                                .into_iter()
                                .map(|id| ast::Params {
                                    name: Vec::new(),
                                    typ: (Box::new(ast::Type::Ident(id.into())), false),
                                })
                                .collect::<Vec<_>>())
                        }
                        // a, b func... | a, b struct...
                        _ => {
                            let typ = Box::new(self.parse_type()?);
                            return Ok(vec![ast::Params {
                                name: ident_list,
                                typ: (typ, false),
                            }]);
                        }
                    }
                }
            }
            // (...T)
            Token::Operator(Operator::Ellipsis) => {
                self.next()?;
                Ok(vec![ast::Params {
                    name: Vec::new(),
                    typ: (Box::new(self.parse_type()?), true),
                }])
            }
            // ()
            Token::Operator(Operator::ParenRight) => Ok(vec![]),
            _ => Ok(vec![ast::Params {
                name: Vec::new(),
                typ: (Box::new(self.parse_type()?), false),
            }]),
        }
    }
}

#[cfg(test)]
mod test {
    use std::assert_matches::assert_matches;

    use crate::ast::{ChanMode, ChannelType, Type};
    use crate::parser::Parser;

    #[test]
    fn parse_const() {
        let consts =
            |s| Parser::from_str(format!("const {}", s)).parse_decl(Parser::parse_const_sepc);

        assert!(consts("a = 1").is_ok());
        assert!(consts("a, b, c").is_ok());
        assert!(consts("(a; b; c)").is_ok());
        assert!(consts("a int64 = 1").is_ok());
        assert!(consts("a, b int64 = 1, 2").is_ok());
        assert!(consts("(a = iota; b, c;)").is_ok());
        assert!(consts("(a = 1; b, c = 2, 3)").is_ok());

        assert!(consts("a int64;").is_err());
        assert!(consts("(a = 1; b int; c = 3)").is_err());
    }

    #[test]
    fn parse_var() {
        let vars = |s| Parser::from_str(format!("var {}", s)).parse_decl(Parser::parse_var_spec);

        assert!(vars("a int").is_ok());
        assert!(vars("a = 1").is_ok());
        assert!(vars("a, b int").is_ok());
        assert!(vars("a, b = 1, 2").is_ok());
        assert!(vars("a, b int = 1, 2").is_ok());
        assert!(vars("(a = 1; b int = 2)").is_ok());
        assert!(vars("(a int; b, c int = 2, 3; e, f = 5, 6)").is_ok());

        assert!(vars("a, b;").is_err());
    }

    #[test]
    fn parse_expr() {
        let expr = |s| Parser::from_str(s).parse_expr();

        assert!(expr("struct{}").is_ok());
        assert!(expr("struct{}").is_ok());
        assert!(expr("<-chan chan int").is_ok());
        assert!(expr("<-chan chan<- int").is_ok());
        assert!(expr("<-chan <-chan <-chan int").is_ok());

        println!("{:#?}", expr("a + b"));
        println!("{:#?}", expr("a + b * c + d"));
        println!("{:#?}", expr("a * b + c * d"));

        assert!(expr("a + b").is_ok());
        assert!(expr("a + b * c + d").is_ok());
        assert!(expr("a * b + c * d").is_ok());

        assert!(expr("<-chan <-chan <- int").is_err());
    }

    #[test]
    fn parse_operand() {
        let operand = |s| Parser::from_str(s).parse_operand();

        assert!(operand("a.b").is_ok());
        assert!(operand("`Hola`").is_ok());
        assert!(operand("[10]string{}").is_ok());
        assert!(operand("[6]int{1, 2, 3, 5}").is_ok());
        assert!(operand("[...]string{`Sat`, `Sun`}").is_ok());
        assert!(operand("[][]Point{{{0, 1}, {1, 2}}}").is_ok());
        assert!(operand("[...]Point{{1.5, -3.5}, {0, 0}}").is_ok());
        assert!(operand("map[string]Point{`orig`: {0, 0}}").is_ok());
        assert!(operand("map[Point]string{{0, 0}: `orig`}").is_ok());
    }

    #[test]
    fn parse_slice_index() {
        let slice = |s| Parser::from_str(s).parse_slice();

        assert!(slice("[a]").is_ok());
        assert!(slice("[:]").is_ok());
        assert!(slice("[a:]").is_ok());
        assert!(slice("[:a]").is_ok());
        assert!(slice("[a:b]").is_ok());
        assert!(slice("[:a:b]").is_ok());
        assert!(slice("[a:b:c]").is_ok());

        assert!(slice("[]").is_err());
        assert!(slice("[::]").is_err());
        assert!(slice("[a::b]").is_err());
        assert!(slice("[a:b:]").is_err());
    }

    #[test]
    fn parse_interface_type() {
        let face = |s| Parser::from_str(s).parse_interface_type();

        assert!(face("interface{}").is_ok());
        assert!(face("interface{Close() error}").is_ok());
        assert!(face("interface{Show(int) string}").is_ok());
        assert!(face("interface{Show(...int) string}").is_ok());
    }

    #[test]
    fn parse_struct_type() {
        let suct = |s| Parser::from_str(s).parse_struct_type();

        assert!(suct("struct {}").is_ok());
        assert!(suct("struct {T1}").is_ok());
        assert!(suct("struct {*T2}").is_ok());
        assert!(suct("struct {P.T3}").is_ok());
        assert!(suct("struct {*P.T4}").is_ok());
        assert!(suct("struct {A *[]int}").is_ok());
        assert!(suct("struct {x, y int}").is_ok());
        assert!(suct("struct {u float32}").is_ok());
        assert!(suct("struct {_ float32}").is_ok());
        assert!(suct("struct {a int; b bool}").is_ok());
        assert!(suct("struct {a int\nb bool}").is_ok());
        assert!(suct("struct {a int ``; b bool}").is_ok());
        assert!(suct("struct {microsec  uint64 `protobuf:\"1\"`}").is_ok());

        assert!(suct("struct {*[]a}").is_err());
        assert!(suct("struct {**T2}").is_err());
        assert!(suct("struct {a _}").is_err());
        assert!(suct("struct {a, b}").is_err());
        assert!(suct("struct {a ...int}").is_err());
        assert!(suct("struct {a, b int, bool}").is_err());
    }

    #[test]
    fn parse_func_type() {
        let func = |s| Parser::from_str(s).parse_func_type();

        assert!(func("func()").is_ok());
        assert!(func("func(x int) int").is_ok());
        assert!(func("func(a, _ int, z float32) bool").is_ok());
        assert!(func("func(a, b int, z float32) (bool)").is_ok());
        assert!(func("func(prefix string, values ...int)").is_ok());
        assert!(func("func(int, int, float64) (float64, *[]int)").is_ok());
        assert!(func("func(int, int, float64) (*a, []b, map[c]d)").is_ok());
        assert!(func("func(n int) func(p *T)").is_ok());

        assert!(func("func(...int").is_err());
        assert!(func("func() (...int)").is_err());
        assert!(func("func(a int, bool)").is_err());
        assert!(func("func(int) (...bool, int)").is_err());
    }

    #[test]
    fn parse_param_list() {
        let params = |s| Parser::from_str(s).parse_params_list(true);

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

        let ret_params = |s| Parser::from_str(s).parse_params_list(false);

        assert!(ret_params("(int)").is_ok());
        assert!(ret_params("(a int)").is_ok());
        assert!(ret_params("(int, bool)").is_ok());
        assert!(ret_params("(a int, b bool)").is_ok());

        assert!(ret_params("(...bool)").is_err());
        assert!(ret_params("(a int, bool)").is_err());
        assert!(ret_params("(...bool, int)").is_err());
    }

    #[test]
    fn parse_type() {
        let type_of = |x| Parser::from_str(x).parse_type().ok();

        assert_matches!(type_of("int"), Some(Type::Ident(_)));
        assert_matches!(type_of("int"), Some(Type::Ident(_)));
        assert_matches!(type_of("((int))"), Some(Type::Ident(_)));
        assert_matches!(type_of("a.b;"), Some(Type::Ident(..)));
        assert_matches!(type_of("[]int;"), Some(Type::Slice(..)));
        assert_matches!(type_of("map[int]map[int]int;"), Some(Type::Map(..)));

        assert_matches!(type_of("chan int;"), Some(Type::Channel(..)));

        assert_matches!(
            type_of("<-chan <- chan int;"),
            Some(Type::Channel(ChannelType {
                dir: Some(ChanMode::Recv),
                ..
            }))
        );

        assert_matches!(
            type_of("chan<- int;"),
            Some(Type::Channel(ChannelType {
                dir: Some(ChanMode::Send),
                ..
            }))
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
