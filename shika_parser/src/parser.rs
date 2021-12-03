use crate::ast;
use crate::ast::BasicLit;
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
                let dir = self.skipped(Operator::Arrow)?.then_some(ChanMode::Send);
                let typ = Box::new(self.parse_type()?);
                Ok(ast::ChannelType { pos, dir, typ }.into())
            }
            token::ARROW => {
                self.next()?;
                let dir = Some(ChanMode::Recv);
                let typ = Box::new(self.parse_type()?);
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

        let pos2 = self.expect(Operator::BraceRight)?;
        Ok(ast::InterfaceType {
            pos: (pos1, pos2),
            methods,
        }
        .into())
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
                _ => (vec![], self.parse_embeded_field()?),
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

    fn parse_embeded_field(&mut self) -> Result<ast::Type> {
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

    pub fn parse_expr(&mut self) -> Result<ast::Expression> {
        self.parse_binary_expr()
    }

    fn parse_binary_expr(&mut self) -> Result<ast::Expression> {
        self.parse_unary_expr()
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
                let _expr = self.parse_unary_expr()?;

                // TODO: handle <- chan int(nil)
                unimplemented!()
            }
            token::STAR => {
                self.next()?;
                let right = Box::new(self.parse_unary_expr()?);
                ast::StarExpression { pos, right }.into()
            }
            _ => self.parse_primary_expr()?.into(),
        })
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
    fn parse_expr() {
        let expr = |s| Parser::from_str(s).parse_expr();

        assert!(expr("struct{}").is_ok());
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
