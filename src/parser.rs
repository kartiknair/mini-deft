use crate::{
    ast,
    common::Error,
    token::{Token, TokenKind},
};

#[derive(Debug, Clone)]
struct Parser<'a> {
    tokens: &'a [Token],
    current: usize,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Assoc {
    Ltr,
    Rtl,
}

#[derive(Debug, Clone, Copy)]
struct OpInfo {
    prec: u8,
    assoc: Assoc,
}

impl TokenKind {
    fn op_info(&self) -> OpInfo {
        match self {
            Self::Percent => OpInfo {
                prec: 6,
                assoc: Assoc::Ltr,
            },
            Self::Star => OpInfo {
                prec: 6,
                assoc: Assoc::Ltr,
            },
            Self::Slash => OpInfo {
                prec: 6,
                assoc: Assoc::Ltr,
            },

            Self::Plus => OpInfo {
                prec: 5,
                assoc: Assoc::Ltr,
            },
            Self::Minus => OpInfo {
                prec: 5,
                assoc: Assoc::Ltr,
            },

            Self::Lesser => OpInfo {
                prec: 4,
                assoc: Assoc::Ltr,
            },
            Self::LesserEqual => OpInfo {
                prec: 4,
                assoc: Assoc::Ltr,
            },
            Self::Greater => OpInfo {
                prec: 4,
                assoc: Assoc::Ltr,
            },
            Self::GreaterEqual => OpInfo {
                prec: 4,
                assoc: Assoc::Ltr,
            },

            Self::EqualEqual => OpInfo {
                prec: 3,
                assoc: Assoc::Ltr,
            },
            Self::BangEqual => OpInfo {
                prec: 3,
                assoc: Assoc::Ltr,
            },

            Self::AndAnd => OpInfo {
                prec: 2,
                assoc: Assoc::Ltr,
            },
            Self::OrOr => OpInfo {
                prec: 2,
                assoc: Assoc::Ltr,
            },

            Self::Equal => OpInfo {
                prec: 1,
                assoc: Assoc::Ltr,
            },

            _ => {
                panic!("`op_info()` has not been implemented for token: {:?}", self)
            }
        }
    }
}

impl<'a> Parser<'a> {
    fn new(tokens: &'a [Token]) -> Self {
        Parser { tokens, current: 0 }
    }

    fn peek(&self) -> Result<&Token, Error> {
        if let Some(token) = self.tokens.get(self.current) {
            Ok(token)
        } else {
            Err(Error {
                message: "unexpected end of file".into(),
                span: self.tokens.last().unwrap().span.clone(),
                file: None,
            })
        }
    }

    fn error_at_current(&self, message: &str) -> Error {
        Error {
            message: message.into(),
            span: {
                if let Some(token) = self.tokens.get(self.current) {
                    token.span.clone()
                } else {
                    self.tokens.last().unwrap().span.clone()
                }
            },
            file: None,
        }
    }

    fn expect(&mut self, kind: TokenKind, message: &str) -> Result<&Token, Error> {
        if let Some(token) = self.tokens.get(self.current) {
            if token.kind == kind {
                self.current += 1;
                Ok(token)
            } else {
                Err(Error {
                    message: message.into(),
                    span: token.span.clone(),
                    file: None,
                })
            }
        } else {
            Err(Error {
                message: message.into(),
                span: self.tokens.last().unwrap().span.clone(),
                file: None,
            })
        }
    }

    fn parse_block(&mut self) -> Result<ast::BlockStmt, Error> {
        self.expect(TokenKind::LeftBrace, "expect block")?;

        let mut stmts = Vec::new();
        while self.peek()?.kind != TokenKind::RightBrace {
            stmts.push(self.parse_stmt()?);
        }

        self.expect(TokenKind::RightBrace, "unclosed block")?;
        if self.peek()?.kind == TokenKind::Semicolon {
            self.current += 1; // optional trailing ';'
        }

        Ok(ast::BlockStmt { stmts })
    }

    fn parse_type(&mut self) -> Result<ast::Type, Error> {
        let mut typ = None;

        match self.peek()?.kind {
            TokenKind::Ident => {
                let ident = self.peek()?.clone();
                self.current += 1;

                if (self.current < self.tokens.len()) && self.peek()?.kind == TokenKind::Dot {
                    self.current += 1;
                    let segment = self
                        .expect(TokenKind::Ident, "expect type name after module name")?
                        .clone();

                    typ = Some(ast::Type {
                        span: ident.span.clone(),
                        kind: ast::NamedType {
                            source: Some(ident),
                            name: segment,
                        }
                        .into(),
                    });
                } else {
                    typ = Some(ast::Type {
                        span: ident.span.clone(),
                        kind: ast::NamedType {
                            source: None,
                            name: ident,
                        }
                        .into(),
                    });
                }
            }
            TokenKind::Tilde => {
                let box_type_start = self.peek()?.span.start;
                self.current += 1;

                let eltype = self.parse_type()?;
                typ = Some(ast::Type {
                    span: box_type_start..eltype.span.end,
                    kind: ast::TypeKind::Box(ast::BoxType {
                        eltype: Box::new(eltype),
                    }),
                });
            }
            TokenKind::LeftParen => {
                // Type grouping, does not get a seperate AST node but makes is
                // easier to clarify what you mean. For example to make `*int | str`
                // unambiguous you could explicitly write it as `(*int) | str` or
                // `*(int | str)`
                let grouping_start = self.peek()?.span.start;
                self.current += 1;

                let mut nested = self.parse_type()?;
                self.expect(TokenKind::RightParen, "unclosed type grouping")?;

                nested.span = grouping_start..nested.span.end;
                typ = Some(nested);
            }
            TokenKind::LeftBracket => {
                let array_type_start = self.peek()?.span.start;
                self.current += 1;

                let eltype = self.parse_type()?;
                let closing_bracket =
                    self.expect(TokenKind::RightBracket, "unclosed array type")?;

                typ = Some(ast::Type {
                    span: array_type_start..closing_bracket.span.end,
                    kind: ast::TypeKind::Arr(ast::ArrType {
                        eltype: Box::new(eltype),
                    }),
                });
            }
            _ => {}
        }

        if let Some(typ) = typ {
            Ok(typ)
        } else {
            Err(self.error_at_current("expect type"))
        }
    }

    fn parse_primary(&mut self) -> Result<ast::Expr, Error> {
        let mut expr = None;

        let token = self.peek()?.clone();

        match &token.kind {
            TokenKind::Int
            | TokenKind::Float
            | TokenKind::String
            | TokenKind::True
            | TokenKind::False => {
                self.current += 1;
                expr = Some(ast::Expr {
                    span: token.span.clone(),
                    kind: ast::Lit { token }.into(),
                    typ: None,
                })
            }
            TokenKind::LeftParen => {
                return Err(self.error_at_current("grouping expressions are not yet implemented"))
            }
            TokenKind::LeftBracket => {
                let slice_literal_start = self.current;
                self.current += 1;

                let mut elements = Vec::new();
                if self.peek()?.kind != TokenKind::RightBracket {
                    loop {
                        elements.push(self.parse_expr()?);

                        if self.peek()?.kind != TokenKind::Comma {
                            break;
                        } else {
                            self.current += 1;
                        }
                    }
                }

                let rbracket_token =
                    self.expect(TokenKind::RightBracket, "unclosed array literal")?;

                expr = Some(ast::Expr {
                    kind: ast::ArrLit { elements }.into(),
                    span: slice_literal_start..rbracket_token.span.end,
                    typ: None,
                })
            }
            TokenKind::Ident => {
                self.current += 1;

                expr = if self.peek()?.kind == TokenKind::LeftBrace {
                    Some(
                        self.parse_struct_lit(ast::Type {
                            span: token.span.clone(),
                            kind: ast::NamedType {
                                source: None,
                                name: token.clone(),
                            }
                            .into(),
                        })?,
                    )
                } else {
                    Some(ast::Expr {
                        span: token.span.clone(),
                        kind: ast::VarExpr {
                            ident: token.clone(),
                        }
                        .into(),
                        typ: None,
                    })
                };
            }
            _ if token.kind.is_prefix_op() => {
                self.current += 1;
                let target = self.parse_primary()?;
                expr = Some(ast::Expr {
                    span: token.span.clone(),
                    kind: ast::UnaryExpr {
                        op: token.clone(),
                        expr: Box::new(target),
                    }
                    .into(),
                    typ: None,
                });
            }
            _ => {}
        }

        let mut expr = if let Some(expr) = expr {
            expr
        } else {
            return Err(self.error_at_current("expected expression"));
        };

        while self.peek()?.kind == TokenKind::LeftParen
            || self.peek()?.kind == TokenKind::LeftBracket
            || self.peek()?.kind == TokenKind::As
            || self.peek()?.kind == TokenKind::Caret
            || self.peek()?.kind == TokenKind::Dot
        {
            match self.peek()?.kind {
                TokenKind::LeftParen => {
                    self.current += 1;

                    let mut args = Vec::new();
                    let mut template_inits = Vec::new();
                    if self.peek()?.kind != TokenKind::RightParen {
                        if self.peek()?.kind == TokenKind::Lesser {
                            self.current += 1;

                            while self.peek()?.kind != TokenKind::Greater {
                                template_inits.push(self.parse_type()?);

                                if self.peek()?.kind == TokenKind::Comma {
                                    self.current += 1;
                                }
                            }

                            self.expect(
                                TokenKind::Greater,
                                "expect closing '>' after template parameters",
                            )?;

                            if self.peek()?.kind == TokenKind::Comma {
                                self.current += 1;
                            }
                        }

                        while self.peek()?.kind != TokenKind::RightParen {
                            args.push(self.parse_expr()?);

                            if self.peek()?.kind == TokenKind::Comma {
                                self.current += 1;
                            }
                        }
                    }

                    let rparen_token = self.expect(
                        TokenKind::RightParen,
                        "missing closing ')' in call expression",
                    )?;

                    expr = ast::Expr {
                        span: expr.span.start..rparen_token.span.end,
                        kind: ast::CallExpr {
                            callee: Box::new(expr),
                            template_inits,
                            args,
                        }
                        .into(),
                        typ: None,
                    };
                }
                TokenKind::LeftBracket => {
                    self.current += 1;

                    let idx = self.parse_expr()?;
                    let rbracket_token = self.expect(
                        TokenKind::RightBracket,
                        "missing closing ']' in index expression",
                    )?;

                    expr = ast::Expr {
                        span: expr.span.start..rbracket_token.span.end,
                        kind: ast::IdxExpr {
                            target: Box::new(expr),
                            idx: Box::new(idx),
                        }
                        .into(),
                        typ: None,
                    };
                }
                TokenKind::As => {
                    self.current += 1;
                    let typ = self.parse_type()?;
                    expr = ast::Expr {
                        span: expr.span.start..typ.span.end,
                        kind: ast::AsExpr {
                            expr: Box::new(expr),
                            typ,
                        }
                        .into(),
                        typ: None,
                    }
                }
                TokenKind::Caret => {
                    let caret = self.peek()?.clone();
                    self.current += 1;
                    expr = ast::Expr {
                        span: expr.span.start..caret.span.end,
                        kind: ast::UnaryExpr {
                            op: caret,
                            expr: Box::new(expr),
                        }
                        .into(),
                        typ: None,
                    }
                }
                TokenKind::Dot => {
                    let dot_token = self.peek()?.clone();

                    self.current += 1;
                    let ident = self
                        .expect(
                            TokenKind::Ident,
                            "expect identifier after `.` in get expression",
                        )?
                        .clone();

                    if self.peek()?.kind == TokenKind::LeftBrace {
                        // We've actually got a `module.StructType{}` struct literal
                        expr = self.parse_struct_lit(ast::Type {
                            span: 0..0,
                            kind: ast::NamedType {
                                name: ident,
                                source: if let ast::ExprKind::Var(var_expr) = expr.kind {
                                    Some(var_expr.ident)
                                } else {
                                    unreachable!()
                                },
                            }
                            .into(),
                        })?;
                    } else {
                        expr = ast::Expr {
                            span: expr.span.start..ident.span.end,
                            kind: ast::BinaryExpr {
                                left: Box::new(expr),
                                right: Box::new(ast::Expr {
                                    span: ident.span.clone(),
                                    kind: ast::VarExpr { ident }.into(),
                                    typ: None,
                                }),
                                op: dot_token,
                            }
                            .into(),
                            typ: None,
                        }
                    }
                }
                _ => {}
            }
        }

        Ok(expr)
    }

    fn parse_struct_lit(&mut self, typ: ast::Type) -> Result<ast::Expr, Error> {
        if self.peek()?.kind == TokenKind::LeftBrace {
            self.current += 1;

            let mut inits = Vec::new();
            // let mut template_inits = Vec::new();
            while self.peek()?.kind != TokenKind::RightBrace {
                // if self.peek()?.kind == TokenKind::Lesser {
                //     self.current += 1;

                //     while self.peek()?.kind != TokenKind::Greater {
                //         template_inits.push(self.parse_type()?);

                //         if self.peek()?.kind == TokenKind::Comma {
                //             self.current += 1;
                //         }
                //     }

                //     self.expect(
                //         TokenKind::Greater,
                //         "expect closing '>' after template parameters",
                //     )?;
                // }

                let init_ident = self
                    .expect(TokenKind::Ident, "expect initializer name")?
                    .clone();
                self.expect(TokenKind::Colon, "expect ':' after initializer name")?;
                let init_expr = self.parse_expr()?;
                inits.push((init_ident, init_expr));

                if self.peek()?.kind != TokenKind::Comma {
                    break;
                } else {
                    self.current += 1;
                }
            }

            let rbrace_token = self.expect(TokenKind::RightBrace, "unclosed struct literal")?;

            Ok(ast::Expr {
                span: typ.span.start..rbrace_token.span.end,
                kind: ast::StructLit {
                    typ,
                    // template_inits,
                    inits,
                }
                .into(),
                typ: None,
            })
        } else {
            Err(self.error_at_current("expected '{' after type in struct literal"))
        }
    }

    fn parse_prec_expr(&mut self, mut lhs: ast::Expr, min_prec: u8) -> Result<ast::Expr, Error> {
        let mut lookahead = self.peek()?.clone();

        while lookahead.kind.is_binary_op() && lookahead.kind.op_info().prec >= min_prec {
            let op = lookahead;
            self.current += 1;
            let mut rhs = self.parse_primary()?;
            lookahead = self.peek()?.clone();

            while lookahead.kind.is_binary_op()
                && ((lookahead.kind.op_info().assoc == Assoc::Ltr
                    && lookahead.kind.op_info().prec > op.kind.op_info().prec)
                    || (lookahead.kind.op_info().assoc == Assoc::Rtl
                        && lookahead.kind.op_info().prec == op.kind.op_info().prec))
            {
                rhs = self.parse_prec_expr(rhs, min_prec + 1)?;
                lookahead = self.peek()?.clone();
            }

            lhs = ast::Expr {
                span: lhs.span.start..rhs.span.end,
                kind: ast::BinaryExpr {
                    op,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                }
                .into(),
                typ: None,
            };
        }

        Ok(lhs)
    }

    fn parse_expr(&mut self) -> Result<ast::Expr, Error> {
        let primary = self.parse_primary()?;
        self.parse_prec_expr(primary, 0)
    }

    fn parse_stmt(&mut self) -> Result<ast::Stmt, Error> {
        let token = self.peek()?.clone();

        match &token.kind {
            TokenKind::Extern => {
                self.current += 1;
                if self.peek()?.kind != TokenKind::Fun {
                    return Err(self.error_at_current("only function declarations can be external"));
                }

                let mut decl = self.parse_stmt()?;
                if let ast::StmtKind::Fun(fun_decl) = &mut decl.kind {
                    fun_decl.external = true;
                    if fun_decl.block.is_some() {
                        return Err(self.error_at_current("external function cannot have body"));
                    }
                    Ok(decl)
                } else {
                    panic!("internal-error: parser should have validated function declaration")
                }
            }
            TokenKind::Fun => {
                self.current += 1;

                let ident = self
                    .expect(TokenKind::Ident, "expect function name")?
                    .clone();

                let mut template_params = Vec::new();
                if self.peek()?.kind == TokenKind::Lesser {
                    self.current += 1;

                    while self.peek()?.kind != TokenKind::Greater {
                        template_params.push(
                            self.expect(TokenKind::Ident, "expect template parameter name")?
                                .clone(),
                        );

                        if self.peek()?.kind == TokenKind::Comma {
                            self.current += 1;
                        }
                    }

                    self.expect(
                        TokenKind::Greater,
                        "expect closing '>' after template parameters",
                    )?;
                }

                let mut parameters = Vec::new();
                self.expect(TokenKind::LeftParen, "expect '(' after function name")?;
                if self.peek()?.kind != TokenKind::RightParen {
                    loop {
                        let param_ident = self
                            .expect(TokenKind::Ident, "expect parameter name")?
                            .clone();
                        let param_type = self.parse_type()?;
                        parameters.push((param_ident, param_type));

                        if self.peek()?.kind != TokenKind::Comma {
                            break;
                        } else {
                            self.current += 1;
                        }
                    }
                }

                self.expect(TokenKind::RightParen, "missing closing ')'")?;

                let return_type = match self.peek()?.kind {
                    TokenKind::LeftBrace | TokenKind::Semicolon | TokenKind::For => None,
                    _ => Some(self.parse_type()?),
                };

                let target_type = if let TokenKind::For = self.peek()?.kind {
                    self.current += 1;
                    Some(self.parse_type()?)
                } else {
                    None
                };

                let block = if self.peek()?.kind == TokenKind::LeftBrace {
                    Some(self.parse_block()?)
                } else {
                    self.expect(TokenKind::Semicolon, "expect ';' after no-body function")?;
                    None
                };

                Ok(ast::Stmt {
                    kind: ast::StmtKind::Fun(ast::FunDecl {
                        exported: false,
                        external: false,
                        ident,
                        template_params,
                        parameters,
                        return_type,
                        target_type,
                        block,
                    }),
                    pointer: token.span,
                })
            }
            TokenKind::Struct => {
                self.current += 1;

                let ident = self.expect(TokenKind::Ident, "expect struct name")?.clone();

                let mut members = Vec::new();
                // let mut template_params = Vec::new();

                // if self.peek()?.kind == TokenKind::Lesser {
                //     self.current += 1;

                //     while self.peek()?.kind != TokenKind::Greater {
                //         template_params.push(
                //             self.expect(TokenKind::Ident, "expect template parameter name")?
                //                 .clone(),
                //         );

                //         if self.peek()?.kind == TokenKind::Comma {
                //             self.current += 1;
                //         }
                //     }

                //     self.expect(
                //         TokenKind::Greater,
                //         "expect closing '>' after template parameters",
                //     )?;
                // }

                self.expect(TokenKind::LeftBrace, "expect struct body")?;
                if self.peek()?.kind == TokenKind::RightBrace {
                    return Err(self.error_at_current("empty struct is illegal"));
                }

                while self.peek()?.kind != TokenKind::RightBrace {
                    let member_ident = self
                        .expect(TokenKind::Ident, "expect struct member name")?
                        .clone();
                    let member_type = self.parse_type()?;
                    self.expect(TokenKind::Semicolon, "expect ';' after struct member type")?;
                    members.push((member_ident, member_type));
                }

                self.expect(TokenKind::RightBrace, "unclosed struct body")?;

                if self.peek()?.kind == TokenKind::Semicolon {
                    self.current += 1; // optional trailing ';'
                }

                Ok(ast::Stmt {
                    kind: ast::StmtKind::Struct(ast::StructDecl {
                        exported: false,
                        ident,
                        // template_params,
                        members,
                    }),
                    pointer: token.span.clone(),
                })
            }
            TokenKind::Var => {
                self.current += 1;

                let ident = self
                    .expect(TokenKind::Ident, "expect variable name")?
                    .clone();

                let typ = if self.peek()?.kind != TokenKind::Equal {
                    Some(self.parse_type()?)
                } else {
                    None
                };
                let init = if self.peek()?.kind == TokenKind::Equal {
                    self.current += 1;
                    self.parse_expr()?
                } else {
                    return Err(self.error_at_current("expect variable initializer"));
                };

                self.expect(
                    TokenKind::Semicolon,
                    "expect ';' after variable declaration",
                )?;

                Ok(ast::Stmt {
                    kind: ast::StmtKind::Var(ast::VarStmt { ident, typ, init }),
                    pointer: token.span.clone(),
                })
            }
            TokenKind::If => {
                self.current += 1;

                let condition = self.parse_expr()?;
                let if_block = self.parse_block()?;
                let mut elif_stmts = Vec::new();
                let mut else_block = None;

                while self.peek()?.kind == TokenKind::Else {
                    self.current += 1;
                    if self.peek()?.kind == TokenKind::If {
                        if else_block.is_some() {
                            return Err(self.error_at_current("else if after final else block"));
                        }

                        self.current += 1;
                        let elif_cond = self.parse_expr()?;
                        let elif_block = self.parse_block()?;
                        elif_stmts.push((elif_cond, elif_block));
                    } else {
                        else_block = Some(self.parse_block()?);
                    }
                }

                Ok(ast::Stmt {
                    kind: ast::StmtKind::If(ast::IfStmt {
                        condition,
                        if_block,
                        elif_stmts,
                        else_block,
                    }),
                    pointer: token.span.clone(),
                })
            }
            TokenKind::While => {
                self.current += 1;

                let condition = self.parse_expr()?;
                let block = self.parse_block()?;

                Ok(ast::Stmt {
                    kind: ast::StmtKind::While(ast::WhileStmt { condition, block }),
                    pointer: token.span.clone(),
                })
            }
            TokenKind::Return => {
                self.current += 1;

                let value = if self.peek()?.kind != TokenKind::Semicolon {
                    Some(self.parse_expr()?)
                } else {
                    None
                };

                self.expect(TokenKind::Semicolon, "expect ';' after return statement")?;

                Ok(ast::Stmt {
                    kind: ast::StmtKind::Return(ast::ReturnStmt { value }),
                    pointer: token.span.clone(),
                })
            }
            TokenKind::Import => {
                self.current += 1;

                let path = self
                    .expect(TokenKind::String, "expect string with path to file")?
                    .clone();
                let alias = if self.peek()?.kind == TokenKind::Semicolon {
                    None
                } else {
                    let ident = self
                        .expect(TokenKind::Ident, "expected identifier as import alias")?
                        .clone();
                    Some(ident)
                };

                self.expect(TokenKind::Semicolon, "expect ';' after import statement")?;

                Ok(ast::Stmt {
                    kind: ast::StmtKind::Import(ast::ImportDecl { path, alias }),
                    pointer: token.span.clone(),
                })
            }
            TokenKind::Export => {
                self.current += 1;

                let mut decl = self.parse_stmt()?;
                match &mut decl.kind {
                    ast::StmtKind::Struct(struct_decl) => {
                        struct_decl.exported = true;
                        Ok(decl)
                    }
                    ast::StmtKind::Fun(fun_decl) => {
                        fun_decl.exported = true;
                        Ok(decl)
                    }
                    _ => Err(self.error_at_current("cannot export non-declaration statement")),
                }
            }
            TokenKind::LeftBrace => {
                self.current += 1;
                Ok(ast::Stmt {
                    kind: ast::StmtKind::Block(self.parse_block()?),
                    pointer: token.span.clone(),
                })
            }
            _ => {
                let expr = self.parse_expr()?;
                self.expect(
                    TokenKind::Semicolon,
                    "expect ';' after top-level expression",
                )?;

                Ok(ast::Stmt {
                    pointer: expr.span.clone(),
                    kind: ast::StmtKind::Expr(ast::ExprStmt { expr }),
                })
            }
        }
    }
}

pub fn parse(tokens: &[Token]) -> Result<Vec<ast::Stmt>, Error> {
    let mut stmts = Vec::new();

    if !tokens.is_empty() {
        let mut parser = Parser::new(tokens);
        while parser.peek()?.kind != TokenKind::Eof {
            stmts.push(parser.parse_stmt()?);
        }
    }

    Ok(stmts)
}
