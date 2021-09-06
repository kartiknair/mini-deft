use crate::{
    common::{Error, Span},
    token::{Token, TokenKind},
};

#[derive(Debug, Clone)]
struct Lexer {
    source: Vec<char>,

    start: usize,
    current: usize,
    line: usize,
    line_begin: usize,
}

impl Lexer {
    pub fn from_str(source: &str) -> Self {
        Lexer {
            source: source.chars().collect(),
            start: 0,
            current: 0,
            line: 1,
            line_begin: 0,
        }
    }

    fn at_end(&mut self) -> bool {
        self.current >= self.source.len()
    }

    fn advance(&mut self) {
        self.current += 1;
    }

    fn get_span(&self) -> Span {
        self.start..self.current
    }

    fn create_token(&mut self, kind: TokenKind) -> Token {
        Token {
            kind,
            span: self.get_span(),
        }
    }

    fn peek(&mut self) -> Result<char, Error> {
        if let Some(c) = self.source.get(self.current) {
            Ok(*c)
        } else {
            Err(Error {
                message: "unexpected end of file".into(),
                span: self.get_span(),
            })
        }
    }

    fn lex_string(&mut self) -> Result<Token, Error> {
        while !self.at_end() && self.peek()? != '"' {
            if self.peek()? == '\n' {
                return Err(Error {
                    message: "strings must be on a single line".into(),
                    span: self.get_span(),
                });
            }

            self.advance();
        }

        if self.at_end() {
            return Err(Error {
                message: "unterminated string literal".into(),
                span: self.get_span(),
            });
        }

        self.advance(); // skip the closing: "
        Ok(self.create_token(TokenKind::String))
    }

    fn lex_number(&mut self) -> Result<Token, Error> {
        let radix = 10;
        let mut token_kind = TokenKind::Int;

        while !self.at_end() && self.peek()?.is_digit(radix) {
            self.advance()
        }

        if !self.at_end() && self.peek()? == '.' {
            self.current += 1;
            if self.peek()?.is_digit(radix) {
                token_kind = TokenKind::Float;
                while !self.at_end() && self.peek()?.is_digit(radix) {
                    self.advance()
                }
            } else {
                self.current -= 1;
            }
        }

        Ok(self.create_token(token_kind))
    }

    fn lex_ident(&mut self) -> Result<Token, Error> {
        while !self.at_end() && self.peek()?.is_alphanumeric() {
            self.advance();
        }

        let lexeme = &self.source[self.start..self.current];
        let keyword_str = lexeme.iter().collect::<String>();

        let token = self.create_token(
            if let Some(keyword_kind) = TokenKind::from_keyword_str(&keyword_str) {
                keyword_kind
            } else {
                TokenKind::Ident
            },
        );

        Ok(token)
    }

    pub fn lex_token(&mut self, prev_token: Option<&Token>) -> Result<Option<Token>, Error> {
        let c = self.peek()?;
        self.current += 1;

        let token = match c {
            '(' => Ok(Some(self.create_token(TokenKind::LeftParen))),
            ')' => Ok(Some(self.create_token(TokenKind::RightParen))),
            '{' => Ok(Some(self.create_token(TokenKind::LeftBrace))),
            '}' => Ok(Some(self.create_token(TokenKind::RightBrace))),
            '[' => Ok(Some(self.create_token(TokenKind::LeftBracket))),
            ']' => Ok(Some(self.create_token(TokenKind::RightBracket))),
            ',' => Ok(Some(self.create_token(TokenKind::Comma))),
            '.' => Ok(Some(self.create_token(TokenKind::Dot))),
            ':' => Ok(Some(self.create_token(TokenKind::Colon))),
            '~' => Ok(Some(self.create_token(TokenKind::Tilde))),
            '&' => {
                if self.peek()? == '&' {
                    self.advance();
                    Ok(Some(self.create_token(TokenKind::AndAnd)))
                } else {
                    Ok(Some(self.create_token(TokenKind::And)))
                }
            }
            '|' => {
                if self.peek()? == '|' {
                    self.advance();
                    Ok(Some(self.create_token(TokenKind::OrOr)))
                } else {
                    Ok(Some(self.create_token(TokenKind::Or)))
                }
            }
            '=' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(Some(self.create_token(TokenKind::EqualEqual)))
                } else {
                    Ok(Some(self.create_token(TokenKind::Equal)))
                }
            }
            '!' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(Some(self.create_token(TokenKind::BangEqual)))
                } else {
                    Ok(Some(self.create_token(TokenKind::Bang)))
                }
            }
            '<' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(Some(self.create_token(TokenKind::LesserEqual)))
                } else {
                    Ok(Some(self.create_token(TokenKind::Lesser)))
                }
            }
            '>' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(Some(self.create_token(TokenKind::GreaterEqual)))
                } else {
                    Ok(Some(self.create_token(TokenKind::Greater)))
                }
            }
            '^' => Ok(Some(self.create_token(TokenKind::Caret))),
            '-' => Ok(Some(self.create_token(TokenKind::Minus))),
            '+' => Ok(Some(self.create_token(TokenKind::Plus))),
            '*' => Ok(Some(self.create_token(TokenKind::Star))),
            '%' => Ok(Some(self.create_token(TokenKind::Percent))),

            '/' => {
                if self.peek()? == '/' {
                    self.advance();
                    while !self.at_end() && self.peek()? != '\n' {
                        self.advance();
                    }
                    Ok(None)
                } else {
                    Ok(Some(self.create_token(TokenKind::Slash)))
                }
            }

            ';' => Ok(Some(self.create_token(TokenKind::Semicolon))),

            '"' => Ok(Some(self.lex_string()?)),

            '\n' => {
                if let Some(prev_token) = prev_token {
                    if prev_token.kind != TokenKind::Semicolon
                        && (prev_token.kind == TokenKind::Ident
                            || prev_token.kind == TokenKind::RightParen
                            || prev_token.kind == TokenKind::RightBrace
                            || prev_token.kind == TokenKind::RightBracket
                            || prev_token.kind == TokenKind::Return
                            || prev_token.kind == TokenKind::Int
                            || prev_token.kind == TokenKind::Float
                            || prev_token.kind == TokenKind::True
                            || prev_token.kind == TokenKind::False
                            || prev_token.kind == TokenKind::Caret
                            || prev_token.kind == TokenKind::String)
                    {
                        Ok(Some(self.create_token(TokenKind::Semicolon)))
                    } else {
                        Ok(None)
                    }
                } else {
                    Ok(None)
                }
            }

            _ if c.is_whitespace() => {
                if self.at_end() {
                    Ok(Some(self.create_token(TokenKind::Eof)))
                } else {
                    Ok(None)
                }
            }

            _ => {
                if c.is_digit(10) {
                    Ok(Some(self.lex_number()?))
                } else if c.is_alphabetic() {
                    Ok(Some(self.lex_ident()?))
                } else {
                    Err(Error {
                        message: "unexpected character".into(),
                        span: self.get_span(),
                    })
                }
            }
        };

        self.start = self.current;
        token
    }
}

pub fn lex(source: &str) -> Result<Vec<Token>, Error> {
    let mut lexer = Lexer::from_str(source);
    let mut tokens = Vec::new();

    while !lexer.at_end() {
        if let Some(token) = lexer.lex_token(tokens.last())? {
            tokens.push(token)
        }
    }

    Ok(tokens)
}
