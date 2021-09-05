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
        Ok(self.create_token(
            if let Some(keyword_kind) =
                TokenKind::from_keyword_str(&lexeme.iter().collect::<String>())
            {
                keyword_kind
            } else {
                TokenKind::Ident
            },
        ))
    }

    pub fn lex_token(&mut self, prev_token: Option<&Token>) -> Result<Token, Error> {
        let c = self.peek()?;
        self.current += 1;

        let token = match c {
            '(' => Ok(self.create_token(TokenKind::LeftParen)),
            ')' => Ok(self.create_token(TokenKind::RightParen)),
            '{' => Ok(self.create_token(TokenKind::LeftBrace)),
            '}' => Ok(self.create_token(TokenKind::RightBrace)),
            '[' => Ok(self.create_token(TokenKind::LeftBracket)),
            ']' => Ok(self.create_token(TokenKind::RightBracket)),
            ',' => Ok(self.create_token(TokenKind::Comma)),
            '.' => Ok(self.create_token(TokenKind::Dot)),
            ':' => Ok(self.create_token(TokenKind::Colon)),
            '~' => Ok(self.create_token(TokenKind::Tilde)),
            '&' => {
                if self.peek()? == '&' {
                    self.advance();
                    Ok(self.create_token(TokenKind::AndAnd))
                } else {
                    Ok(self.create_token(TokenKind::And))
                }
            }
            '|' => {
                if self.peek()? == '|' {
                    self.advance();
                    Ok(self.create_token(TokenKind::OrOr))
                } else {
                    Ok(self.create_token(TokenKind::Or))
                }
            }
            '=' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(self.create_token(TokenKind::EqualEqual))
                } else {
                    Ok(self.create_token(TokenKind::Equal))
                }
            }
            '!' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(self.create_token(TokenKind::BangEqual))
                } else {
                    Ok(self.create_token(TokenKind::Bang))
                }
            }
            '<' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(self.create_token(TokenKind::LesserEqual))
                } else {
                    Ok(self.create_token(TokenKind::Lesser))
                }
            }
            '>' => {
                if self.peek()? == '=' {
                    self.advance();
                    Ok(self.create_token(TokenKind::GreaterEqual))
                } else {
                    Ok(self.create_token(TokenKind::Greater))
                }
            }
            '^' => Ok(self.create_token(TokenKind::Caret)),
            '-' => Ok(self.create_token(TokenKind::Minus)),
            '+' => Ok(self.create_token(TokenKind::Plus)),
            '*' => Ok(self.create_token(TokenKind::Star)),
            '%' => Ok(self.create_token(TokenKind::Percent)),

            '/' => {
                if self.peek()? == '/' {
                    self.advance();
                    while !self.at_end() && self.peek()? != '\n' {
                        self.advance();
                    }

                    if self.at_end() {
                        Ok(self.create_token(TokenKind::Eof))
                    } else {
                        self.lex_token(prev_token)
                    }
                } else {
                    Ok(self.create_token(TokenKind::Slash))
                }
            }

            ';' => Ok(self.create_token(TokenKind::Semicolon)),

            '"' => self.lex_string(),

            _ if c.is_whitespace() => {
                if self.at_end() {
                    Ok(self.create_token(TokenKind::Eof))
                } else {
                    self.lex_token(prev_token)
                }
            }

            _ => {
                if c.is_digit(10) {
                    self.lex_number()
                } else if c.is_alphabetic() {
                    self.lex_ident()
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
        tokens.push(lexer.lex_token(tokens.last())?)
    }

    Ok(tokens)
}
