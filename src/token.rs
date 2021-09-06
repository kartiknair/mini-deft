use crate::common::Span;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd)]
pub enum TokenKind {
    String,
    Int,
    Float,
    Ident,
    Eof,

    // keywords
    Var,
    Fun,
    Return,
    Struct,
    True,
    False,
    If,
    Else,
    While,
    As,
    Is,
    Import,
    Export,
    Extern,
    Impl,

    // symbols
    LeftParen,
    RightParen,
    LeftBrace,
    RightBrace,
    LeftBracket,
    RightBracket,

    Comma,
    Dot,
    Colon,
    Caret,
    And,
    Or,
    Bang,
    Tilde,

    // binary operators
    Equal,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,

    Lesser,
    Greater,
    LesserEqual,
    GreaterEqual,
    EqualEqual,
    BangEqual,

    AndAnd,
    OrOr,

    Semicolon,
}

impl TokenKind {
    pub fn from_keyword_str(name: &str) -> Option<TokenKind> {
        match name {
            "var" => Some(TokenKind::Var),
            "fun" => Some(TokenKind::Fun),
            "return" => Some(TokenKind::Return),
            "struct" => Some(TokenKind::Struct),
            "true" => Some(TokenKind::True),
            "false" => Some(TokenKind::False),
            "if" => Some(TokenKind::If),
            "else" => Some(TokenKind::Else),
            "while" => Some(TokenKind::While),
            "as" => Some(TokenKind::As),
            "is" => Some(TokenKind::Is),
            "import" => Some(TokenKind::Import),
            "export" => Some(TokenKind::Export),
            "extern" => Some(TokenKind::Extern),
            "impl" => Some(TokenKind::Impl),
            _ => None,
        }
    }

    pub fn is_prefix_op(&self) -> bool {
        matches!(*self, Self::Minus | Self::Bang | Self::And)
    }

    pub fn is_binary_op(&self) -> bool {
        *self > Self::Equal && *self < Self::OrOr
    }

    pub fn is_comparitive_op(&self) -> bool {
        *self > Self::Lesser && *self < Self::OrOr
    }
}

#[derive(Debug, Clone)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}
