use derive_more::{From, TryInto};

use crate::{common::Span, token};

#[derive(Debug, Clone)]
pub enum PrimitiveType {
    Int(u8),
    UInt(u8),
    Float(u8),
    Str,
    Bool,
}

#[derive(Debug, Clone)]
pub struct FunctionType {
    pub parameters: Vec<Type>,
    pub returns: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub members: Vec<(String, Type)>,
}

#[derive(Debug, Clone)]
pub struct PointerType {
    pub eltype: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct BoxType {
    pub eltype: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct SliceType {
    pub eltype: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct SumType {
    pub varants: Vec<Type>,
}

#[derive(Debug, Clone, From, TryInto)]
pub enum TypeKind {
    Primitive(PrimitiveType),
    Function(FunctionType),
    Struct(StructType),
    Pointer(PointerType),
    Box(BoxType),
    Slice(SliceType),
    Sum(SumType),
}

#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FunDecl {
    pub external: bool,
    pub exported: bool,
    pub ident: token::Token,
    pub parameters: Vec<(token::Token, Type)>,
    pub return_type: Type,
    pub block: BlockStmt,
}

#[derive(Debug, Clone)]
pub struct StructDecl {
    pub exported: bool,
    pub ident: token::Token,
    pub members: Vec<(token::Token, Type)>,
}

#[derive(Debug, Clone)]
pub struct ImportDecl {
    pub path: token::Token,
    pub ident: Option<token::Token>,
}

#[derive(Debug, Clone)]
pub struct VarStmt {
    pub ident: token::Token,
    pub typ: Type,
    pub init: Expr,
}

#[derive(Debug, Clone)]
pub struct IfStmt {
    pub condition: Expr,
    pub if_block: BlockStmt,
    pub else_block: Option<BlockStmt>,
}

#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub condition: Expr,
    pub block: BlockStmt,
}

#[derive(Debug, Clone)]
pub struct ReturnStmt {
    pub value: Expr,
}

#[derive(Debug, Clone)]
pub struct ExprStmt {
    pub expr: Expr,
}

#[derive(Debug, Clone)]
pub struct BlockStmt {
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Clone, From, TryInto)]
pub enum StmtKind {
    Var(VarStmt),
    If(IfStmt),
    While(WhileStmt),
    Return(ReturnStmt),
    Expr(ExprStmt),
    Block(BlockStmt),
}

#[derive(Debug, Clone)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
    pub pointer: Span,
}

#[derive(Debug, Clone)]
pub struct UnaryExpr {
    pub op: token::Token,
    pub expr: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct BinaryExpr {
    pub op: token::Token,
    pub left: Box<Expr>,
    pub right: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct VarExpr {
    pub ident: token::Token,
}

#[derive(Debug, Clone)]
pub struct CallExpr {
    pub callee: Box<Expr>,
    pub args: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct IdxExpr {
    pub target: Box<Expr>,
    pub idx: Box<Expr>,
}

#[derive(Debug, Clone)]
pub struct AsExpr {
    pub expr: Box<Expr>,
    pub target: Type,
}

#[derive(Debug, Clone)]
pub struct IsExpr {
    pub expr: Box<Expr>,
    pub typ: Type,
}

#[derive(Debug, Clone)]
pub struct StructLit {
    pub ident: token::Token,
    pub inits: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct SliceLit {
    pub exprs: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct Lit {
    pub token: token::Token,
}

#[derive(Debug, Clone, From, TryInto)]
pub enum ExprKind {
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Var(VarExpr),
    Call(CallExpr),
    Idx(IdxExpr),
    As(AsExpr),
    Is(IsExpr),
    StructLit(StructLit),
    SliceLit(SliceLit),
    Lit(Lit),
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub typ: Option<Type>,
}
