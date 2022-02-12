use std::{
    collections::HashMap,
    fs, io,
    path::{Path, PathBuf},
};

use derive_more::{From, TryInto};

use crate::{common::Span, token};

#[derive(Debug, Clone, PartialEq)]
pub enum PrimType {
    Int(u8),
    UInt(u8),
    Float(u8),
    Bool,
}

impl PrimType {
    pub fn is_numeric(&self) -> bool {
        !matches!(self, Self::Bool)
    }
}

#[derive(Debug, Clone)]
pub struct FunType {
    pub parameters: Vec<Type>,
    pub returns: Option<Box<Type>>,
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub name: String,
    pub members: Vec<(String, Type)>,
}

#[derive(Debug, Clone)]
pub struct ArrType {
    pub eltype: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct BoxType {
    pub eltype: Box<Type>,
}

// arbitrary named type. can resolve to any kind of type (currently
// only struct and primitive types, but once aliases are introduced)
#[derive(Debug, Clone)]
pub struct NamedType {
    pub source: Option<token::Token>,
    pub name: token::Token,
}

#[derive(Debug, Clone, From, TryInto)]
#[try_into(ref, ref_mut)]
pub enum TypeKind {
    Prim(PrimType),
    Fun(FunType),
    Struct(StructType),
    Box(BoxType),
    Arr(ArrType),
    Named(NamedType),
}

impl TypeKind {
    pub fn is_copyable(&self) -> bool {
        match self {
            Self::Prim(_) => true,
            Self::Fun(_) => false,
            Self::Struct(struct_type) => !struct_type
                .members
                .iter()
                .any(|(_, member_type)| !member_type.kind.is_copyable()),
            Self::Box(_) => false,
            Self::Arr(_) => false,
            Self::Named(_) => {
                panic!("Named type must be resolved before reaching `is_copyable()`.")
            }
        }
    }

    pub fn type_name(&self) -> String {
        match self {
            Self::Prim(prim_type) => match prim_type {
                PrimType::Int(bit_size) => format!("i{}", bit_size),
                PrimType::UInt(bit_size) => format!("u{}", bit_size),
                PrimType::Float(bit_size) => format!("f{}", bit_size),
                PrimType::Bool => "bool".to_string(),
            },
            Self::Struct(struct_type) => struct_type.name.clone(),
            Self::Box(box_type) => format!("box.{}", box_type.eltype.kind.type_name()),
            Self::Arr(arr_type) => format!("arr.{}", arr_type.eltype.kind.type_name()),

            Self::Fun(_) => todo!(),
            Self::Named(_) => todo!(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub span: Span,
}

#[derive(Debug, Clone)]
pub struct FunDecl {
    pub exported: bool,
    pub external: bool,
    pub ident: token::Token,
    pub parameters: Vec<(token::Token, Type)>,
    pub return_type: Option<Type>,
    pub target_type: Option<Type>,
    pub block: Option<BlockStmt>,
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
    pub alias: Option<token::Token>,
}

#[derive(Debug, Clone)]
pub struct VarStmt {
    pub ident: token::Token,
    pub typ: Option<Type>,
    pub init: Expr,
}

#[derive(Debug, Clone)]
pub struct IfStmt {
    pub condition: Expr,
    pub if_block: BlockStmt,
    pub elif_stmts: Vec<(Expr, BlockStmt)>,
    pub else_block: Option<BlockStmt>,
}

#[derive(Debug, Clone)]
pub struct WhileStmt {
    pub condition: Expr,
    pub block: BlockStmt,
}

#[derive(Debug, Clone)]
pub struct ReturnStmt {
    pub value: Option<Expr>,
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
    Fun(FunDecl),
    Struct(StructDecl),
    Import(ImportDecl),

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
pub struct IdxExpr {
    pub target: Box<Expr>,
    pub idx: Box<Expr>,
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
pub struct AsExpr {
    pub expr: Box<Expr>,
    pub typ: Type,
}

#[derive(Debug, Clone)]
pub struct StructLit {
    pub typ: Type,
    pub inits: Vec<(token::Token, Expr)>,
}

#[derive(Debug, Clone)]
pub struct ArrLit {
    pub elements: Vec<Expr>,
}

#[derive(Debug, Clone)]
pub struct Lit {
    pub token: token::Token,
}

#[derive(Debug, Clone, From, TryInto)]
pub enum ExprKind {
    Unary(UnaryExpr),
    Binary(BinaryExpr),
    Idx(IdxExpr),
    Var(VarExpr),
    Call(CallExpr),
    As(AsExpr),
    StructLit(StructLit),
    ArrLit(ArrLit),
    Lit(Lit),
}

impl ExprKind {
    pub fn is_lvalue(&self) -> bool {
        match self {
            Self::Var(_) | Self::Idx(_) => true,
            Self::Binary(binary_expr) => binary_expr.op.kind == token::TokenKind::Dot,
            _ => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
    pub typ: Option<Type>,
}

#[derive(Debug, Clone)]
pub struct File {
    pub path: PathBuf,
    pub source: String,
    pub stmts: Vec<Stmt>,
    pub direct_deps: HashMap<String, File>,
}

impl File {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self, io::Error> {
        let path = path.as_ref().to_path_buf();
        let source = fs::read_to_string(&path)?;

        Ok(Self {
            path,
            source,
            stmts: Vec::new(),
            direct_deps: HashMap::new(),
        })
    }

    pub fn id(&self) -> String {
        return self.path.components().fold(String::new(), |a, b| {
            format!("{}_{}", a, b.as_os_str().to_str().unwrap())
        });
    }

    pub fn lexeme(&self, span: &Span) -> &str {
        &self.source[span.clone()]
    }
}
