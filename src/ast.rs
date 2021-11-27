use std::{
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
pub struct PtrType {
    pub eltype: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct BoxType {
    pub eltype: Box<Type>,
}

#[derive(Debug, Clone)]
pub struct SumType {
    pub variants: Vec<Type>,
}

#[derive(Debug, Clone)]
pub struct IfaceType {
    pub name: String,
    pub methods: Vec<(String, FunType)>,
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
    Sum(SumType),
    Iface(IfaceType),
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
            Self::Sum(_) => false,
            Self::Iface(_) => false,
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
            Self::Iface(iface_type) => iface_type.name.clone(),
            Self::Struct(struct_type) => struct_type.name.clone(),
            Self::Fun(_) => todo!(),
            Self::Box(_) => todo!(),
            Self::Sum(_) => todo!(),
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
pub struct IsExpr {
    pub expr: Box<Expr>,
    pub typ: Type,
}

#[derive(Debug, Clone)]
pub struct StructLit {
    pub typ: Type,
    pub inits: Vec<(token::Token, Expr)>,
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
    As(AsExpr),
    Is(IsExpr),
    StructLit(StructLit),
    Lit(Lit),
}

impl ExprKind {
    pub fn is_lvalue(&self) -> bool {
        match self {
            Self::Var(_) => true,
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
}

impl File {
    pub fn new<P: AsRef<Path>>(path: P) -> Result<Self, io::Error> {
        let path = path.as_ref().to_path_buf();
        let source = fs::read_to_string(&path)?;

        Ok(Self {
            path,
            source,
            stmts: Vec::new(),
        })
    }

    pub fn exports(&self) -> Vec<&Stmt> {
        self.stmts
            .iter()
            .filter(|stmt| match &stmt.kind {
                StmtKind::Fun(fun_decl) => fun_decl.exported,
                StmtKind::Struct(struct_decl) => struct_decl.exported,
                _ => false,
            })
            .collect()
    }

    pub fn imports(&self) -> Vec<&Stmt> {
        self.stmts
            .iter()
            .filter(|stmt| matches!(&stmt.kind, StmtKind::Import(_)))
            .collect()
    }

    #[allow(dead_code)]
    pub fn exports_mut(&mut self) -> Vec<&mut Stmt> {
        self.stmts
            .iter_mut()
            .filter(|stmt| match &stmt.kind {
                StmtKind::Fun(fun_decl) => fun_decl.exported,
                StmtKind::Struct(struct_decl) => struct_decl.exported,
                _ => false,
            })
            .collect()
    }

    #[allow(dead_code)]
    pub fn imports_mut(&mut self) -> Vec<&mut Stmt> {
        self.stmts
            .iter_mut()
            .filter(|stmt| matches!(&stmt.kind, StmtKind::Import(_)))
            .collect()
    }

    pub fn lexeme(&self, span: &Span) -> &str {
        &self.source[span.clone()]
    }
}
