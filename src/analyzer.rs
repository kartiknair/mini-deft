use std::{
    borrow::Borrow, collections::HashMap, convert::TryInto, mem::discriminant, ops::Deref,
    path::Path,
};

use crate::{ast, common::Error, lexer, parser, token};

#[derive(Debug)]
struct TypeInfo {
    kind: ast::TypeKind,
    methods: HashMap<String, ast::FunType>,
    public: bool,
}

impl TypeInfo {
    fn new(type_kind: ast::TypeKind) -> Self {
        Self {
            kind: type_kind,
            methods: HashMap::new(),
            public: false,
        }
    }

    fn new_public(type_kind: ast::TypeKind) -> Self {
        Self {
            kind: type_kind,
            methods: HashMap::new(),
            public: true,
        }
    }
}

#[derive(Debug)]
struct Analyzer<'a> {
    file: &'a mut ast::File,
    namespace: HashMap<String, ast::Type>,
    typespace: HashMap<String, TypeInfo>,
    imports: HashMap<String, ast::File>,

    within_function: Option<ast::FunDecl>,
}

impl<'a> Analyzer<'a> {
    fn new(file: &'a mut ast::File) -> Self {
        let mut typespace = HashMap::new();

        typespace.insert(
            "i8".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::Int(8))),
        );
        typespace.insert(
            "i16".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::Int(16))),
        );
        typespace.insert(
            "i32".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::Int(32))),
        );
        typespace.insert(
            "i64".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::Int(64))),
        );

        typespace.insert(
            "u8".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::UInt(8))),
        );
        typespace.insert(
            "u16".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::UInt(16))),
        );
        typespace.insert(
            "u32".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::UInt(32))),
        );
        typespace.insert(
            "u64".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::UInt(64))),
        );

        typespace.insert(
            "f32".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::Float(32))),
        );
        typespace.insert(
            "f64".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::Float(64))),
        );

        typespace.insert(
            "bool".to_string(),
            TypeInfo::new_public(ast::TypeKind::Prim(ast::PrimType::Bool)),
        );

        Self {
            file,
            namespace: HashMap::new(),
            typespace,
            imports: HashMap::new(),

            within_function: None,
        }
    }

    fn type_eq(&self, left: &ast::Type, right: &ast::Type) -> bool {
        if discriminant(&left.kind) != discriminant(&right.kind) {
            return false;
        }

        match &left.kind {
            ast::TypeKind::Prim(left_prim_type) => {
                let right_prim_type: &ast::PrimType = right.kind.borrow().try_into().unwrap();
                left_prim_type == right_prim_type
            }
            ast::TypeKind::Struct(left_struct_type) => {
                let right_struct_type: &ast::StructType = right.kind.borrow().try_into().unwrap();
                left_struct_type.name == right_struct_type.name
            }
            ast::TypeKind::Arr(left_arr_type) => {
                let right_arr_type: &ast::ArrType = right.kind.borrow().try_into().unwrap();
                self.type_eq(&left_arr_type.eltype, &right_arr_type.eltype)
            }
            ast::TypeKind::Box(left_box_type) => {
                let right_box_type: &ast::BoxType = right.kind.borrow().try_into().unwrap();
                self.type_eq(&left_box_type.eltype, &right_box_type.eltype)
            }
            _ => {
                panic!(
                    "Type equality has not been implemented for kind: {:?}",
                    left.kind
                );
            }
        }
    }

    fn analyze_type(&self, typ: &mut ast::Type) -> Result<(), Error> {
        match &mut typ.kind {
            ast::TypeKind::Box(box_type) => {
                self.analyze_type(&mut box_type.eltype)?;
            }
            ast::TypeKind::Arr(arr_type) => {
                self.analyze_type(&mut arr_type.eltype)?;
            }
            ast::TypeKind::Named(named_type) => {
                if let Some(resolved_type_info) = self
                    .typespace
                    .get(&self.name_from_named_type(None, named_type))
                {
                    typ.kind = resolved_type_info.kind.clone();
                } else {
                    return Err(Error {
                        message: "unknown named type".into(),
                        span: named_type.name.span.clone(),
                        file: None,
                    });
                }
            }
            _ => todo!(),
        }

        Ok(())
    }

    fn name_from_named_type(
        &self,
        file: Option<&ast::File>,
        named_type: &ast::NamedType,
    ) -> String {
        let file = if let Some(file) = file {
            file
        } else {
            &self.file
        };
        let lexeme = file.lexeme(&named_type.name.span);

        if let Some(type_info) = self.typespace.get(lexeme) {
            if let ast::TypeKind::Prim(_) = &type_info.kind {
                // Primitives are shared accross files
                return lexeme.to_string();
            }
        }

        format!(
            "{}.{}",
            if let Some(module_ident) = &named_type.source {
                file.direct_deps
                    .get(file.lexeme(&module_ident.span))
                    .unwrap()
                    .id()
            } else {
                file.id()
            },
            lexeme,
        )
    }

    fn analyze_stmt(&mut self, stmt: &mut ast::Stmt) -> Result<(), Error> {
        match &mut stmt.kind {
            ast::StmtKind::Import(_) => {
                // Nothing to do
            }
            ast::StmtKind::Fun(fun_decl) => {
                if self.within_function.is_some() {
                    return Err(fun_decl
                        .ident
                        .error_at("nested functions have not yet been implemented"));
                }

                let function_name = self.file.lexeme(&fun_decl.ident.span);
                self.within_function = Some(fun_decl.clone());

                if let Some(return_type) = &mut fun_decl.return_type {
                    self.analyze_type(return_type)?;
                }

                let mut shadowed = HashMap::new();
                for param in fun_decl.parameters.iter_mut() {
                    if let ast::TypeKind::Named(named_type) = &param.1.kind {
                        if let Some(typ_info) = self
                            .typespace
                            .get(&self.name_from_named_type(None, named_type))
                        {
                            if !typ_info.public && fun_decl.exported {
                                return Err(param
                                    .0
                                    .error_at("cannot use private type in exported function"));
                            }
                        } // let the else error be handled by the analyze_type() below instead
                    }

                    self.analyze_type(&mut param.1)?;

                    if self.file.lexeme(&param.0.span) == function_name {
                        return Err(param
                            .0
                            .error_at("parameter name cannot be same as function name"));
                    } else if self.file.lexeme(&param.0.span) == "self" {
                        return Err(param.0.error_at("parameter name cannot be `self`"));
                    }

                    if let Some(old_value) = self
                        .namespace
                        .insert(self.file.lexeme(&param.0.span).to_string(), param.1.clone())
                    {
                        shadowed.insert(self.file.lexeme(&param.0.span).to_string(), old_value);
                    }
                }

                if let Some(target_type) = &mut fun_decl.target_type {
                    if let ast::TypeKind::Named(named_type) = &target_type.kind {
                        let type_name = self.name_from_named_type(None, named_type);
                        let resolved_type_info = match self.typespace.get_mut(&type_name) {
                            Some(typ_info) => typ_info,
                            None => {
                                return Err(Error {
                                    span: target_type.span.clone(),
                                    message: format!("undefined type: '{}'", type_name),
                                    file: None,
                                });
                            }
                        };

                        resolved_type_info.methods.insert(
                            function_name.to_string(),
                            ast::FunType {
                                parameters: fun_decl
                                    .parameters
                                    .iter()
                                    .map(|(_, typ)| typ.clone())
                                    .collect(),
                                returns: fun_decl
                                    .return_type
                                    .as_ref()
                                    .map(|return_type| Box::new(return_type.clone())),
                            },
                        );

                        self.analyze_type(target_type)?;
                        self.namespace
                            .insert("self".to_string(), target_type.clone());
                    } else {
                        return Err(Error{
                            span: target_type.span.clone(),
                            message: "methods can only be defined on named types. consider introducing a new type".to_string(),
                            file: None,
                        });
                    }
                } else {
                    self.namespace.insert(
                        function_name.to_string(),
                        ast::Type {
                            span: 0..0,
                            kind: ast::TypeKind::Fun(ast::FunType {
                                parameters: fun_decl
                                    .parameters
                                    .iter()
                                    .map(|(_, typ)| typ.clone())
                                    .collect(),
                                returns: fun_decl
                                    .return_type
                                    .as_ref()
                                    .map(|return_type| Box::new(return_type.clone())),
                            }),
                        },
                    );
                }

                self.within_function = Some(fun_decl.clone());

                if let Some(block) = &mut fun_decl.block {
                    for stmt in block.stmts.iter_mut() {
                        self.analyze_stmt(stmt)?;
                    }
                } else if !fun_decl.external {
                    return Err(fun_decl
                        .ident
                        .error_at("missing block in function declaration"));
                }

                for param in fun_decl.parameters.iter_mut() {
                    self.namespace.remove(self.file.lexeme(&param.0.span));
                }
                for (name, typ) in shadowed {
                    self.namespace.insert(name, typ);
                }

                self.within_function = None;
            }
            ast::StmtKind::Struct(struct_decl) => {
                // Validate the struct declaration and add it to the namespace
                for member in struct_decl.members.iter_mut() {
                    if let ast::TypeKind::Named(named_type) = &member.1.kind {
                        if let Some(typ_info) = self
                            .typespace
                            .get(&self.name_from_named_type(None, named_type))
                        {
                            if !typ_info.public && struct_decl.exported {
                                return Err(member
                                    .0
                                    .error_at("cannot use private type in exported struct type"));
                            }
                        } // let the else error be handled by the analyze_type() below instead
                    }

                    self.analyze_type(&mut member.1)?;
                }

                let struct_id = format!(
                    "{}.{}",
                    self.file.id(),
                    self.file.lexeme(&struct_decl.ident.span)
                );

                let struct_type = ast::StructType {
                    name: self.file.lexeme(&struct_decl.ident.span).to_string(),
                    file_id: self.file.id(),
                    members: struct_decl
                        .members
                        .iter()
                        .map(|(ident, typ)| (self.file.lexeme(&ident.span).into(), typ.clone()))
                        .collect(),
                };

                self.typespace.insert(
                    struct_id,
                    TypeInfo {
                        kind: ast::TypeKind::Struct(struct_type),
                        methods: HashMap::new(),
                        public: struct_decl.exported,
                    },
                );
            }

            ast::StmtKind::Var(var_stmt) => {
                if let Some(typ) = &mut var_stmt.typ {
                    // e.g. var x int = 32
                    self.analyze_expr(&mut var_stmt.init)?;
                    self.analyze_type(typ)?;
                    if !self.is_assignable(&var_stmt.init, typ, false)? {
                        return Err(Error {
                            message: "variable initializer is not assignable to provided type"
                                .into(),
                            span: var_stmt.init.span.clone(),
                            file: None,
                        });
                    }
                } else {
                    // e.g. var x = 34
                    self.analyze_expr(&mut var_stmt.init)?;
                    if !var_stmt.init.typ.as_ref().unwrap().kind.is_copyable()
                        && var_stmt.init.kind.is_lvalue()
                    {
                        return Err(Error {
                            message: "variable initializer is not copyable. use an explicit copy operation"
                                .into(),
                            span: var_stmt.init.span.clone(),
                            file: None,
                        });
                    }
                    var_stmt.typ = var_stmt.init.typ.clone();
                }

                if let Some(var_type) = &var_stmt.typ {
                    if self
                        .namespace
                        .get(self.file.lexeme(&var_stmt.ident.span))
                        .is_some()
                    {
                        return Err(var_stmt.ident.error_at("redefinition of variable"));
                    } else if self
                        .file
                        .direct_deps
                        .get(self.file.lexeme(&var_stmt.ident.span))
                        .is_some()
                    {
                        return Err(var_stmt
                            .ident
                            .error_at("cannot define variable with same name as imported module"));
                    }

                    self.namespace.insert(
                        self.file.lexeme(&var_stmt.ident.span).to_string(),
                        var_type.clone(),
                    );
                } else {
                    panic!("internal-error: could not get type for variable declaration")
                }
            }
            ast::StmtKind::If(if_stmt) => {
                self.analyze_expr(&mut if_stmt.condition)?;

                if let Some(cond_type) = &if_stmt.condition.typ {
                    if let ast::TypeKind::Prim(ast::PrimType::Bool) = cond_type.kind {
                        for stmt in if_stmt.if_block.stmts.iter_mut() {
                            self.analyze_stmt(stmt)?;
                        }

                        for (elif_cond, elif_block) in if_stmt.elif_stmts.iter_mut() {
                            self.analyze_expr(elif_cond)?;
                            if let Some(cond_type) = &elif_cond.typ {
                                if let ast::TypeKind::Prim(ast::PrimType::Bool) = cond_type.kind {
                                    for stmt in elif_block.stmts.iter_mut() {
                                        self.analyze_stmt(stmt)?;
                                    }
                                }
                            } else {
                                return Err(Error {
                                    span: if_stmt.condition.span.clone(),
                                    message: "void expression cannot be used as else if condition"
                                        .into(),
                                    file: None,
                                });
                            }
                        }

                        if let Some(else_block) = &mut if_stmt.else_block {
                            for stmt in else_block.stmts.iter_mut() {
                                self.analyze_stmt(stmt)?;
                            }
                        }
                    } else {
                        return Err(Error {
                            span: if_stmt.condition.span.clone(),
                            message: "if statement condition must be a boolean".into(),
                            file: None,
                        });
                    }
                } else {
                    return Err(Error {
                        span: if_stmt.condition.span.clone(),
                        message: "void expression cannot be used as if statement condition".into(),
                        file: None,
                    });
                }
            }
            ast::StmtKind::While(while_stmt) => {
                self.analyze_expr(&mut while_stmt.condition)?;
                if let Some(typ) = &while_stmt.condition.typ {
                    if let ast::TypeKind::Prim(ast::PrimType::Bool) = &typ.kind {
                        for stmt in while_stmt.block.stmts.iter_mut() {
                            self.analyze_stmt(stmt)?;
                        }
                        return Ok(());
                    }

                    return Err(Error {
                        message: "while condition must be of boolean type".into(),
                        span: while_stmt.condition.span.clone(),
                        file: None,
                    });
                } else {
                    return Err(Error {
                        message: "cannot use void expression as while condition".into(),
                        span: while_stmt.condition.span.clone(),
                        file: None,
                    });
                }
            }
            ast::StmtKind::Return(return_stmt) => {
                if let Some(value) = &mut return_stmt.value {
                    self.analyze_expr(value)?;
                }

                if let Some(current_func) = &self.within_function {
                    if let Some(value) = &mut return_stmt.value {
                        if let Some(return_type) = &current_func.return_type {
                            if !self.is_assignable(value, return_type, true)? {
                                return Err(Error {
                                    message: "return value is not assignable to return type".into(),
                                    span: value.span.clone(),
                                    file: None,
                                });
                            }
                        } else {
                            return Err(Error {
                                message: "returning value in void function".into(),
                                span: value.span.clone(),
                                file: None,
                            });
                        }
                    } else if current_func.return_type.is_some() {
                        return Err(Error {
                            message: "void return in function with return type".into(),
                            span: stmt.pointer.clone(),
                            file: None,
                        });
                    }
                } else {
                    return Err(Error {
                        message: "return statement must be inside function".into(),
                        span: stmt.pointer.clone(),
                        file: None,
                    });
                }
            }
            ast::StmtKind::Expr(expr_stmt) => {
                self.analyze_expr(&mut expr_stmt.expr)?;
            }
            ast::StmtKind::Block(block) => {
                for stmt in block.stmts.iter_mut() {
                    self.analyze_stmt(stmt)?;
                }
            }
        }

        Ok(())
    }

    fn is_assignable(
        &self,
        expr: &ast::Expr,
        target_type: &ast::Type,
        allow_lvalue: bool,
    ) -> Result<bool, Error> {
        if let Some(expr_type) = &expr.typ {
            if expr.kind.is_lvalue() && !target_type.kind.is_copyable() && !allow_lvalue {
                Ok(false)
            } else {
                let is_same_type = self.type_eq(expr_type, target_type);
                if !is_same_type {
                    if let ast::TypeKind::Prim(expr_prim_type) = &expr_type.kind {
                        if let ast::TypeKind::Prim(target_prim_type) = &target_type.kind {
                            match (&target_prim_type, &expr_prim_type) {
                                (
                                    ast::PrimType::UInt(target_bit_size),
                                    ast::PrimType::UInt(expr_bit_size),
                                )
                                | (
                                    ast::PrimType::Int(target_bit_size),
                                    ast::PrimType::Int(expr_bit_size),
                                )
                                | (
                                    ast::PrimType::Float(target_bit_size),
                                    ast::PrimType::Int(expr_bit_size),
                                ) => return Ok(expr_bit_size < target_bit_size),
                                _ => {}
                            }
                        }
                    }
                }

                Ok(is_same_type)
            }
        } else {
            Err(Error {
                span: expr.span.clone(),
                message: "unexpected void expression".into(),
                file: None,
            })
        }
    }

    fn analyze_expr(&mut self, expr: &mut ast::Expr) -> Result<(), Error> {
        match &mut expr.kind {
            ast::ExprKind::Unary(unary_expr) => {
                self.analyze_expr(&mut unary_expr.expr)?;
                if let Some(expr_type) = &mut unary_expr.expr.typ {
                    match &unary_expr.op.kind {
                        token::TokenKind::Minus => {
                            if let ast::TypeKind::Prim(prim_type) = &expr_type.kind {
                                if prim_type.is_numeric() {
                                    expr.typ = Some(expr_type.clone());
                                    return Ok(());
                                }
                            }

                            return Err(Error {
                                message: "unary negate is only valid on numeric expressions".into(),
                                span: expr.span.clone(),
                                file: None,
                            });
                        }
                        token::TokenKind::Bang => {
                            if let ast::TypeKind::Prim(ast::PrimType::Bool) = &expr_type.kind {
                                expr.typ = Some(ast::Type {
                                    kind: ast::TypeKind::Prim(ast::PrimType::Bool),
                                    span: 0..0,
                                });
                                return Ok(());
                            }

                            return Err(Error {
                                message: "unary not is only valid on boolean expressions".into(),
                                span: expr.span.clone(),
                                file: None,
                            });
                        }
                        token::TokenKind::Tilde => {
                            expr.typ = Some(ast::Type {
                                kind: ast::BoxType {
                                    eltype: Box::new(expr_type.clone()),
                                }
                                .into(),
                                span: 0..0,
                            });
                        }
                        token::TokenKind::Caret => {
                            if let ast::TypeKind::Box(box_type) = &expr_type.kind {
                                expr.typ = Some(box_type.eltype.deref().clone());
                                return Ok(());
                            }

                            return Err(Error {
                                message: "operator '^' is only valid on box expressions".into(),
                                span: expr.span.clone(),
                                file: None,
                            });
                        }
                        token::TokenKind::Copy => {
                            if expr_type.kind.is_copyable() {
                                return Err(Error {
                                    message: "unrequired copy on copyable type".into(),
                                    span: expr.span.clone(),
                                    file: None,
                                });
                            }

                            expr.typ = Some(expr_type.clone());
                        }
                        _ => {
                            panic!(
                                "Analysis has not been implemented for unary operator: {:?}",
                                unary_expr.op.kind
                            )
                        }
                    }
                } else {
                    return Err(Error {
                        message: "unary expression cannot be done on void expression".into(),
                        span: expr.span.clone(),
                        file: None,
                    });
                }
            }
            ast::ExprKind::Binary(binary_expr) => {
                if let token::TokenKind::Dot = &binary_expr.op.kind {
                    if let ast::ExprKind::Var(left_var_expr) = &binary_expr.left.kind {
                        if self
                            .file
                            .direct_deps
                            .get(self.file.lexeme(&left_var_expr.ident.span))
                            .is_some()
                        {
                            // Left of '.' is a module type ident
                            if let ast::ExprKind::Var(right_var_expr) = &binary_expr.right.kind {
                                expr.typ = Some(
                                    match self.namespace.get(&format!(
                                        "{}.{}",
                                        self.file.lexeme(&left_var_expr.ident.span),
                                        self.file.lexeme(&right_var_expr.ident.span)
                                    )) {
                                        Some(typ) => typ.clone(),
                                        None => {
                                            return Err(Error {
                                                message: format!(
                                                    "module: '{}' doesnot export member: '{}'",
                                                    self.file.lexeme(&left_var_expr.ident.span),
                                                    self.file.lexeme(&right_var_expr.ident.span)
                                                ),
                                                span: binary_expr.right.span.clone(),
                                                file: None,
                                            });
                                        }
                                    },
                                );

                                return Ok(());
                            } else {
                                return Err(Error {
                                    message:
                                        "operator '.' can only have an identifier on it's right"
                                            .to_string(),
                                    span: binary_expr.right.span.clone(),
                                    file: None,
                                });
                            }
                        }
                    }

                    self.analyze_expr(&mut binary_expr.left)?;

                    if let ast::ExprKind::Var(var_expr) = &binary_expr.right.kind {
                        let member_name = self.file.lexeme(&var_expr.ident.span);

                        let type_name = if let ast::TypeKind::Struct(struct_type) =
                            &binary_expr.left.typ.as_ref().unwrap().kind
                        {
                            format!("{}.{}", &struct_type.file_id, &struct_type.name,)
                        } else {
                            binary_expr.left.typ.as_ref().unwrap().kind.type_name()
                        };

                        if let Some(type_info) = self.typespace.get(&type_name) {
                            if let Some(method_type) = type_info.methods.get(member_name) {
                                expr.typ = Some(ast::Type {
                                    kind: method_type.clone().into(),
                                    span: 0..0,
                                });
                                return Ok(());
                            }
                        }

                        if let Some(target_type) = &binary_expr.left.typ {
                            if let ast::TypeKind::Struct(struct_type) = &target_type.kind {
                                let found_member = struct_type
                                    .members
                                    .iter()
                                    .find(|(type_member_name, _)| type_member_name == member_name);

                                if let Some(found_member) = found_member {
                                    expr.typ = Some(found_member.1.clone());
                                } else {
                                    return Err(Error {
                                        message: format!(
                                            "field '{}' does not exist on struct type: '{}'",
                                            member_name, struct_type.name
                                        ),
                                        span: binary_expr.left.span.clone(),
                                        file: None,
                                    });
                                }
                            } else {
                                return Err(Error {
                                    message:
                                        "operator '.' must have struct type expression on left"
                                            .to_string(),
                                    span: binary_expr.left.span.clone(),
                                    file: None,
                                });
                            }
                        } else {
                            return Err(Error {
                                message: "operator '.' cannot have void expression on left"
                                    .to_string(),
                                span: binary_expr.left.span.clone(),
                                file: None,
                            });
                        }
                    } else {
                        return Err(Error {
                            message: "operator '.' can only have an identifier on it's right"
                                .to_string(),
                            span: binary_expr.right.span.clone(),
                            file: None,
                        });
                    }
                } else {
                    self.analyze_expr(&mut binary_expr.left)?;
                    self.analyze_expr(&mut binary_expr.right)?;

                    if let Some(left_expr_type) = &binary_expr.left.typ {
                        if let Some(right_expr_type) = &binary_expr.right.typ {
                            if !self.type_eq(right_expr_type, left_expr_type) {
                                return Err(Error {
                                    message: "binary expressions must have the same type expression on both sides".into(),
                                    span: expr.span.clone(),
                                    file: None,
                                });
                            }

                            if let ast::TypeKind::Prim(prim_type) = &left_expr_type.kind {
                                match &binary_expr.op.kind {
                                    token::TokenKind::Equal => {
                                        if !binary_expr.left.kind.is_lvalue() {
                                            return Err(Error {
                                                message: "left of assignment can only be variable or get expression".into(),
                                                span: binary_expr.left.span.clone(),
                                                file: None,
                                            });
                                        }
                                        expr.typ = Some(left_expr_type.clone());
                                    }

                                    token::TokenKind::Plus
                                    | token::TokenKind::Minus
                                    | token::TokenKind::Star
                                    | token::TokenKind::Slash
                                    | token::TokenKind::Percent => {
                                        if !prim_type.is_numeric() {
                                            return Err(Error {
                                                message:
                                                    "binary expressions are only valid on primitive numeric operands"
                                                        .into(),
                                                span: expr.span.clone(),
                                                file: None,
                                            });
                                        }

                                        expr.typ = Some(left_expr_type.clone());
                                    }
                                    token::TokenKind::Lesser
                                    | token::TokenKind::Greater
                                    | token::TokenKind::LesserEqual
                                    | token::TokenKind::GreaterEqual
                                    | token::TokenKind::EqualEqual
                                    | token::TokenKind::BangEqual => {
                                        expr.typ = Some(ast::Type {
                                            span: 0..0,
                                            kind: ast::TypeKind::Prim(ast::PrimType::Bool),
                                        });
                                    }
                                    token::TokenKind::AndAnd | token::TokenKind::OrOr => {
                                        if !matches!(prim_type, ast::PrimType::Bool) {
                                            return Err(Error {
                                                message:
                                                    "operator `&&` & `||` can only be used with boolean operands"
                                                        .into(),
                                                span: expr.span.clone(),
                                                file: None,
                                            });
                                        }
                                    }
                                    _ => unreachable!(),
                                }
                            }
                        }
                    } else {
                        return Err(Error {
                            message: "cannot use void expression in a binary expression".into(),
                            span: expr.span.clone(),
                            file: None,
                        });
                    }
                }
            }
            ast::ExprKind::Var(var_expr) => {
                let var_name = self.file.lexeme(&var_expr.ident.span);
                if let Some(var_type) = self.namespace.get(var_name) {
                    expr.typ = Some(var_type.clone());
                } else {
                    return Err(Error {
                        message: "undefined variable".into(),
                        span: expr.span.clone(),
                        file: None,
                    });
                }
            }
            ast::ExprKind::Call(call_expr) => {
                self.analyze_expr(&mut call_expr.callee)?;
                for arg in call_expr.args.iter_mut() {
                    self.analyze_expr(arg)?;
                }

                if let Some(callee_type) = &call_expr.callee.typ {
                    if let ast::TypeKind::Fun(fun_type) = &callee_type.kind {
                        // Validate arguments
                        for (i, arg) in call_expr.args.iter().enumerate() {
                            if arg.typ.is_some() {
                                let param_type = &fun_type.parameters[i];
                                if !self.is_assignable(arg, param_type, true)? {
                                    return Err(Error {
                                        message: "invalid argument type".into(),
                                        span: arg.span.clone(),
                                        file: None,
                                    });
                                }
                            } else {
                                return Err(Error {
                                    message: "cannot use void expression as function argument"
                                        .into(),
                                    span: call_expr.callee.span.clone(),
                                    file: None,
                                });
                            }
                        }

                        expr.typ = fun_type
                            .returns
                            .as_ref()
                            .map(|return_type| (**return_type).clone());
                    } else {
                        return Err(Error {
                            message: "callee must be of function type".into(),
                            span: call_expr.callee.span.clone(),
                            file: None,
                        });
                    }
                } else {
                    return Err(Error {
                        message: "cannot call void expression".into(),
                        span: call_expr.callee.span.clone(),
                        file: None,
                    });
                }
            }
            ast::ExprKind::As(as_expr) => {
                self.analyze_expr(&mut as_expr.expr)?;
                self.analyze_type(&mut as_expr.typ)?;

                if let Some(expr_type) = &as_expr.expr.typ {
                    if let ast::TypeKind::Prim(prim_type) = &expr_type.kind {
                        if prim_type.is_numeric() {
                            expr.typ = Some(as_expr.typ.clone());
                        } else {
                            return Err(Error {
                                message: "cannot cast non-numeric primitive expression".into(),
                                span: as_expr.expr.span.clone(),
                                file: None,
                            });
                        }
                    } else {
                        return Err(Error {
                            message: "can only cast numeric primitives or sum type values".into(),
                            span: as_expr.expr.span.clone(),
                            file: None,
                        });
                    }
                } else {
                    return Err(Error {
                        message: "cannot cast void expression".into(),
                        span: as_expr.expr.span.clone(),
                        file: None,
                    });
                }
            }
            ast::ExprKind::StructLit(struct_lit) => {
                self.analyze_type(&mut struct_lit.typ)?;

                if let ast::TypeKind::Struct(struct_type) = &struct_lit.typ.kind {
                    if struct_lit.inits.len() != struct_type.members.len() {
                        return Err(Error {
                            message: "incorrect number of initializers".into(),
                            span: expr.span.clone(),
                            file: None,
                        });
                    }

                    for (init_ident, init_expr) in struct_lit.inits.iter_mut() {
                        let found_member_type = if let Some(found_member) =
                            struct_type.members.iter().find(|(member_name, _)| {
                                self.file.lexeme(&init_ident.span) == member_name
                            }) {
                            Some(&found_member.1)
                        } else {
                            None
                        };

                        self.analyze_expr(init_expr)?;
                        if let Some(found_member_type) = found_member_type {
                            if !self.is_assignable(init_expr, found_member_type, false)? {
                                return Err(Error {
                                    message: "invalid initializer for member in struct literal"
                                        .into(),
                                    span: init_ident.span.clone(),
                                    file: None,
                                });
                            }
                        } else {
                            return Err(Error {
                                message: format!(
                                    "struct type has no member named: '{}'",
                                    self.file.lexeme(&init_ident.span)
                                ),
                                span: init_ident.span.clone(),
                                file: None,
                            });
                        }
                    }

                    expr.typ = Some(struct_lit.typ.clone());
                } else {
                    return Err(Error {
                        message: "struct literal must use struct type".into(),
                        span: struct_lit.typ.span.clone(),
                        file: None,
                    });
                }
            }
            ast::ExprKind::ArrLit(arr_lit) => {
                let mut eltype = None;

                if arr_lit.elements.is_empty() {
                    return Ok(()); // we give this a void type and handle the error later one
                }

                for expr in arr_lit.elements.iter_mut() {
                    self.analyze_expr(expr)?;
                    if expr.typ.is_none() {
                        return Err(Error {
                            message: "cannot use void expression as array literal element".into(),
                            span: expr.span.clone(),
                            file: None,
                        });
                    }
                }

                for expr in arr_lit.elements.iter_mut() {
                    if let Some(eltype) = &eltype {
                        if !self.is_assignable(expr, &eltype, false)? {
                            return Err(Error {
                                message: "cannot infer type of empty array literal".into(),
                                span: expr.span.clone(),
                                file: None,
                            });
                        }
                    } else {
                        eltype = Some(expr.typ.as_ref().unwrap().clone());
                    }
                }

                expr.typ = Some(ast::Type {
                    kind: ast::ArrType {
                        eltype: Box::new(eltype.unwrap()),
                    }
                    .into(),
                    span: 0..0,
                });
            }
            ast::ExprKind::Idx(idx_expr) => {
                self.analyze_expr(&mut idx_expr.target)?;
                self.analyze_expr(&mut idx_expr.idx)?;

                if let Some(target_type) = &idx_expr.target.typ {
                    if let ast::TypeKind::Arr(arr_type) = &target_type.kind {
                        expr.typ = Some((*arr_type.eltype).clone())
                    } else {
                        return Err(Error {
                            message: "index target has non-array type".into(),
                            span: idx_expr.target.span.clone(),
                            file: None,
                        });
                    }
                } else {
                    return Err(Error {
                        message: "cannot index void expression".into(),
                        span: idx_expr.target.span.clone(),
                        file: None,
                    });
                }
            }
            ast::ExprKind::Lit(lit) => {
                expr.typ = Some(match &lit.token.kind {
                    token::TokenKind::Int => ast::Type {
                        span: 0..0,
                        kind: ast::TypeKind::Prim(ast::PrimType::Int(32)),
                    },
                    token::TokenKind::Float => ast::Type {
                        span: 0..0,
                        kind: ast::TypeKind::Prim(ast::PrimType::Float(64)),
                    },
                    token::TokenKind::True => ast::Type {
                        span: 0..0,
                        kind: ast::TypeKind::Prim(ast::PrimType::Bool),
                    },
                    token::TokenKind::False => ast::Type {
                        span: 0..0,
                        kind: ast::TypeKind::Prim(ast::PrimType::Bool),
                    },
                    token::TokenKind::String => ast::Type {
                        span: 0..0,
                        kind: ast::ArrType {
                            eltype: Box::new(ast::Type {
                                span: 0..0,
                                kind: ast::PrimType::UInt(8).into(),
                            }),
                        }
                        .into(),
                    },
                    _ => {
                        panic!(
                            "Analysis has not yet been implemented for literal: {:?}",
                            lit.token.kind
                        )
                    }
                });
            }
        }
        Ok(())
    }

    fn analyze(&mut self) -> Result<HashMap<String, ast::File>, Error> {
        // Validate that there is only one import of a file

        for stmt in &self.file.stmts {
            if let ast::StmtKind::Import(import_decl) = &stmt.kind {
                let import_name = if let Some(alias) = &import_decl.alias {
                    self.file.lexeme(&alias.span).to_string()
                } else {
                    let import_path = Path::new(self.file.lexeme(
                        &((import_decl.path.span.start + 1)..(import_decl.path.span.end - 1)),
                    ));
                    import_path
                        .file_stem()
                        .unwrap()
                        .to_str()
                        .unwrap()
                        .to_string()
                };

                if self.file.direct_deps.get(&import_name).is_some() {
                    return Err(Error {
                        span: stmt.pointer.clone(),
                        message: "re-importing previously imported module".into(),
                        file: None,
                    });
                }

                let import_path = {
                    let mut dir_path = self.file.path.clone();
                    dir_path.pop();
                    dir_path.push(
                        &self.file.lexeme(&import_decl.path.span)
                            [1..self.file.lexeme(&import_decl.path.span).len() - 1],
                    );
                    dir_path
                };

                let mut imported_file = match ast::File::new(import_path) {
                    Ok(file) => file,
                    Err(io_error) => {
                        return Err(Error {
                            span: import_decl.path.span.clone(),
                            message: format!(
                                "could not read imported file. OS Error: {}",
                                io_error.to_string()
                            ),
                            file: None,
                        })
                    }
                };

                let tokens = match lexer::lex(&imported_file.source) {
                    Ok(tokens) => tokens,
                    Err(mut err) => {
                        err.file = Some(imported_file);
                        err.message = format!("lex error in imported module. {}", err.message);
                        return Err(err);
                    }
                };

                imported_file.stmts = match parser::parse(&tokens) {
                    Ok(stmts) => stmts,
                    Err(mut err) => {
                        err.file = Some(imported_file);
                        err.message = format!("parse error in imported module. {}", err.message);
                        return Err(err);
                    }
                };

                imported_file.direct_deps = match analyze_mut(&mut imported_file) {
                    Ok(imports) => imports,
                    Err(mut err) => {
                        err.file = Some(imported_file);
                        err.message = format!("analysis error in imported module. {}", err.message);
                        return Err(err);
                    }
                };

                for stmt in &imported_file.stmts {
                    match &stmt.kind {
                        ast::StmtKind::Fun(fun_decl) => {
                            if fun_decl.exported {
                                if let Some(target_type) = &fun_decl.target_type {
                                    let type_name = match &target_type.kind {
                                        ast::TypeKind::Struct(struct_type) => {
                                            format!("{}.{}", imported_file.id(), struct_type.name)
                                        }
                                        _ => target_type.kind.type_name(),
                                    };

                                    let resolved_type_info = match self
                                        .typespace
                                        .get_mut(&type_name)
                                    {
                                        Some(typ_info) => typ_info,
                                        None => {
                                            return Err(Error {
                                                span: target_type.span.clone(),
                                                message: format!("undefined type: '{}'", type_name),
                                                file: Some(imported_file),
                                            });
                                        }
                                    };

                                    resolved_type_info.methods.insert(
                                        imported_file.lexeme(&fun_decl.ident.span).to_string(),
                                        ast::FunType {
                                            parameters: fun_decl
                                                .parameters
                                                .iter()
                                                .map(|(_, typ)| typ.clone())
                                                .collect(),
                                            returns: fun_decl
                                                .return_type
                                                .as_ref()
                                                .map(|return_type| Box::new(return_type.clone())),
                                        },
                                    );
                                } else {
                                    let fun_name = format!(
                                        "{}.{}",
                                        import_name,
                                        imported_file.lexeme(&fun_decl.ident.span)
                                    );

                                    self.namespace.insert(
                                        fun_name,
                                        ast::Type {
                                            span: 0..0,
                                            kind: ast::FunType {
                                                parameters: fun_decl
                                                    .parameters
                                                    .iter()
                                                    .map(|(_, typ)| typ.clone())
                                                    .collect(),
                                                returns: fun_decl.return_type.as_ref().map(
                                                    |return_type| Box::new(return_type.clone()),
                                                ),
                                            }
                                            .into(),
                                        },
                                    );
                                }
                            }
                        }
                        ast::StmtKind::Struct(struct_decl) => {
                            if struct_decl.exported {
                                let struct_id = format!(
                                    "{}.{}",
                                    imported_file.id(),
                                    imported_file.lexeme(&struct_decl.ident.span).to_string()
                                );

                                let struct_type = ast::StructType {
                                    name: imported_file.lexeme(&struct_decl.ident.span).to_string(),
                                    file_id: imported_file.id(),
                                    members: struct_decl
                                        .members
                                        .iter()
                                        .map(|(ident, typ)| {
                                            (imported_file.lexeme(&ident.span).into(), typ.clone())
                                        })
                                        .collect(),
                                };

                                self.typespace.insert(
                                    struct_id,
                                    TypeInfo::new(ast::TypeKind::Struct(struct_type)),
                                );
                            }
                        }
                        _ => {}
                    }
                }

                self.file
                    .direct_deps
                    .insert(import_name.to_string(), imported_file);
                // TODO: Validate that there are no import cycles (e.g. a->b->a where `->` implying dependancy)
            }
        }

        let mut new_stmts = self.file.stmts.clone();
        for stmt in new_stmts.iter_mut() {
            self.analyze_stmt(stmt)?;
        }

        self.file.stmts = new_stmts;
        Ok(self.file.direct_deps.clone())
    }
}

#[allow(dead_code)]
pub fn analyze(file: &ast::File) -> Result<(ast::File, HashMap<String, ast::File>), Error> {
    let mut new_file = file.clone();
    let mut analyzer = Analyzer::new(&mut new_file);
    let deps = analyzer.analyze()?;
    Ok((new_file, deps))
}

pub fn analyze_mut(file: &mut ast::File) -> Result<HashMap<String, ast::File>, Error> {
    let mut analyzer = Analyzer::new(file);
    let deps = analyzer.analyze()?;
    Ok(deps)
}

fn recursively_add_deps(
    deps: &mut HashMap<String, ast::File>,
    file: &ast::File,
) -> Result<(), Error> {
    deps.insert(
        file.path.iter().fold(String::new(), |a, b| {
            format!("{}_{}", a, b.to_str().unwrap())
        }),
        file.clone(),
    );

    for stmt in &file.stmts {
        if let ast::StmtKind::Import(import_decl) = &stmt.kind {
            let import_path = {
                let mut dir_path = file.path.clone();
                dir_path.pop();
                dir_path.push(
                    &file.lexeme(&import_decl.path.span)
                        [1..file.lexeme(&import_decl.path.span).len() - 1],
                );
                dir_path
            };

            let mut imported_file = ast::File::new(import_path).unwrap();
            let tokens = lexer::lex(&imported_file.source).unwrap();
            imported_file.stmts = parser::parse(&tokens).unwrap();
            analyze_mut(&mut imported_file)?;

            recursively_add_deps(deps, &imported_file)?;
        }
    }

    Ok(())
}

pub fn get_deps<'ctx>(file: &ast::File) -> Result<HashMap<String, ast::File>, Error> {
    let mut deps = HashMap::new();
    recursively_add_deps(&mut deps, file)?;
    deps.remove(&file.path.iter().fold(String::new(), |a, b| {
        format!("{}_{}", a, b.to_str().unwrap())
    }));
    Ok(deps)
}
