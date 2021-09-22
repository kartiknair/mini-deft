use std::{borrow::Borrow, collections::HashMap, convert::TryInto, mem::discriminant};

use crate::{ast, common::Error, token};

#[derive(Debug)]
struct Analyzer<'a> {
    file: &'a mut ast::File,
    namespace: HashMap<String, ast::Type>,
    typespace: HashMap<String, ast::TypeKind>,

    within_function: Option<ast::FunDecl>,
}

impl<'a> Analyzer<'a> {
    fn new(file: &'a mut ast::File) -> Self {
        let mut typespace = HashMap::new();

        typespace.insert("i8".into(), ast::PrimType::Int(8).into());
        typespace.insert("i16".into(), ast::PrimType::Int(16).into());
        typespace.insert("i32".into(), ast::PrimType::Int(32).into());
        typespace.insert("i64".into(), ast::PrimType::Int(64).into());

        typespace.insert("u8".into(), ast::PrimType::UInt(8).into());
        typespace.insert("u16".into(), ast::PrimType::UInt(16).into());
        typespace.insert("u32".into(), ast::PrimType::UInt(32).into());
        typespace.insert("u64".into(), ast::PrimType::UInt(64).into());

        typespace.insert("f32".into(), ast::PrimType::Float(32).into());
        typespace.insert("f64".into(), ast::PrimType::Float(64).into());

        typespace.insert("str".into(), ast::PrimType::Str.into());
        typespace.insert("bool".into(), ast::PrimType::Bool.into());

        Self {
            file,
            namespace: HashMap::new(),
            typespace,

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
            ast::TypeKind::Box(left_box_type) => {
                let right_box_type: &ast::BoxType = right.kind.borrow().try_into().unwrap();
                self.type_eq(&left_box_type.eltype, &right_box_type.eltype)
            }
            ast::TypeKind::Slice(left_slice_type) => {
                let right_slice_type: &ast::SliceType = right.kind.borrow().try_into().unwrap();
                self.type_eq(&left_slice_type.eltype, &right_slice_type.eltype)
            }
            ast::TypeKind::Sum(left_sum_type) => {
                let right_sum_type: &ast::SumType = right.kind.borrow().try_into().unwrap();

                if left_sum_type.variants.len() == right_sum_type.variants.len() {
                    let mut every_variant_same = true;
                    for variant in &left_sum_type.variants {
                        if !right_sum_type
                            .variants
                            .iter()
                            .any(|right_variant| self.type_eq(variant, right_variant))
                        {
                            every_variant_same = false
                        }
                    }

                    every_variant_same
                } else {
                    false
                }
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
            ast::TypeKind::Sum(sum_type) => {
                for variant in sum_type.variants.iter_mut() {
                    self.analyze_type(variant)?;
                }
            }
            ast::TypeKind::Box(box_type) => {
                self.analyze_type(&mut box_type.eltype)?;
            }
            ast::TypeKind::Slice(slice_type) => {
                self.analyze_type(&mut slice_type.eltype)?;
            }
            ast::TypeKind::Named(named_type) => {
                let lexeme = self.file.lexeme(&named_type.name.span);
                if let Some(resolved_type) = self.typespace.get(lexeme) {
                    typ.kind = resolved_type.clone();
                } else {
                    return Err(Error {
                        message: "unknown named type".into(),
                        span: named_type.name.span.clone(),
                    });
                }
            }
            _ => todo!(),
        }

        Ok(())
    }

    fn analyze_stmt(&mut self, stmt: &mut ast::Stmt) -> Result<(), Error> {
        match &mut stmt.kind {
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

                for param in fun_decl.parameters.iter_mut() {
                    self.analyze_type(&mut param.1)?;

                    if self.file.lexeme(&param.0.span) == function_name {
                        return Err(param
                            .0
                            .error_at("parameter name cannot be same as function name"));
                    }

                    self.namespace
                        .insert(self.file.lexeme(&param.0.span).into(), param.1.clone());
                }

                self.namespace.insert(
                    function_name.into(),
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

                self.within_function = None;
            }
            ast::StmtKind::Struct(struct_decl) => {
                for member in struct_decl.members.iter_mut() {
                    self.analyze_type(&mut member.1)?;
                }

                let struct_name = self.file.lexeme(&struct_decl.ident.span).to_string();
                let struct_type = ast::StructType {
                    name: struct_name.clone(),
                    members: struct_decl
                        .members
                        .iter()
                        .map(|(ident, typ)| (self.file.lexeme(&ident.span).into(), typ.clone()))
                        .collect(),
                };

                self.typespace
                    .insert(struct_name, ast::TypeKind::Struct(struct_type));
            }

            ast::StmtKind::Var(var_stmt) => {
                if let Some(typ) = &mut var_stmt.typ {
                    if let Some(init) = &mut var_stmt.init {
                        // e.g. var x int = 32
                        self.analyze_expr(init)?;
                        if !self.is_assignable(init, typ, false)? {
                            return Err(Error {
                                message: "variable initializer is not assignable to provided type"
                                    .into(),
                                span: init.span.clone(),
                            });
                        }
                    } else {
                        // e.g. var x int
                        self.analyze_type(typ)?;
                    }
                } else if let Some(init) = &mut var_stmt.init {
                    // e.g. var x = 34
                    self.analyze_expr(init)?;
                    var_stmt.typ = init.typ.clone();
                } else {
                    // e.g. var x
                    return Err(var_stmt.ident.error_at(
                        "variable declaration requires either a type or an initializer",
                    ));
                }

                if let Some(var_type) = &var_stmt.typ {
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
                        });
                    }
                } else {
                    return Err(Error {
                        span: if_stmt.condition.span.clone(),
                        message: "void expression cannot be used as if statement condition".into(),
                    });
                }
            }
            ast::StmtKind::While(while_stmt) => {
                self.analyze_expr(&mut while_stmt.condition)?;
                if let Some(typ) = &while_stmt.condition.typ {
                    if let ast::TypeKind::Prim(ast::PrimType::Bool) = &typ.kind {
                        return Ok(());
                    }

                    return Err(Error {
                        message: "while condition must be of boolean type".into(),
                        span: while_stmt.condition.span.clone(),
                    });
                } else {
                    return Err(Error {
                        message: "cannot use void expression as while condition".into(),
                        span: while_stmt.condition.span.clone(),
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
                                });
                            }
                        } else {
                            return Err(Error {
                                message: "returning value in void function".into(),
                                span: value.span.clone(),
                            });
                        }
                    } else if current_func.return_type.is_some() {
                        return Err(Error {
                            message: "void return in function with return type".into(),
                            span: stmt.pointer.clone(),
                        });
                    }
                } else {
                    return Err(Error {
                        message: "return statement must be inside function".into(),
                        span: stmt.pointer.clone(),
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
                return Ok(false);
            }

            // Cases where we do implicit casting (e.g. upcasting sum-type variants)
            if !self.type_eq(expr_type, target_type) {
                if let ast::TypeKind::Box(box_type) = &target_type.kind {
                    Ok(self.type_eq(expr_type, &*box_type.eltype))
                } else if let ast::TypeKind::Sum(target_sum_type) = &target_type.kind {
                    if let ast::TypeKind::Sum(_) = &expr_type.kind {
                        return Ok(false);
                    }

                    Ok(target_sum_type
                        .variants
                        .iter()
                        .any(|variant| self.type_eq(variant, expr_type)))
                } else if let ast::TypeKind::Sum(expr_sum_type) = &expr_type.kind {
                    if let ast::TypeKind::Sum(_) = &target_type.kind {
                        return Ok(false);
                    }

                    Ok(expr_sum_type
                        .variants
                        .iter()
                        .any(|variant| self.type_eq(variant, target_type)))
                } else {
                    Ok(false)
                }
            } else {
                Ok(true)
            }
        } else {
            Err(Error {
                span: expr.span.clone(),
                message: "unexpected void expression".into(),
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
                            });
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
                    });
                }
            }
            ast::ExprKind::Binary(binary_expr) => {
                self.analyze_expr(&mut binary_expr.left)?;
                self.analyze_expr(&mut binary_expr.right)?;

                if let Some(left_expr_type) = &binary_expr.left.typ {
                    if let Some(right_expr_type) = &binary_expr.right.typ {
                        if !self.type_eq(right_expr_type, left_expr_type) {
                            return Err(Error {
                                message: "binary expressions must have the same type expression on both sides".into(),
                                span: expr.span.clone(),
                            });
                        }

                        if let ast::TypeKind::Prim(prim_type) = &left_expr_type.kind {
                            if prim_type.is_numeric() {
                                expr.typ = Some(left_expr_type.clone());
                                return Ok(());
                            }
                        }

                        return Err(Error {
                            message:
                                "binary expressions can only be done on primitive numeric types"
                                    .into(),
                            span: expr.span.clone(),
                        });
                    }
                }

                return Err(Error {
                    message: "cannot use void expression in a binary expression".into(),
                    span: expr.span.clone(),
                });
            }
            ast::ExprKind::Var(var_expr) => {
                let var_name = self.file.lexeme(&var_expr.ident.span);
                if let Some(var_type) = self.namespace.get(var_name) {
                    expr.typ = Some(var_type.clone());
                } else {
                    return Err(Error {
                        message: "undefined variable".into(),
                        span: expr.span.clone(),
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
                                if !self.is_assignable(arg, &param_type, true)? {
                                    return Err(Error {
                                        message: "invalid argument type".into(),
                                        span: arg.span.clone(),
                                    });
                                }
                            } else {
                                return Err(Error {
                                    message: "cannot use void expression as function argument"
                                        .into(),
                                    span: call_expr.callee.span.clone(),
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
                        });
                    }
                } else {
                    return Err(Error {
                        message: "cannot call void expression".into(),
                        span: call_expr.callee.span.clone(),
                    });
                }
            }
            ast::ExprKind::Idx(idx_expr) => {
                self.analyze_expr(&mut idx_expr.target)?;
                self.analyze_expr(&mut idx_expr.idx)?;

                if let Some(target_type) = &idx_expr.target.typ {
                    if let ast::TypeKind::Slice(slice_type) = &target_type.kind {
                        expr.typ = Some((*slice_type.eltype).clone())
                    } else {
                        return Err(Error {
                            message: "index target has non-slice type".into(),
                            span: idx_expr.target.span.clone(),
                        });
                    }
                } else {
                    return Err(Error {
                        message: "cannot index void expression".into(),
                        span: idx_expr.target.span.clone(),
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
                            });
                        }
                    } else if let ast::TypeKind::Sum(sum_type) = &expr_type.kind {
                        let mut found_variant = None;
                        for variant in &sum_type.variants {
                            if self.type_eq(variant, &as_expr.typ) {
                                found_variant = Some(variant.clone())
                            }
                        }

                        if let Some(variant_type) = found_variant {
                            expr.typ = Some(variant_type);
                        } else {
                            return Err(Error {
                                message: "cast target is not a variant".into(),
                                span: as_expr.typ.span.clone(),
                            });
                        }
                    } else {
                        return Err(Error {
                            message: "can only cast numeric primitives or sum type values".into(),
                            span: as_expr.expr.span.clone(),
                        });
                    }
                } else {
                    return Err(Error {
                        message: "cannot cast void expression".into(),
                        span: as_expr.expr.span.clone(),
                    });
                }
            }
            ast::ExprKind::Is(is_expr) => {
                self.analyze_expr(&mut is_expr.expr)?;
                self.analyze_type(&mut is_expr.typ)?;

                if let Some(expr_type) = &is_expr.expr.typ {
                    if let ast::TypeKind::Sum(sum_type) = &expr_type.kind {
                        if !sum_type
                            .variants
                            .iter()
                            .any(|variant| self.type_eq(variant, &is_expr.typ))
                        {
                            return Err(Error {
                                message: "checked type is not a variant of the expression type"
                                    .into(),
                                span: is_expr.expr.span.clone(),
                            });
                        }

                        expr.typ = Some(ast::Type {
                            kind: ast::TypeKind::Prim(ast::PrimType::Bool),
                            span: 0..0,
                        });
                    } else {
                        return Err(Error {
                            message: "cannot check type of non-sum-type expression".into(),
                            span: is_expr.expr.span.clone(),
                        });
                    }
                } else {
                    return Err(Error {
                        message: "cannot compare type of void expression".into(),
                        span: is_expr.expr.span.clone(),
                    });
                }
            }
            ast::ExprKind::StructLit(struct_lit) => {
                self.analyze_type(&mut struct_lit.typ)?;
                expr.typ = Some(struct_lit.typ.clone());
            }
            ast::ExprKind::SliceLit(slice_lit) => {
                let mut eltype = None;

                if slice_lit.exprs.is_empty() {
                    return Err(Error {
                        message: "cannot infer type of empty slice literal".into(),
                        span: expr.span.clone(),
                    });
                }

                for expr in slice_lit.exprs.iter_mut() {
                    self.analyze_expr(expr)?;
                    if expr.typ.is_none() {
                        return Err(Error {
                            message: "cannot use void expression as slice literal element".into(),
                            span: expr.span.clone(),
                        });
                    }
                }

                for expr in slice_lit.exprs.iter_mut() {
                    let expr_typ = if let Some(typ) = &mut expr.typ {
                        typ
                    } else {
                        panic!("")
                    };
                    let cloned_expr_typ = expr_typ.clone();

                    if let Some(slice_eltype) = &eltype {
                        if let ast::TypeKind::Sum(sum_type) = &mut expr_typ.kind {
                            if !sum_type
                                .variants
                                .iter()
                                .any(|variant| self.type_eq(variant, &cloned_expr_typ))
                            {
                                sum_type.variants.push(cloned_expr_typ);
                            }
                        } else if !self.type_eq(&slice_eltype, &expr_typ) {
                            let sum_type = ast::Type {
                                span: 0..0,
                                kind: ast::TypeKind::Sum(ast::SumType {
                                    variants: vec![slice_eltype.clone(), cloned_expr_typ],
                                }),
                            };
                            eltype = Some(sum_type);
                        }
                    } else {
                        eltype = Some(expr_typ.clone());
                    }
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
                    token::TokenKind::String => ast::Type {
                        span: 0..0,
                        kind: ast::TypeKind::Prim(ast::PrimType::Str),
                    },
                    token::TokenKind::True => ast::Type {
                        span: 0..0,
                        kind: ast::TypeKind::Prim(ast::PrimType::Bool),
                    },
                    token::TokenKind::False => ast::Type {
                        span: 0..0,
                        kind: ast::TypeKind::Prim(ast::PrimType::Bool),
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

    fn analyze(&mut self) -> Result<(), Error> {
        let mut new_stmts = self.file.stmts.clone();
        for stmt in new_stmts.iter_mut() {
            self.analyze_stmt(stmt)?;
        }

        self.file.stmts = new_stmts;
        Ok(())
    }
}

pub fn analyze(file: &ast::File) -> Result<ast::File, Error> {
    let mut new_file = file.clone();
    let mut analyzer = Analyzer::new(&mut new_file);
    analyzer.analyze()?;
    Ok(new_file)
}

pub fn analyze_mut(file: &mut ast::File) -> Result<(), Error> {
    let mut analyzer = Analyzer::new(file);
    analyzer.analyze()
}
