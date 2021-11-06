use std::collections::HashMap;

use either::Either;
use inkwell::{
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum},
    values::{BasicValueEnum, FunctionValue},
    AddressSpace,
};

use crate::{ast, token};

#[derive(Debug)]
struct Generator<'a, 'ctx> {
    pub file: &'a ast::File,

    pub context: &'ctx inkwell::context::Context,
    pub module: &'a inkwell::module::Module<'ctx>,
    pub builder: &'a inkwell::builder::Builder<'ctx>,

    current_function: Option<FunctionValue<'ctx>>,
    function_retval: Option<inkwell::values::PointerValue<'ctx>>,
    function_retblock: Option<inkwell::basic_block::BasicBlock<'ctx>>,

    pub namespace: HashMap<String, inkwell::values::PointerValue<'ctx>>,
}

impl<'a, 'ctx> Generator<'a, 'ctx> {
    fn gen_type(&self, typ: &ast::Type) -> BasicTypeEnum<'ctx> {
        match &typ.kind {
            ast::TypeKind::Prim(prim) => match prim {
                ast::PrimType::Int(bit_size) => self
                    .context
                    .custom_width_int_type((*bit_size).into())
                    .into(),
                ast::PrimType::UInt(bit_size) => self
                    .context
                    .custom_width_int_type((*bit_size).into())
                    .into(),
                ast::PrimType::Float(bit_size) => match bit_size {
                    32 => self.context.f32_type().into(),
                    64 => self.context.f64_type().into(),
                    _ => panic!("internal-error: codegen has only been implemented for 32 and 64 bit float types"),
                },
                ast::PrimType::Bool => self.context.bool_type().into(),
                ast::PrimType::Str => self
                    .module
                    .get_struct_type("str")
                    .unwrap_or_else(|| {
                        self.context.opaque_struct_type("str");
                        self.module.get_struct_type("str").unwrap().set_body(
                            &[
                                self.context
                                    .i8_type()
                                    .ptr_type(AddressSpace::Generic)
                                    .into(), // buffer
                                self.context.i64_type().into(), // length
                                self.context.bool_type().into(), // is_heap
                            ],
                            false,
                        );
                        self.module.get_struct_type("str").unwrap()
                    })
                    .into(),
            },
            ast::TypeKind::Box(box_type) => self
                .gen_type(&*box_type.eltype)
                .ptr_type(AddressSpace::Generic)
                .into(),
            ast::TypeKind::Fun(_) => todo!(),
            ast::TypeKind::Struct(struct_type) => self
                .module
                .get_struct_type(&struct_type.name)
                .unwrap()
                .into(),
            ast::TypeKind::Slice(_) => todo!(),
            ast::TypeKind::Sum(_) => todo!(),
            ast::TypeKind::Named(_) => panic!("internal-error: named type should be resolved before generation"),
        }
    }

    fn declare_struct(&mut self, struct_decl: &ast::StructDecl) -> inkwell::types::StructType {
        self.module
            .get_struct_type(self.file.lexeme(&struct_decl.ident.span))
            .unwrap_or_else(|| {
                self.context
                    .opaque_struct_type(self.file.lexeme(&struct_decl.ident.span))
            })
    }

    fn declare_fun(&mut self, func: &ast::FunDecl) -> FunctionValue<'ctx> {
        self.module
            .get_function(self.file.lexeme(&func.ident.span))
            .unwrap_or_else(|| {
                if let Some(return_type) = &func.return_type {
                    self.module.add_function(
                        self.file.lexeme(&func.ident.span),
                        self.gen_type(return_type).fn_type(
                            &func
                                .parameters
                                .iter()
                                .map(|(_, typ)| self.gen_type(typ).into())
                                .collect::<Vec<BasicMetadataTypeEnum>>(),
                            false,
                        ),
                        None,
                    )
                } else {
                    self.module.add_function(
                        self.file.lexeme(&func.ident.span),
                        self.context.void_type().fn_type(
                            &func
                                .parameters
                                .iter()
                                .map(|(_, typ)| self.gen_type(typ).into())
                                .collect::<Vec<BasicMetadataTypeEnum>>(),
                            false,
                        ),
                        None,
                    )
                }
            })
    }

    fn gen_struct(&mut self, struct_decl: &ast::StructDecl) {
        self.module
            .get_struct_type(self.file.lexeme(&struct_decl.ident.span))
            .expect("internal-error: did not predeclare struct type")
            .set_body(
                &struct_decl
                    .members
                    .iter()
                    .map(|(_, typ)| typ)
                    .map(|typ| self.gen_type(typ))
                    .collect::<Vec<BasicTypeEnum>>(),
                false,
            );
    }

    fn gen_fun(&mut self, func: &ast::FunDecl) -> FunctionValue<'ctx> {
        self.namespace.clear();

        let func_decl = self.declare_fun(func);

        self.current_function = Some(func_decl);

        if let Some(block) = &func.block {
            let retblock = self.context.append_basic_block(func_decl, "retblock");
            self.function_retblock = Some(retblock);

            let function_entry_block = self.context.append_basic_block(func_decl, "entry");
            self.builder.position_at_end(function_entry_block);
            if let Some(ret_type) = &func.return_type {
                self.function_retval = Some(self.builder.build_alloca(self.gen_type(ret_type), ""));
            }

            for (i, param) in func_decl.get_param_iter().enumerate() {
                let param_alloca = self.builder.build_alloca(param.get_type(), "");
                self.builder.build_store(param_alloca, param);
                self.namespace.insert(
                    self.file.lexeme(&func.parameters[i].0.span).to_string(),
                    param_alloca,
                );
            }

            self.gen_stmt(&ast::Stmt {
                kind: ast::StmtKind::Block(block.clone()),
                pointer: 0..0,
            });

            self.builder.position_at_end(retblock);
            if func.return_type.is_some() {
                self.builder.build_return(Some(
                    &self.builder.build_load(self.function_retval.unwrap(), ""),
                ));
            } else {
                self.builder.build_return(None);
            }

            self.function_retblock
                .unwrap()
                .move_after(func_decl.get_last_basic_block().unwrap())
                .unwrap();

            self.current_function = None;
            self.function_retblock = None;
            self.function_retval = None;
        }

        func_decl
    }

    fn gen_expr(&mut self, expr: &ast::Expr) -> BasicValueEnum<'ctx> {
        match &expr.kind {
            ast::ExprKind::Unary(unary_expr) => {
                let target_value = self.gen_expr(&*unary_expr.expr);

                match &unary_expr.op.kind {
                    token::TokenKind::Bang => self
                        .builder
                        .build_not(target_value.into_int_value(), "")
                        .into(),
                    token::TokenKind::Minus => match &unary_expr.expr.typ.as_ref().unwrap().kind {
                        ast::TypeKind::Prim(prim_type) => match prim_type {
                            ast::PrimType::Int(_) | ast::PrimType::UInt(_) => self
                                .builder
                                .build_int_sub(
                                    target_value.get_type().const_zero().into_int_value(),
                                    target_value.into_int_value(),
                                    "",
                                )
                                .into(),
                            ast::PrimType::Float(_) => self
                                .builder
                                .build_float_sub(
                                    target_value.get_type().const_zero().into_float_value(),
                                    target_value.into_float_value(),
                                    "",
                                )
                                .into(),
                            _ => unreachable!(),
                        },
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                }
            }
            ast::ExprKind::Binary(binary_expr) => match &binary_expr.op.kind {
                token::TokenKind::Equal => {
                    let target = &*binary_expr.left;
                    match &target.kind {
                        ast::ExprKind::Var(var_expr) => {
                            let ptr = *self.namespace.get(self.file.lexeme(&var_expr.ident.span)).unwrap();
                            self.builder.build_store(ptr, self.gen_expr(&*binary_expr.right));
                            self.builder.build_load(ptr, "")
                        }
                        ast::ExprKind::Binary(get_expr) => {
                            if get_expr.op.kind != token::TokenKind::Dot {
                                panic!("internal-error: can only generate assignment to `.` get expressions")
                            }

                            let struct_value = self.gen_expr(&*get_expr.left);
                            let new_member_value = self.gen_expr(&*binary_expr.right);

                            if let ast::TypeKind::Struct(struct_type) = &get_expr.left.typ.as_ref().unwrap().kind {
                                if let ast::ExprKind::Var(var_expr) = &get_expr.right.kind {
                                    let member_name = self.file.lexeme(&var_expr.ident.span);
                                    let member_idx = struct_type
                                        .members
                                        .iter()
                                        .position(
                                            |(nested_member_name, _)| nested_member_name == member_name
                                        )
                                        .unwrap();
                                    let member_ptr = self.builder
                                        .build_struct_gep(
                                            struct_value.into_pointer_value(),
                                            member_idx as u32,
                                            "",
                                        ).unwrap();
                                    self.builder.build_store(member_ptr, new_member_value);
                                    self.builder.build_load(member_ptr, "")
                                } else {
                                    unreachable!()
                                }
                            } else {
                                unreachable!()
                            }
                        },
                        _ => panic!("internal-error: codegen has only been implemented for assignment with variables or get expression on the left-hand")
                    }
                }

                token::TokenKind::Dot => {
                    let struct_value = self.gen_expr(&*binary_expr.left);

                    if let ast::TypeKind::Struct(struct_type) =
                        &binary_expr.left.typ.as_ref().unwrap().kind
                    {
                        if let ast::ExprKind::Var(var_expr) = &binary_expr.right.kind {
                            let member_name = self.file.lexeme(&var_expr.ident.span);
                            let member_idx = struct_type
                                .members
                                .iter()
                                .position(|(nested_member_name, _)| {
                                    nested_member_name == member_name
                                })
                                .unwrap();
                            let member_ptr = self
                                .builder
                                .build_struct_gep(
                                    struct_value.into_pointer_value(),
                                    member_idx as u32,
                                    "",
                                )
                                .unwrap();
                            self.builder.build_load(member_ptr, "")
                        } else {
                            unreachable!()
                        }
                    } else {
                        unreachable!()
                    }
                }

                token::TokenKind::Plus
                | token::TokenKind::Minus
                | token::TokenKind::Star
                | token::TokenKind::Slash
                | token::TokenKind::Percent => {
                    let left_value = self.gen_expr(&*binary_expr.left);
                    let right_value = self.gen_expr(&*binary_expr.right);

                    match &binary_expr.left.typ.as_ref().unwrap().kind {
                        ast::TypeKind::Prim(prim_type) => match prim_type {
                            ast::PrimType::Int(_) | ast::PrimType::UInt(_) => {
                                match &binary_expr.op.kind {
                                    token::TokenKind::Plus => self
                                        .builder
                                        .build_int_add(
                                            left_value.into_int_value(),
                                            right_value.into_int_value(),
                                            "",
                                        )
                                        .into(),
                                    token::TokenKind::Minus => self
                                        .builder
                                        .build_int_sub(
                                            left_value.into_int_value(),
                                            right_value.into_int_value(),
                                            "",
                                        )
                                        .into(),
                                    token::TokenKind::Star => self
                                        .builder
                                        .build_int_mul(
                                            left_value.into_int_value(),
                                            right_value.into_int_value(),
                                            "",
                                        )
                                        .into(),
                                    token::TokenKind::Slash => {
                                        if let ast::PrimType::Int(_) = prim_type {
                                            self.builder
                                                .build_int_signed_div(
                                                    left_value.into_int_value(),
                                                    right_value.into_int_value(),
                                                    "",
                                                )
                                                .into()
                                        } else {
                                            self.builder
                                                .build_int_unsigned_div(
                                                    left_value.into_int_value(),
                                                    right_value.into_int_value(),
                                                    "",
                                                )
                                                .into()
                                        }
                                    }
                                    token::TokenKind::Percent => {
                                        if let ast::PrimType::Int(_) = prim_type {
                                            self.builder
                                                .build_int_signed_rem(
                                                    left_value.into_int_value(),
                                                    right_value.into_int_value(),
                                                    "",
                                                )
                                                .into()
                                        } else {
                                            self.builder
                                                .build_int_unsigned_rem(
                                                    left_value.into_int_value(),
                                                    right_value.into_int_value(),
                                                    "",
                                                )
                                                .into()
                                        }
                                    }
                                    _ => unreachable!(),
                                }
                            }
                            ast::PrimType::Float(_) => match &binary_expr.op.kind {
                                token::TokenKind::Plus => self
                                    .builder
                                    .build_float_add(
                                        left_value.into_float_value(),
                                        right_value.into_float_value(),
                                        "",
                                    )
                                    .into(),
                                token::TokenKind::Minus => self
                                    .builder
                                    .build_float_sub(
                                        left_value.into_float_value(),
                                        right_value.into_float_value(),
                                        "",
                                    )
                                    .into(),
                                token::TokenKind::Star => self
                                    .builder
                                    .build_float_mul(
                                        left_value.into_float_value(),
                                        right_value.into_float_value(),
                                        "",
                                    )
                                    .into(),
                                token::TokenKind::Slash => self
                                    .builder
                                    .build_float_div(
                                        left_value.into_float_value(),
                                        right_value.into_float_value(),
                                        "",
                                    )
                                    .into(),
                                token::TokenKind::Percent => self
                                    .builder
                                    .build_float_rem(
                                        left_value.into_float_value(),
                                        right_value.into_float_value(),
                                        "",
                                    )
                                    .into(),
                                _ => unreachable!(),
                            },
                            ast::PrimType::Str => todo!(),
                            ast::PrimType::Bool => unreachable!(),
                        },
                        _ => unreachable!(),
                    }
                }

                token::TokenKind::Lesser
                | token::TokenKind::Greater
                | token::TokenKind::LesserEqual
                | token::TokenKind::GreaterEqual
                | token::TokenKind::EqualEqual
                | token::TokenKind::BangEqual => {
                    let left_value = self.gen_expr(&*binary_expr.left);
                    let right_value = self.gen_expr(&*binary_expr.right);

                    match &binary_expr.left.typ.as_ref().unwrap().kind {
                        ast::TypeKind::Prim(prim_type) => match prim_type {
                            ast::PrimType::Int(_) => self
                                .builder
                                .build_int_compare(
                                    match &binary_expr.op.kind {
                                        token::TokenKind::Lesser => inkwell::IntPredicate::SLT,
                                        token::TokenKind::Greater => inkwell::IntPredicate::SGT,
                                        token::TokenKind::LesserEqual => inkwell::IntPredicate::SLE,
                                        token::TokenKind::GreaterEqual => {
                                            inkwell::IntPredicate::SGE
                                        }
                                        token::TokenKind::EqualEqual => inkwell::IntPredicate::EQ,
                                        token::TokenKind::BangEqual => inkwell::IntPredicate::NE,
                                        _ => unreachable!(),
                                    },
                                    left_value.into_int_value(),
                                    right_value.into_int_value(),
                                    "",
                                )
                                .into(),
                            ast::PrimType::UInt(_) => self
                                .builder
                                .build_int_compare(
                                    match &binary_expr.op.kind {
                                        token::TokenKind::Lesser => inkwell::IntPredicate::ULT,
                                        token::TokenKind::Greater => inkwell::IntPredicate::UGT,
                                        token::TokenKind::LesserEqual => inkwell::IntPredicate::ULE,
                                        token::TokenKind::GreaterEqual => {
                                            inkwell::IntPredicate::UGE
                                        }
                                        token::TokenKind::EqualEqual => inkwell::IntPredicate::EQ,
                                        token::TokenKind::BangEqual => inkwell::IntPredicate::NE,
                                        _ => unreachable!(),
                                    },
                                    left_value.into_int_value(),
                                    right_value.into_int_value(),
                                    "",
                                )
                                .into(),

                            ast::PrimType::Bool => self
                                .builder
                                .build_int_compare(
                                    match &binary_expr.op.kind {
                                        token::TokenKind::EqualEqual => inkwell::IntPredicate::EQ,
                                        token::TokenKind::BangEqual => inkwell::IntPredicate::NE,
                                        _ => unreachable!(),
                                    },
                                    left_value.into_int_value(),
                                    right_value.into_int_value(),
                                    "",
                                )
                                .into(),
                            ast::PrimType::Float(_) => self
                                .builder
                                .build_float_compare(
                                    inkwell::FloatPredicate::OEQ,
                                    left_value.into_float_value(),
                                    right_value.into_float_value(),
                                    "",
                                )
                                .into(),
                            ast::PrimType::Str => todo!(),
                        },
                        _ => todo!(),
                    }
                }

                token::TokenKind::AndAnd => {
                    // `&&` generates IR more similar to an if statement, rather than a simple `and` instruction
                    // This is because the right-hand of `&&` is only evaluated if the left-hand evaluates true
                    // (which is why `&&` is sometimes referred to as shortcutting and). We do this to allow code like:
                    // ```
                    // var el = arr.length > 0 && arr[0]
                    // ```

                    // So we transform an expression like:
                    // ```
                    // var n = 21
                    // var b = n == 21 && n < 10
                    // ```
                    //
                    // to something more like:
                    // ```
                    // var n = 21
                    // var b = false
                    // if n == 21 {
                    //     b = n < 10
                    // }
                    // ```
                    let result = self.builder.build_alloca(self.context.bool_type(), "");

                    let left_value = self.gen_expr(&*binary_expr.left);
                    let current_func = self
                        .current_function
                        .expect("internal-error: cannot generate if statement outside function");

                    let right_value_block = self.context.append_basic_block(current_func, "");
                    let left_false_block = self.context.append_basic_block(current_func, "");
                    let after_block = self.context.append_basic_block(current_func, "");

                    self.builder.build_conditional_branch(
                        left_value.into_int_value(),
                        right_value_block,
                        left_false_block,
                    );
                    self.builder.position_at_end(left_false_block);
                    self.builder
                        .build_store(result, self.context.bool_type().const_int(0, false));
                    self.builder.build_unconditional_branch(after_block);

                    self.builder.position_at_end(right_value_block);
                    let right_value = self.gen_expr(&*binary_expr.right);
                    self.builder.build_store(
                        result,
                        self.builder.build_and(
                            left_value.into_int_value(),
                            right_value.into_int_value(),
                            "",
                        ),
                    );
                    self.builder.build_unconditional_branch(after_block);

                    self.builder.position_at_end(after_block);
                    self.builder.build_load(result, "")
                }
                token::TokenKind::OrOr => {
                    let left_value = self.gen_expr(&*binary_expr.left);
                    let right_value = self.gen_expr(&*binary_expr.right);
                    self.builder
                        .build_or(
                            left_value.into_int_value(),
                            right_value.into_int_value(),
                            "",
                        )
                        .into()
                }

                _ => panic!(
                    "internal-error: codegen has not been implemented for binary operator: {:?}",
                    binary_expr.op.kind
                ),
            },
            ast::ExprKind::Var(var_expr) => {
                let var_ptr = *self
                    .namespace
                    .get(self.file.lexeme(&var_expr.ident.span))
                    .unwrap();

                if let ast::TypeKind::Struct(_) = &expr.typ.as_ref().unwrap().kind {
                    // Structs are passed around directly by a pointer to them
                    var_ptr.into()
                } else {
                    self.builder.build_load(var_ptr, "")
                }
            }
            ast::ExprKind::Call(call_expr) => {
                if let ast::ExprKind::Var(var_expr) = &call_expr.callee.kind {
                    if let Some(func) = self
                        .module
                        .get_function(self.file.lexeme(&var_expr.ident.span))
                    {
                        let mut genned_args = Vec::new();
                        for arg in &call_expr.args {
                            genned_args.push(self.gen_expr(arg).into());
                        }

                        if let Either::Left(value) = self
                            .builder
                            .build_call(func, &genned_args, "")
                            .try_as_basic_value()
                        {
                            value
                        } else {
                            self.context.i32_type().get_undef().into()
                        }
                    } else {
                        panic!("internal-error: uncaught undefined function")
                    }
                } else if let ast::ExprKind::Binary(binary_expr) = &call_expr.callee.kind {
                    if binary_expr.op.kind == token::TokenKind::Dot {
                        todo!()
                    } else {
                        panic!("internal-error: calling non-getexpr binary expr has not been implemented yet")
                    }
                } else {
                    panic!("internal-error: can only call variable & get expressions")
                }
            }
            ast::ExprKind::Idx(_) => todo!(),
            ast::ExprKind::As(_) => todo!(),
            ast::ExprKind::Is(_) => todo!(),
            ast::ExprKind::StructLit(struct_lit) => {
                let struct_type = self.gen_type(&struct_lit.typ);

                let mut genned_inits = Vec::new();
                for (_, init) in &struct_lit.inits {
                    genned_inits.push(self.gen_expr(init));
                }

                if let BasicTypeEnum::StructType(struct_type) = struct_type {
                    struct_type.const_named_struct(&genned_inits).into()
                } else {
                    // I can't even imagine how much I'd have to mess up to see this
                    panic!("internal-error: generated struct type is not a struct type")
                }
            }
            ast::ExprKind::SliceLit(_) => todo!(),
            ast::ExprKind::Lit(lit) => match &lit.token.kind {
                token::TokenKind::Int => self
                    .context
                    .i32_type()
                    .const_int(
                        self.file.lexeme(&lit.token.span).parse::<i32>().unwrap() as u64,
                        true,
                    )
                    .into(),
                token::TokenKind::Float => self
                    .context
                    .f64_type()
                    .const_float(self.file.lexeme(&lit.token.span).parse::<f64>().unwrap())
                    .into(),
                token::TokenKind::String => {
                    let global_str = self.module.add_global(
                        self.context
                            .i8_type()
                            .array_type(self.file.lexeme(&lit.token.span).len() as u32),
                        Some(AddressSpace::Const),
                        "",
                    );
                    global_str.set_initializer(
                        &self
                            .context
                            .const_string(self.file.lexeme(&lit.token.span).as_bytes(), false),
                    );

                    // SAFETY: Building a GEP is unsafe if the provided indices are incorrect. In this
                    // case that is not an issue since we're using `i32 0` as both the indices.
                    unsafe {
                        self.builder
                            .build_in_bounds_gep(
                                global_str.as_pointer_value(),
                                &[
                                    self.context.i32_type().const_int(0, false),
                                    self.context.i32_type().const_int(0, false),
                                ],
                                "",
                            )
                            .into()
                    }
                }
                token::TokenKind::True => self.context.bool_type().const_int(1, false).into(),
                token::TokenKind::False => self.context.bool_type().const_int(0, false).into(),
                _ => panic!(
                    "internal-error: codegen has not been implemented for literal token type: {:?}",
                    lit
                ),
            },
        }
    }

    fn gen_stmt(&mut self, stmt: &ast::Stmt) {
        match &stmt.kind {
            ast::StmtKind::Var(var_decl) => {
                let alloca = self.builder.build_alloca(
                    self.gen_type(var_decl.init.typ.as_ref().unwrap()),
                    self.file.lexeme(&var_decl.ident.span),
                );

                let value = self.gen_expr(&var_decl.init);
                self.builder.build_store(alloca, value);
                self.namespace
                    .insert(self.file.lexeme(&var_decl.ident.span).to_string(), alloca);
            }
            ast::StmtKind::Expr(expr_stmt) => {
                self.gen_expr(&expr_stmt.expr);
            }
            ast::StmtKind::Return(ret_stmt) => {
                if let Some(value) = &ret_stmt.value {
                    self.builder
                        .build_store(self.function_retval.unwrap(), self.gen_expr(value));
                }

                self.builder
                    .build_unconditional_branch(self.function_retblock.unwrap());
            }
            ast::StmtKind::Block(block_stmt) => {
                for stmt in &block_stmt.stmts {
                    self.gen_stmt(stmt);
                }
            }

            ast::StmtKind::If(if_stmt) => {
                let current_func = self
                    .current_function
                    .expect("internal-error: cannot generate if statement outside function");

                let cond_value = self.gen_expr(&if_stmt.condition);
                let then_block = self.context.append_basic_block(current_func, "");
                let elif_blocks = if_stmt
                    .elif_stmts
                    .iter()
                    .map(|(_, _)| {
                        (
                            self.context.append_basic_block(current_func, ""),
                            self.context.append_basic_block(current_func, ""),
                        )
                    })
                    .collect::<Vec<_>>();
                let else_block = self.context.append_basic_block(current_func, "");
                let after_block = self.context.append_basic_block(current_func, "");

                self.builder.build_conditional_branch(
                    cond_value.into_int_value(),
                    then_block,
                    if elif_blocks.is_empty() {
                        else_block
                    } else {
                        elif_blocks[0].0
                    },
                );

                self.builder.position_at_end(then_block);
                for stmt in &if_stmt.if_block.stmts {
                    self.gen_stmt(stmt)
                }
                if then_block.get_terminator().is_none() {
                    self.builder.build_unconditional_branch(after_block);
                }

                self.builder.position_at_end(else_block);
                if let Some(else_block) = &if_stmt.else_block {
                    for stmt in &else_block.stmts {
                        self.gen_stmt(stmt)
                    }
                }
                if else_block.get_terminator().is_none() {
                    self.builder.build_unconditional_branch(after_block);
                }

                for (i, (_, block)) in if_stmt.elif_stmts.iter().enumerate() {
                    self.builder.position_at_end(elif_blocks[i].1);
                    for stmt in &block.stmts {
                        self.gen_stmt(stmt)
                    }
                    if elif_blocks[i].1.get_terminator().is_none() {
                        self.builder.build_unconditional_branch(after_block);
                    }

                    self.builder.position_at_end(elif_blocks[i].0);
                    self.builder.build_conditional_branch(
                        self.gen_expr(&if_stmt.elif_stmts[i].0).into_int_value(),
                        elif_blocks[i].1,
                        if i == (elif_blocks.len() - 1) {
                            else_block
                        } else {
                            elif_blocks[i + 1].0
                        },
                    );
                }

                self.builder.position_at_end(after_block);
            }
            ast::StmtKind::While(while_stmt) => {
                let current_func = self
                    .current_function
                    .expect("internal-error: cannot generate while statement outside function");

                let cond_value = self.gen_expr(&while_stmt.condition);
                let while_block = self.context.append_basic_block(current_func, "");
                let after_block = self.context.append_basic_block(current_func, "");

                self.builder.build_conditional_branch(
                    cond_value.into_int_value(),
                    while_block,
                    after_block,
                );

                self.builder.position_at_end(while_block);
                for stmt in &while_stmt.block.stmts {
                    self.gen_stmt(stmt)
                }
                self.builder.build_conditional_branch(
                    cond_value.into_int_value(),
                    while_block,
                    after_block,
                );

                self.builder.position_at_end(after_block);
            }
            _ => panic!("internal-error: cannot generate non top-level declaration"),
        }
    }
}

pub fn gen<'ctx>(
    context: &'ctx inkwell::context::Context,
    file: &ast::File,
) -> inkwell::module::Module<'ctx> {
    let namespace = HashMap::<String, inkwell::values::PointerValue>::new();
    let module = context.create_module("my_module");
    let builder = context.create_builder();

    let mut generator = Generator {
        context,
        module: &module,
        builder: &builder,

        current_function: None,
        function_retval: None,
        function_retblock: None,

        file,
        namespace,
    };

    // Forward declare all our declarations
    for stmt in &file.stmts {
        match &stmt.kind {
            ast::StmtKind::Fun(fun_decl) => {
                generator.declare_fun(fun_decl);
            }
            ast::StmtKind::Struct(struct_decl) => {
                generator.declare_struct(struct_decl);
            }
            ast::StmtKind::Import(_) => todo!(),
            _ => unreachable!(),
        }
    }

    for stmt in &file.stmts {
        match &stmt.kind {
            ast::StmtKind::Fun(fun_decl) => {
                generator.gen_fun(fun_decl);
            }
            ast::StmtKind::Struct(struct_decl) => {
                generator.gen_struct(struct_decl);
            }
            ast::StmtKind::Import(_) => todo!(),
            _ => unreachable!(),
        }
    }

    module
}
