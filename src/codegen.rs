use std::{collections::HashMap, convert::{TryInto, TryFrom}};

use either::Either;
use inkwell::{
    context::Context,
    module::{Module, Linkage},
    types::{BasicMetadataTypeEnum, BasicType, BasicTypeEnum, AnyType},
    values::{BasicValueEnum, FunctionValue, CallableValue},
    AddressSpace,
};

use crate::{analyzer, ast, token};

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
            },
            ast::TypeKind::Box(box_type) => {
                let genned_box_type = self.gen_type(&*box_type.eltype).ptr_type(AddressSpace::Generic);

                // generate drop function
                let drop_func_name = format!("{}.{}.drop", self.file.id(), typ.kind.type_name());
                self.module.get_function(&drop_func_name)
                    .unwrap_or_else(|| {
                        let drop_func = self.module.add_function(
                            &drop_func_name,
                            self.context.void_type().fn_type(&vec![
                                genned_box_type.ptr_type(AddressSpace::Generic).into(), // ptr to ptr
                            ], false),
                            Some(Linkage::Private),
                        );

                        let prev_block = self.builder.get_insert_block();
                        
                        let drop_func_block = self.context.append_basic_block(drop_func, "entry");
                        self.builder.position_at_end(drop_func_block);
                        if !box_type.eltype.kind.is_copyable() {
                            let nested_drop_func_name = if let ast::TypeKind::Struct(struct_type) = &box_type.eltype.kind {
                                format!("{}.{}.drop", &struct_type.file_id, &struct_type.name)
                            } else {
                                format!("{}.{}.drop", self.file.id(), box_type.eltype.kind.type_name())
                            };
                            self.builder.build_call(
                                self.module.get_function(&nested_drop_func_name).unwrap(),
                                &vec![
                                    self.builder.build_load(
                                        drop_func.get_first_param().unwrap().into_pointer_value(),
                                        ""
                                    ).into()
                                ],
                                "",
                            );
                        }
                        self.builder.build_free(self.builder.build_load(
                            drop_func.get_first_param().unwrap().into_pointer_value(), 
                            "",
                        ).into_pointer_value());

                        self.builder.build_return(None);
        
                        if let Some(prev_block) = prev_block {
                            self.builder.position_at_end(prev_block);
                        }

                        drop_func
                    });

                // generate copy function
                let copy_func_name = format!("{}.{}.copy", self.file.id(), typ.kind.type_name());
                self.module.get_function(&copy_func_name)
                    .unwrap_or_else(|| {
                        let copy_func = self.module.add_function(
                            &copy_func_name,
                            genned_box_type.fn_type(&vec![
                                genned_box_type.into(),
                            ], false),
                            Some(Linkage::Private),
                        );

                        let prev_block = self.builder.get_insert_block();
                        
                        let copy_func_block = self.context.append_basic_block(copy_func, "entry");
                        self.builder.position_at_end(copy_func_block);
                        
                        let eltype: BasicTypeEnum = genned_box_type.get_element_type().try_into().unwrap();
                        let result_ptr = self.builder.build_malloc(eltype, "").unwrap();
                        if box_type.eltype.kind.is_copyable() {
                            self.builder.build_store(result_ptr, self.builder.build_load(copy_func.get_first_param().unwrap().into_pointer_value(), ""));
                        } else {
                            let nested_copy_func_name = if let ast::TypeKind::Struct(struct_type) = &box_type.eltype.kind {
                                format!("{}.copy", struct_type.name)
                            } else {
                                format!("{}.{}.copy", self.file.id(), box_type.eltype.kind.type_name())
                            };
                            self.builder.build_store(
                                result_ptr, 
                                self.builder.build_call(
                                    self.module.get_function(&nested_copy_func_name).unwrap(),
                                    &vec![],
                                    "",
                                ).try_as_basic_value().unwrap_left(),
                            );
                        }
                        self.builder.build_return(Some(&result_ptr));
        
                        if let Some(prev_block) = prev_block {
                            self.builder.position_at_end(prev_block);
                        }

                        copy_func
                    });

                genned_box_type.into()
            }
            ast::TypeKind::Arr(arr_type) => {
                // prefixed with `.` to avoic collision with user-defined types
                let prefixed_name = format!(".{}", typ.kind.type_name());

                let arr_struct_type = self.module
                    .get_struct_type(&prefixed_name)
                    .unwrap_or_else(|| {
                        let blank_st = self.context.opaque_struct_type(&prefixed_name);
                        blank_st.set_body(
                            &[
                                self.gen_type(&*arr_type.eltype).ptr_type(AddressSpace::Generic).into(),
                                self.context.i64_type().into(),
                                self.context.i64_type().into(),
                            ],
                            false,
                        );
                        blank_st
                    });
  
                let drop_func_name = format!("{}.{}.drop", self.file.id(), typ.kind.type_name());
                self.module.get_function(&drop_func_name)
                    .unwrap_or_else(|| {
                        let drop_func = self.module.add_function(
                            &drop_func_name,
                            self.context.void_type().fn_type(&vec![
                                arr_struct_type.ptr_type(AddressSpace::Generic).into(),
                            ], false),
                            Some(Linkage::Private),
                        );

                        let prev_block = self.builder.get_insert_block();
                        
                        let drop_func_block = self.context.append_basic_block(drop_func, "entry");
                        self.builder.position_at_end(drop_func_block);
                        if !arr_type.eltype.kind.is_copyable() {
                            let nested_drop_func_name = if let ast::TypeKind::Struct(struct_type) = &arr_type.eltype.kind {
                                format!("{}.{}.drop", &struct_type.file_id, &struct_type.name)
                            } else {
                                format!("{}.{}.drop", self.file.id(), arr_type.eltype.kind.type_name())
                            };
                            let idx_value = self.builder.build_alloca(self.context.i64_type(), "idx");
                            self.builder.build_store(idx_value, self.context.i64_type().const_int(0, false));

                            let comparison = self.builder.build_int_compare(
                                inkwell::IntPredicate::ULT,
                                self.builder.build_load(idx_value, "").into_int_value(),
                                self.builder.build_load(self.builder.build_struct_gep(
                                    drop_func.get_first_param().unwrap().into_pointer_value(),
                                    1,
                                    "length"
                                ).unwrap(), "").into_int_value(),
                                ""
                            );
                            
                            let loop_block = self.context.append_basic_block(drop_func, "loop");
                            let after_block = self.context.append_basic_block(drop_func, "after");
                            self.builder.build_conditional_branch(comparison, loop_block, after_block);

                            self.builder.position_at_end(loop_block);
                            self.builder.build_call(
                                self.module.get_function(&nested_drop_func_name).unwrap(),
                                &vec![
                                    unsafe {          
                                        self.builder.build_in_bounds_gep(self.builder.build_load(
                                            self.builder.build_struct_gep(
                                                drop_func.get_first_param().unwrap().into_pointer_value(), 
                                                0, 
                                                "",
                                                ).unwrap(),
                                            "",
                                        ).into_pointer_value(), &[self.builder.build_load(idx_value, "").into_int_value()], "").into()
                                    }
                                ],
                                "",
                            );
                            self.builder.build_store(idx_value, self.builder.build_int_add(
                                self.builder.build_load(idx_value, "").into_int_value(),
                                self.context.i64_type().const_int(1, false),
                                ""
                            ));
                            let comparison = self.builder.build_int_compare(
                                inkwell::IntPredicate::ULT,
                                self.builder.build_load(idx_value, "").into_int_value(),
                                self.builder.build_load(self.builder.build_struct_gep(
                                    drop_func.get_first_param().unwrap().into_pointer_value(),
                                    1,
                                    "length"
                                ).unwrap(), "").into_int_value(),
                                ""
                            );
                            self.builder.build_conditional_branch(comparison, loop_block, after_block);
                        }


                        self.builder.build_free(
                            self.builder.build_load(
                                self.builder.build_struct_gep(
                                    drop_func.get_first_param().unwrap().into_pointer_value(), 
                                    0, 
                                    "",
                                    ).unwrap(),
                                "",
                            ).into_pointer_value()
                        );
                        self.builder.build_return(None);
        
                        if let Some(prev_block) = prev_block {
                            self.builder.position_at_end(prev_block);
                        } 
                        
                        drop_func
                    });

                arr_struct_type.into()
            }
            ast::TypeKind::Fun(fun_type) => {
                if let Some(return_type) = &fun_type.returns {
                    let genned_type = self.gen_type(&*return_type);
                    genned_type.fn_type(
                        &fun_type.parameters.iter().map(|typ| self.gen_type(typ).into()).collect::<Vec<_>>(),
                        false,
                    ).ptr_type(AddressSpace::Generic).into()
                } else {
                    self.context.void_type().fn_type(
                        &fun_type.parameters.iter().map(|typ| self.gen_type(typ).into()).collect::<Vec<_>>(),
                        false,
                    ).ptr_type(AddressSpace::Generic).into()
                }
            },
            ast::TypeKind::Struct(struct_type) => {
                self
                    .module
                    .get_struct_type(&format!("{}.{}", &struct_type.file_id, &struct_type.name))
                    .unwrap()
                    .into()
            }
            ast::TypeKind::Named(_) => panic!("internal-error: named type should be resolved before generation"),
        }
    }

    fn declare_struct(
        &mut self,
        struct_decl: &ast::StructDecl,
        file: Option<&ast::File>,
    ) -> inkwell::types::StructType {
        let file = if let Some(file) = file {
            file
        } else {
            &self.file
        };

        let struct_name = format!("{}.{}", file.id(), file.lexeme(&struct_decl.ident.span));

        self.module
            .get_struct_type(&struct_name)
            .unwrap_or_else(|| self.context.opaque_struct_type(&struct_name))
    }

    fn declare_fun(
        &mut self,
        func: &ast::FunDecl,
        file: Option<&ast::File>,
    ) -> FunctionValue<'ctx> {
        let file = if let Some(file) = file {
            file
        } else {
            &self.file
        };

        let fun_name = if let Some(target_type) = &func.target_type {
            let type_name = if let ast::TypeKind::Struct(struct_type) = &target_type.kind {
                format!("{}.{}", &struct_type.file_id, &struct_type.name)
            } else {
                target_type.kind.type_name().to_string()
            };

            let fun_name = format!("{}.{}", type_name, file.lexeme(&func.ident.span));

            if file.lexeme(&func.ident.span) == "drop" {
                unsafe {
                    if let Some(function) = self.module.get_function(&fun_name) {
                        function.delete()
                    }
                }
            }

            fun_name
        } else {
            let lexeme = file.lexeme(&func.ident.span);
            if func.external || lexeme == "main" {
                lexeme.to_string()
            } else {
                format!("{}.{}", file.id(), lexeme)
            }
        };

        self.module.get_function(&fun_name).unwrap_or_else(|| -> FunctionValue {
            let mut tmp_params = func
                .parameters
                .iter()
                .map(|(_, typ)| self.gen_type(typ).ptr_type(AddressSpace::Generic).into())
                .collect::<Vec<BasicMetadataTypeEnum>>();
            let mut parameters = if let Some(target_type) = &func.target_type {
                tmp_params.insert(
                    0,
                    self.gen_type(target_type)
                        .ptr_type(AddressSpace::Generic)
                        .into(),
                );
                tmp_params
            } else {
                tmp_params
            };

            let linkage = if func.external {
                Some(Linkage::External)
            } else {
                None
            };

            if let Some(return_type) = &func.return_type {
                let mut has_sret = false;
                let fn_value = self.module.add_function(
                    &fun_name,
                    if let ast::TypeKind::Struct(_) | ast::TypeKind::Arr(_) = &return_type.kind {
                        has_sret = true;
                        parameters.insert(
                            0,
                            self.gen_type(return_type).ptr_type(AddressSpace::Generic).into(),
                        );
                        self.context.void_type().fn_type(&parameters, false)
                    } else {
                        self.gen_type(return_type).fn_type(&parameters, false)
                    },
                    linkage,
                );

                if has_sret {
                    let kind_id = inkwell::attributes::Attribute::get_named_enum_kind_id("sret");
                    let type_attribute = self.context.create_type_attribute(
                        kind_id,
                        self.gen_type(return_type).as_any_type_enum(),
                    );
                    fn_value.add_attribute(inkwell::attributes::AttributeLoc::Param(0), type_attribute);
                }

                fn_value
            } else {
                self.module.add_function(
                    &fun_name,
                    self.context.void_type().fn_type(&parameters, false),
                    linkage,
                )
            }
        })
    }

    fn gen_struct(&mut self, struct_decl: &ast::StructDecl, file: Option<&ast::File>) {
        let file = if let Some(file) = file {
            file
        } else {
            &self.file
        };

        let struct_name = file.lexeme(&struct_decl.ident.span).to_string();
        
        let struct_type = ast::StructType {
            name: struct_name.clone(),
            file_id: file.id(),
            members: struct_decl
                .members
                .iter()
                .map(|(ident, typ)| (file.lexeme(&ident.span).into(), typ.clone()))
                .collect(),
        };

        self.module
            .get_struct_type(&format!("{}.{}", &file.id(), &struct_name))
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

        if !ast::TypeKind::Struct(struct_type.clone()).is_copyable() {
            let drop_func_name = format!("{}.{}.drop", &struct_type.file_id, &struct_name);
            let drop_func = if let Some(_) = self.module.get_function(&drop_func_name) {
                return;
            } else {
                self.module.add_function(
                    &format!("{}.{}.drop", &file.id(), &struct_name),
                    self.context.void_type().fn_type(
                        &vec![self
                            .module
                            .get_struct_type(&format!("{}.{}", &file.id(), &struct_name))
                            .unwrap()
                            .ptr_type(AddressSpace::Generic)
                            .into()],
                        false,
                    ),
                    None,
                )
            };

            let struct_drop_block = self.context.append_basic_block(drop_func, "entry");
            self.builder.position_at_end(struct_drop_block);
            for (i, (_, member_type)) in struct_type.members.iter().enumerate() {
                if !member_type.kind.is_copyable() {
                    let member_drop_func_name =
                        if let ast::TypeKind::Struct(struct_type) = &member_type.kind {
                            format!("{}.{}.drop", &struct_type.file_id, &struct_type.name)
                        } else {
                            format!("{}.{}.drop", self.file.id(), member_type.kind.type_name())
                        };

                    self.builder.build_call(
                        self.module.get_function(&member_drop_func_name).unwrap(),
                        &vec![self
                            .builder
                            .build_struct_gep(
                                drop_func.get_first_param().unwrap().into_pointer_value(),
                                i as u32,
                                "",
                            )
                            .unwrap()
                            .into()],
                        "",
                    );
                }
            }
            self.builder.build_return(None);
        }
    }

    fn gen_fun(&mut self, func: &ast::FunDecl) -> FunctionValue<'ctx> {
        self.namespace.clear();

        let func_decl = self.declare_fun(func, None);

        self.current_function = Some(func_decl);

        if let Some(block) = &func.block {
            let retblock = self.context.append_basic_block(func_decl, "retblock");
            self.function_retblock = Some(retblock);

            let function_entry_block = self.context.append_basic_block(func_decl, "entry");
            self.builder.position_at_end(function_entry_block);
            if let Some(ret_type) = &func.return_type {
                self.function_retval = Some(self.builder.build_alloca(self.gen_type(ret_type), ""));
            }

            let has_sret = func_decl.get_enum_attribute(
                inkwell::attributes::AttributeLoc::Param(0),
                inkwell::attributes::Attribute::get_named_enum_kind_id("sret")
            ).is_some();

            for (mut i, param) in func_decl.get_param_iter().enumerate() {
                if has_sret {
                    if i == 0 {
                        continue;
                    } else {
                        i -= 1;
                    }
                }
                self.namespace.insert(
                    if func.target_type.is_some() && i == 0 {
                        "self".to_string()
                    } else {
                        self.file.lexeme(&func.parameters[if func.target_type.is_some() {
                            i - 1
                        } else {
                            i
                        }].0.span).to_string()
                    },
                    param.into_pointer_value(),
                );
            }

            self.gen_stmt(&ast::Stmt {
                kind: ast::StmtKind::Block(block.clone()),
                pointer: 0..0,
            });

            self.builder.position_at_end(retblock);
            if func.return_type.is_some() {
                if has_sret {
                    self.builder.build_store(
                        func_decl.get_first_param().unwrap().into_pointer_value(),
                        self.builder.build_load(self.function_retval.unwrap(), ""),
                    );
                    self.builder.build_return(None);
                } else {
                    self.builder.build_return(Some(
                        &self.builder.build_load(self.function_retval.unwrap(), ""),
                    ));
                }
            } else {
                self.builder.build_return(None);
            }

            for block in func_decl.get_basic_blocks() {
                if block.get_terminator().is_none() {
                    self.builder.position_at_end(block);
                    self.builder.build_unconditional_branch(retblock);
                }
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

    fn gen_expr_as_ptr(&mut self, expr: &ast::Expr) -> inkwell::values::PointerValue<'ctx> {
        if expr.kind.is_lvalue() {
            match &expr.kind {
                ast::ExprKind::Var(var_expr) => {
                    if let ast::TypeKind::Fun(_) = &expr.typ.as_ref().unwrap().kind {
                        let wrapper_ptr = self.builder.build_alloca(self.gen_type(&expr.typ.as_ref().unwrap()), "");
                        let global_ptr = self
                            .module
                            .get_function(&format!("{}.{}", self.file.id(), self.file.lexeme(&var_expr.ident.span)))
                            .unwrap()
                            .as_global_value()
                            .as_pointer_value();
                        self.builder.build_store(wrapper_ptr, global_ptr);
                        wrapper_ptr
                    } else {
                        (*self
                            .namespace
                            .get(self.file.lexeme(&var_expr.ident.span))
                            .unwrap()
                        ).into()
                    }
                }
                ast::ExprKind::Idx(idx_expr) => {
                    let ptr_to_el = self.gen_ptr_to_arr_el(idx_expr);
                    ptr_to_el.into()
                }
                ast::ExprKind::Binary(get_expr) => {
                    let struct_value = self.gen_expr_as_ptr(&*get_expr.left);

                    if let ast::TypeKind::Struct(struct_type) =
                        &get_expr.left.typ.as_ref().unwrap().kind
                    {
                        if let ast::ExprKind::Var(var_expr) = &get_expr.right.kind {
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
                                .build_struct_gep(struct_value, member_idx as u32, "")
                                .unwrap();
                            member_ptr.into()
                        } else {
                            unreachable!()
                        }
                    } else {
                        unreachable!()
                    }
                }
                _ => panic!(
                    "pointer expression generation for lvalue kind {:?} has not been implemented",
                    expr.kind
                ),
            }
        } else {
            // Create a temp alloca for the rvalue
            let alloca = self
                .builder
                .build_alloca(self.gen_type(expr.typ.as_ref().unwrap()), "");
            self.builder.build_store(alloca, self.gen_expr(expr, false));
            alloca
        }
    }

    fn gen_ptr_to_arr_el(
        &mut self,
        idx_expr: &ast::IdxExpr,
    ) -> inkwell::values::PointerValue<'ctx> {
        let genned_target = self.gen_expr_as_ptr(&idx_expr.target);
        let genned_idx = self.gen_expr(&idx_expr.idx, false);

        let buffer = self
            .builder
            .build_load(
                self.builder.build_struct_gep(genned_target, 0, "").unwrap(),
                "",
            )
            .into_pointer_value();
        let ptr_to_el = unsafe {
            self.builder
                .build_gep(buffer, &[genned_idx.into_int_value()], "")
        };

        ptr_to_el
    }

    fn gen_expr(&mut self, expr: &ast::Expr, has_owner: bool) -> BasicValueEnum<'ctx> {
        let genned_expr = match &expr.kind {
            ast::ExprKind::Unary(unary_expr) => {
                if let token::TokenKind::Copy = &unary_expr.op.kind {
                    let expr_type = unary_expr.expr.typ.as_ref().unwrap();
                    let copy_func_name = if let ast::TypeKind::Struct(struct_type) = &expr_type.kind {
                        format!("{}.copy", struct_type.name)
                    } else {
                        format!("{}.{}.copy", self.file.id(), &expr_type.kind.type_name())
                    };

                    let target_value = self.gen_expr(&*unary_expr.expr, false);
                    let copied = self.builder.build_call(
                        self.module.get_function(&copy_func_name).unwrap(),
                        &vec![target_value.into()],
                        "",
                    ).try_as_basic_value().unwrap_left();

                    copied.into()
                } else {
                    let target_value = self.gen_expr(&*unary_expr.expr, true);

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
                        token::TokenKind::Tilde => {
                            let heap_ptr = self.builder.build_malloc(
                                self.gen_type(unary_expr.expr.typ.as_ref().unwrap()), 
                                "",
                            ).unwrap();

                            let casted_ptr = self.builder.build_bitcast(
                                heap_ptr,
                                self.gen_type(unary_expr.expr.typ.as_ref().unwrap())
                                    .ptr_type(AddressSpace::Generic),
                                "",
                            );

                            self.builder.build_store(casted_ptr.into_pointer_value(), target_value);

                            casted_ptr.into()
                        }
                        token::TokenKind::Caret => {
                            self.builder.build_load(target_value.into_pointer_value(), "")
                        }
                        _ => unreachable!(),
                    }
                }
            }
            ast::ExprKind::Binary(binary_expr) => match &binary_expr.op.kind {
                token::TokenKind::Equal => {
                    let target = &*binary_expr.left;
                    match &target.kind {
                        ast::ExprKind::Var(var_expr) => {
                            let ptr = *self.namespace.get(self.file.lexeme(&var_expr.ident.span)).unwrap();
                            self.builder.build_store(ptr, self.gen_expr(&*binary_expr.right, false));
                            self.builder.build_load(ptr, "")
                        }
                        ast::ExprKind::Idx(idx_expr) => {
                            let ptr_to_el = self.gen_ptr_to_arr_el(idx_expr);
                            self.builder.build_store(ptr_to_el, self.gen_expr(&*binary_expr.right, false));
                            self.builder.build_load(ptr_to_el, "")
                        }
                        ast::ExprKind::Binary(get_expr) => {
                            if get_expr.op.kind != token::TokenKind::Dot {
                                panic!("internal-error: can only generate assignment to `.` get expressions")
                            }

                            let struct_value = self.gen_expr_as_ptr(&*get_expr.left);
                            // TODO: drop() the old member value
                            let new_member_value = self.gen_expr(&*binary_expr.right, true);

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
                                            struct_value,
                                            member_idx as u32,
                                            "",
                                        ).unwrap();
                                    self.builder.build_store(member_ptr, new_member_value);

                                    if let ast::TypeKind::Struct(_) = &expr.typ.as_ref().unwrap().kind {
                                        member_ptr.into()
                                    } else {
                                        self.builder.build_load(member_ptr, "")
                                    }
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
                    let struct_value = self.gen_expr_as_ptr(&*binary_expr.left);

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
                                .build_struct_gep(struct_value, member_idx as u32, "")
                                .unwrap();
                            if let ast::TypeKind::Struct(_) = &expr.typ.as_ref().unwrap().kind {
                                member_ptr.into()
                            } else {
                                self.builder.build_load(member_ptr, "")
                            }
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
                    let left_value = self.gen_expr(&*binary_expr.left, false);
                    let right_value = self.gen_expr(&*binary_expr.right, false);

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
                    let left_value = self.gen_expr(&*binary_expr.left, false);
                    let right_value = self.gen_expr(&*binary_expr.right, false);

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

                    let left_value = self.gen_expr(&*binary_expr.left, false);
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
                    let right_value = self.gen_expr(&*binary_expr.right, false);
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
                    let left_value = self.gen_expr(&*binary_expr.left, false);
                    let right_value = self.gen_expr(&*binary_expr.right, false);
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

                self.builder.build_load(var_ptr, "")
            }
            ast::ExprKind::Call(call_expr) => {
                let mut return_value = None;

                if let ast::ExprKind::Var(var_expr) = &call_expr.callee.kind {
                    let func = if let Some(func) = self.module.get_function(&format!(
                        "{}.{}",
                        self.file.id(),
                        self.file.lexeme(&var_expr.ident.span)
                    )) {
                        Either::Left(func)
                    } else if let Some(func) = self
                        .module
                        .get_function(self.file.lexeme(&var_expr.ident.span))
                    {
                        Either::Left(func)
                    } else if let Some(fun_ptr) = self.namespace.get(self.file.lexeme(&var_expr.ident.span)) {
                        Either::Right(self.builder.build_load(*fun_ptr, "").into_pointer_value())
                    } else {
                        panic!("internal-error: uncaught undefined function")
                    };

                    let mut genned_args = call_expr
                        .args
                        .iter()
                        .map(|expr| self.gen_expr_as_ptr(expr).into())
                        .collect::<Vec<_>>();

                        let mut has_sret = false;
                    if let Some(return_type) = &expr.typ {
                        match &return_type.kind {
                            ast::TypeKind::Struct(_) | ast::TypeKind::Arr(_) => {
                                has_sret = true;
                                // C ABI: Struct returns are implemented as pointer first arg instead of an actual return
                                let struct_return_value = self.builder.build_alloca(self.gen_type(return_type), "");
                                genned_args.insert(0, struct_return_value.into());
                                self.builder.build_call(match func {
                                    Either::Left(func) => CallableValue::from(func),
                                    Either::Right(ptr) => CallableValue::try_from(ptr).unwrap(),
                                }, &genned_args, "");
                                return_value = Some(self.builder.build_load(struct_return_value, ""));
                            }
                            _ => {}
                        }
                    }

                    if !has_sret {
                        return_value = Some(
                            if let Either::Left(value) = self.builder.build_call(match func {
                                Either::Left(func) => CallableValue::from(func),
                                Either::Right(ptr) => CallableValue::try_from(ptr).unwrap(),
                            }, &genned_args, "").try_as_basic_value() {
                                value
                            } else {
                                self.context.i32_type().get_undef().into()
                            }
                        );
                    }
                } else if let ast::ExprKind::Binary(binary_expr) = &call_expr.callee.kind {
                    if let ast::ExprKind::Var(left_var_expr) = &binary_expr.left.kind {
                        if self
                            .file
                            .direct_deps
                            .get(self.file.lexeme(&left_var_expr.ident.span))
                            .is_some()
                        {
                            // Left of '.' is a module type ident
                            if let ast::ExprKind::Var(right_var_expr) = &binary_expr.right.kind
                            {
                                let func = self
                                    .module
                                    .get_function(&format!(
                                        "{}.{}",
                                        self.file
                                            .direct_deps
                                            .get(self.file.lexeme(&left_var_expr.ident.span))
                                            .unwrap()
                                            .id(),
                                        self.file.lexeme(&right_var_expr.ident.span)
                                    ))
                                    .unwrap();

                                let mut genned_args = call_expr
                                    .args
                                    .iter()
                                    .map(|expr| self.gen_expr_as_ptr(expr).into())
                                    .collect::<Vec<_>>();

                                let mut has_sret = false;
                                if let Some(return_type) = &expr.typ {
                                    match &return_type.kind {
                                        ast::TypeKind::Struct(_) | ast::TypeKind::Arr(_) => {
                                            has_sret = true;
                                            // C ABI: Struct returns are implemented as pointer first arg instead of an actual return
                                            let struct_return_value = self.builder.build_alloca(self.gen_type(return_type), "");
                                            genned_args.insert(0, struct_return_value.into());
                                            self.builder.build_call(func, &genned_args, "");
                                            return_value = Some(self.builder.build_load(struct_return_value, ""));
                                        }
                                        _ => {}
                                    }
                                }

                                if !has_sret {
                                    return_value = Some(
                                        if let Either::Left(value) = self
                                            .builder
                                            .build_call(func, &genned_args, "")
                                            .try_as_basic_value()
                                        {
                                            value
                                        } else {
                                            self.context.i32_type().get_undef().into()
                                        }
                                    );
                                }
                            }
                        } else if let ast::ExprKind::Var(var_expr) = &binary_expr.right.kind {
                            // Transform `target.method(42)` to `target.method(target, 42)`
                            let target_ptr = self.gen_expr_as_ptr(&*binary_expr.left);
                            let type_name = if let ast::TypeKind::Struct(struct_type) =
                                &binary_expr.left.typ.as_ref().unwrap().kind
                            {
                                format!("{}.{}", &struct_type.file_id, &struct_type.name)
                            } else {
                                binary_expr.left.typ.as_ref().unwrap().kind.type_name().to_string()
                            };
                            if let Some(func) = self.module.get_function(&format!(
                                "{}.{}",
                                type_name,
                                self.file.lexeme(&var_expr.ident.span)
                            )) {
                                let mut genned_args = call_expr
                                    .args
                                    .iter()
                                    .map(|expr| self.gen_expr_as_ptr(expr).into())
                                    .collect::<Vec<_>>();
                                genned_args.insert(0, target_ptr.into());

                                let mut has_sret = false;
                                if let Some(return_type) = &expr.typ {
                                    match &return_type.kind {
                                        ast::TypeKind::Struct(_) | ast::TypeKind::Arr(_) => {
                                            has_sret = true;
                                            // C ABI: Struct returns are implemented as pointer first arg instead of an actual return
                                            let struct_return_value = self.builder.build_alloca(self.gen_type(return_type), "");
                                            genned_args.insert(0, struct_return_value.into());
                                            self.builder.build_call(func, &genned_args, "");
                                            return_value = Some(self.builder.build_load(struct_return_value, ""));
                                        }
                                        _ => {}
                                    }
                                }

                                if !has_sret {
                                    return_value = Some(
                                        if let Either::Left(value) = self
                                            .builder
                                            .build_call(func, &genned_args, "")
                                            .try_as_basic_value()
                                        {
                                            value
                                        } else {
                                            self.context.i32_type().get_undef().into()
                                        }
                                    );
                                }
                            } else {
                                panic!("internal-error: uncaught undefined method")
                            }
                        } else {
                            panic!("internal-error: method name must be a var expr")
                        }
                    } else {
                        panic!("internal-error: calling non-getexpr binary expr has not been implemented yet")
                    }
                } else {
                    panic!("internal-error: can only call variable & get expressions")
                }

                return_value.unwrap()
            }
            ast::ExprKind::As(as_expr) => {
                let genned_expr = self.gen_expr(&as_expr.expr, false);

                if let ast::TypeKind::Prim(target_prim_type) = &as_expr.typ.kind {
                    if let ast::TypeKind::Prim(expr_prim_type) = &as_expr.expr.typ.as_ref().unwrap().kind {
                        match (expr_prim_type, target_prim_type) {
                            (ast::PrimType::UInt(expr_bit_size), ast::PrimType::UInt(target_bit_size))
                            | (ast::PrimType::Int(expr_bit_size), ast::PrimType::UInt(target_bit_size)) => {
                                if expr_bit_size < target_bit_size {
                                    self.builder.build_int_z_extend(
                                        genned_expr.into_int_value(),
                                        self.context.custom_width_int_type(*target_bit_size as u32),
                                        ""
                                    ).into()
                                } else if expr_bit_size < target_bit_size {
                                    self.builder.build_int_truncate(
                                        genned_expr.into_int_value(),
                                        self.context.custom_width_int_type(*target_bit_size as u32),
                                        ""
                                    ).into()
                                } else {
                                    if expr_prim_type != target_prim_type {
                                        // If going from uX to iX or iX to uX. This is handled naturally since LLVM only has generic "int" types
                                        genned_expr
                                    } else {
                                        unreachable!()
                                    }
                                }
                            }
                            (ast::PrimType::Int(expr_bit_size), ast::PrimType::Int(target_bit_size))
                            | (ast::PrimType::UInt(expr_bit_size), ast::PrimType::Int(target_bit_size)) => {
                                if expr_bit_size < target_bit_size {
                                    self.builder.build_int_s_extend(
                                        genned_expr.into_int_value(),
                                        self.context.custom_width_int_type(*target_bit_size as u32),
                                        ""
                                    ).into()
                                } else if expr_bit_size < target_bit_size {
                                    self.builder.build_int_truncate(
                                        genned_expr.into_int_value(),
                                        self.context.custom_width_int_type(*target_bit_size as u32),
                                        ""
                                    ).into()
                                } else {
                                    if expr_prim_type != target_prim_type {
                                        genned_expr
                                    } else {
                                        unreachable!()
                                    }
                                }
                            }

                            (ast::PrimType::Float(expr_bit_size), ast::PrimType::Float(target_bit_size)) => {
                                if expr_bit_size < target_bit_size {
                                    self.builder.build_float_ext(
                                        genned_expr.into_float_value(),
                                        self.context.f64_type(),
                                        ""
                                    ).into()
                                } else if expr_bit_size < target_bit_size {
                                    self.builder.build_float_trunc(
                                        genned_expr.into_float_value(),
                                        self.context.f32_type(),
                                        ""
                                    ).into()
                                } else {
                                    unreachable!()
                                }
                            },

                            (ast::PrimType::Float(_), ast::PrimType::Int(target_bit_size)) => {
                                self.builder.build_float_to_signed_int(
                                    genned_expr.into_float_value(),
                                    self.context.custom_width_int_type(*target_bit_size as u32),
                                    ""
                                ).into()
                            }
                            (ast::PrimType::Float(_), ast::PrimType::UInt(target_bit_size)) => {
                                self.builder.build_float_to_unsigned_int(
                                    genned_expr.into_float_value(),
                                    self.context.custom_width_int_type(*target_bit_size as u32),
                                    ""
                                ).into()
                            }
                            (ast::PrimType::Int(_), ast::PrimType::Float(target_bit_size)) => {
                                self.builder.build_signed_int_to_float(
                                    genned_expr.into_int_value(),
                                    if *target_bit_size == 32 {
                                        self.context.f32_type()
                                    } else {
                                        self.context.f64_type()
                                    },
                                    ""
                                ).into()
                            }
                            (ast::PrimType::UInt(_), ast::PrimType::Float(target_bit_size)) => {
                                self.builder.build_unsigned_int_to_float(
                                    genned_expr.into_int_value(),
                                    if *target_bit_size == 32 {
                                        self.context.f32_type()
                                    } else {
                                        self.context.f64_type()
                                    },
                                    ""
                                ).into()
                            }

                            // Rather than have an `_` this makes it clear we're only ignoring the `bool` options
                            (ast::PrimType::Int(_), ast::PrimType::Bool) => unreachable!(),
                            (ast::PrimType::UInt(_), ast::PrimType::Bool) => unreachable!(),
                            (ast::PrimType::Float(_), ast::PrimType::Bool) => unreachable!(),
                            (ast::PrimType::Bool, ast::PrimType::Int(_)) => unreachable!(),
                            (ast::PrimType::Bool, ast::PrimType::UInt(_)) => unreachable!(),
                            (ast::PrimType::Bool, ast::PrimType::Float(_)) => unreachable!(),
                            (ast::PrimType::Bool, ast::PrimType::Bool) => unreachable!(),
                        }
                    } else {
                        unreachable!()
                    }
                } else {
                    unreachable!()
                }
            },
            ast::ExprKind::Idx(idx_expr) => {
                let ptr_to_el = self.gen_ptr_to_arr_el(idx_expr);
                self.builder.build_load(ptr_to_el, "")
            }

            ast::ExprKind::StructLit(struct_lit) => {
                let struct_type = self.gen_type(&struct_lit.typ).into_struct_type();

                let mut genned_inits = Vec::new();
                for (_, init) in &struct_lit.inits {
                    genned_inits.push(self.gen_expr(init, true));
                }

                let struct_alloca = self.builder.build_alloca(struct_type, "");
                for (i, init) in genned_inits.iter().enumerate() {
                    self.builder.build_store(
                        unsafe {
                            self.builder.build_gep(
                                struct_alloca,
                                &vec![
                                    self.context.i32_type().const_zero(),
                                    self.context.i32_type().const_int(i as u64, false),
                                ],
                                "",
                            )
                        },
                        *init,
                    );
                }

                self.builder.build_load(struct_alloca, "")
            }
            ast::ExprKind::ArrLit(arr_lit) => {
                let expr_type = expr.typ.as_ref().unwrap();
                let prefixed_name = format!(".{}", expr_type.kind.type_name());
                let _ = self.gen_type(expr_type); // ensure that the array struct type exists

                if let ast::TypeKind::Arr(arr_type) = &expr.typ.as_ref().unwrap().kind {
                    if !arr_lit.elements.is_empty() {
                        let heap_ptr = self
                            .builder
                            .build_array_malloc(
                                self.gen_type(&arr_type.eltype), 
                                self.context.i64_type().const_int(arr_lit.elements.len() as u64, false), 
                                "",
                            )
                            .unwrap();

                        for (i, el) in arr_lit.elements.iter().enumerate() {
                            let genned_el = self.gen_expr(el, true);
                            let ptr_to_el_in_buffer = unsafe {
                                self.builder.build_gep(
                                    heap_ptr,
                                    &[self.context.i64_type().const_int(i as u64, false)],
                                    "",
                                )
                            };
                            self.builder.build_store(ptr_to_el_in_buffer, genned_el);
                        }

                        let arr_alloca = self
                            .builder
                            .build_alloca(self.module.get_struct_type(&prefixed_name).unwrap(), "");
                        self.builder.build_store(
                            self.builder.build_struct_gep(arr_alloca, 0, "").unwrap(),
                            heap_ptr,
                        );
                        self.builder.build_store(
                            self.builder.build_struct_gep(arr_alloca, 1, "").unwrap(),
                            self.context
                                .i64_type()
                                .const_int(arr_lit.elements.len() as u64, false),
                        );
                        self.builder.build_load(arr_alloca, "")
                    } else {
                        self.module
                            .get_struct_type(&prefixed_name)
                            .unwrap()
                            .const_named_struct(&[
                                self.gen_type(&arr_type.eltype)
                                    .ptr_type(AddressSpace::Generic)
                                    .const_null()
                                    .into(),
                                self.context.i64_type().const_int(0, false).into(),
                            ])
                            .into()
                    }
                } else {
                    unreachable!()
                }
            }
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
                    let str_len = (self.file.lexeme(&lit.token.span).len() as u64)-2;
                    let str_bytes = &self.file.lexeme(&lit.token.span).as_bytes()[1..=str_len as usize];

                    let global_str = self.module.add_global(
                        self.context
                            .i8_type()
                            .array_type(str_len as u32),
                        Some(AddressSpace::Const),
                        "",
                    );
                    global_str.set_initializer(
                        &self
                            .context
                            .const_string(str_bytes, false),
                    );

                    let ptr = self.builder.build_array_malloc(
                        self.context.i8_type(),
                        self.context.i64_type().const_int(
                            str_len,
                            false
                        ),
                        ""
                    ).unwrap();

                    let global_str_ptr = unsafe {
                        // SAFETY: Building a GEP is unsafe if the provided indices are incorrect. In this
                        // case that is not an issue since we're using `i32 0` as both the indices.
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
                    };

                    self.builder.build_memcpy(
                        ptr,
                        4,
                        global_str_ptr,
                        4,
                        self.context.i64_type().const_int(str_len, false),
                    ).unwrap();

                    let struct_type = self.gen_type(&ast::Type {
                        span: 0..0,
                        kind: ast::ArrType{
                            eltype: Box::new(ast::Type {
                                span: 0..0,
                                kind: ast::PrimType::UInt(8).into()
                            }),
                        }.into()
                    }).into_struct_type();

                    let struct_alloca = self.builder.build_alloca(struct_type, "");
                    
                    let buf_ptr = self.builder.build_struct_gep(struct_alloca, 0, "").unwrap();
                    let len_ptr = self.builder.build_struct_gep(struct_alloca, 1, "").unwrap();
                    let cap_ptr = self.builder.build_struct_gep(struct_alloca, 2, "").unwrap();
                    self.builder.build_store(buf_ptr, ptr);
                    self.builder.build_store(len_ptr, self.context.i64_type().const_int(str_len, false));
                    self.builder.build_store(cap_ptr, self.context.i64_type().const_int(str_len, false));
                    
                    self.builder.build_load(struct_alloca, "")
                }
                token::TokenKind::True => self.context.bool_type().const_int(1, false).into(),
                token::TokenKind::False => self.context.bool_type().const_int(0, false).into(),
                _ => panic!(
                    "internal-error: codegen has not been implemented for literal token type: {:?}",
                    lit
                ),
            },
        };

        if let Some(expr_type) = &expr.typ {
            let drop_func_name = if let ast::TypeKind::Struct(struct_type) = &expr_type.kind {
                format!("{}.{}.drop", &struct_type.file_id, &struct_type.name)
            } else {
                format!("{}.{}.drop", self.file.id(), &expr_type.kind.type_name())
            };

            if !expr.kind.is_lvalue() && !expr_type.kind.is_copyable() && !has_owner {
                let prev_block = self.builder.get_insert_block().unwrap();
    
                let alloca = self.builder.build_alloca(
                    self.gen_type(expr_type), 
                    "",
                );
                self.builder.build_store(alloca, genned_expr);
    
                self.builder.position_at_end(self.function_retblock.unwrap());
                self.builder.build_call(
                    self.module.get_function(&drop_func_name).unwrap(), 
                    &vec![alloca.into()], 
                    "",
                );
    
                self.builder.position_at_end(prev_block);
            } else if expr_type.kind.is_copyable() {
                if let Some(drop_func) = self.module.get_function(&drop_func_name) {
                    let prev_block = self.builder.get_insert_block().unwrap();
    
                    let alloca = self.builder.build_alloca(
                        self.gen_type(expr_type), 
                        "",
                    );
                    self.builder.build_store(alloca, genned_expr);
        
                    self.builder.position_at_end(self.function_retblock.unwrap());
                    self.builder.build_call(
                        drop_func, 
                        &vec![alloca.into()], 
                        "",
                    );
        
                    self.builder.position_at_end(prev_block);
                }
            }
        }

        genned_expr
    }

    fn gen_stmt(&mut self, stmt: &ast::Stmt) {
        match &stmt.kind {
            ast::StmtKind::Var(var_decl) => {
                let alloca = self.builder.build_alloca(
                    self.gen_type(var_decl.init.typ.as_ref().unwrap()),
                    self.file.lexeme(&var_decl.ident.span),
                );

                // technically the value does have an owner but that doesn't matter here
                let value = self.gen_expr(&var_decl.init, false);
                self.builder.build_store(alloca, value);
                self.namespace
                    .insert(self.file.lexeme(&var_decl.ident.span).to_string(), alloca);
            }
            ast::StmtKind::Expr(expr_stmt) => {
                self.gen_expr(&expr_stmt.expr, false);
            }
            ast::StmtKind::Return(ret_stmt) => {
                if let Some(value) = &ret_stmt.value {
                    // the calling frame owns the returned value, not the callee
                    self.builder
                        .build_store(self.function_retval.unwrap(), self.gen_expr(value, true));
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

                let cond_value = self.gen_expr(&if_stmt.condition, false);
                let then_block = self.context.append_basic_block(current_func, "then");
                let elif_blocks = if_stmt
                    .elif_stmts
                    .iter()
                    .map(|(_, _)| {
                        (
                            self.context.append_basic_block(current_func, "elif_cond"),
                            self.context.append_basic_block(current_func, "elif_block"),
                        )
                    })
                    .collect::<Vec<_>>();
                let else_block = self.context.append_basic_block(current_func, "else");
                let after_block = self.context.append_basic_block(current_func, "after");

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
                        self.gen_expr(&if_stmt.elif_stmts[i].0, false).into_int_value(),
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

                let cond_value = self.gen_expr(&while_stmt.condition, false);
                let while_block = self.context.append_basic_block(current_func, "loop");
                let after_block = self.context.append_basic_block(current_func, "after");

                self.builder.build_conditional_branch(
                    cond_value.into_int_value(),
                    while_block,
                    after_block,
                );

                self.builder.position_at_end(while_block);
                for stmt in &while_stmt.block.stmts {
                    self.gen_stmt(stmt)
                }
                let cond_value = self.gen_expr(&while_stmt.condition, false);
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

pub fn gen_modules<'ctx>(context: &'ctx Context, file: &ast::File) -> Vec<Module<'ctx>> {
    let mut modules = Vec::new();

    modules.push(gen_module(context, ".main", file));
    for (dep_name, dep_file) in &analyzer::get_deps(&file).unwrap() {
        let module = gen_module(context, dep_name, dep_file);
        modules.push(module);
    }

    modules
}

pub fn gen_module<'ctx>(
    context: &'ctx Context,
    module_name: &str,
    file: &ast::File,
) -> Module<'ctx> {
    let namespace = HashMap::<String, inkwell::values::PointerValue>::new();
    let module = context.create_module(module_name);
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

    for (_, imported_file) in &generator.file.direct_deps {
        for stmt in &imported_file.stmts {
            match &stmt.kind {
                ast::StmtKind::Fun(fun_decl) => {
                    if fun_decl.exported {
                        generator.declare_fun(fun_decl, Some(imported_file));
                    }
                }
                ast::StmtKind::Struct(struct_decl) => {
                    if struct_decl.exported {
                        generator.declare_struct(struct_decl, Some(imported_file));
                    }
                }
                _ => {}
            }
        }
        for stmt in &imported_file.stmts {
            if let ast::StmtKind::Struct(struct_decl) = &stmt.kind {
                if struct_decl.exported {
                    generator.gen_struct(struct_decl, Some(imported_file));
                }
            }
        }
    }

    // Forward declare all our declarations
    for stmt in &file.stmts {
        match &stmt.kind {
            ast::StmtKind::Fun(fun_decl) => {
                generator.declare_fun(fun_decl, None);
            }
            ast::StmtKind::Struct(struct_decl) => {
                generator.declare_struct(struct_decl, None);
            }
            ast::StmtKind::Import(_) => {
                // do nothing
            }
            _ => unreachable!(),
        }
    }

    for stmt in &file.stmts {
        match &stmt.kind {
            ast::StmtKind::Fun(fun_decl) => {
                generator.gen_fun(fun_decl);
            }
            ast::StmtKind::Struct(struct_decl) => {
                generator.gen_struct(struct_decl, None);
            }
            ast::StmtKind::Import(_) => {}
            _ => unreachable!(),
        }
    }

    module
}
