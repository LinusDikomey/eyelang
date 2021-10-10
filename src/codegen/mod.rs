/*use std::collections::HashMap;
use inkwell::{OptimizationLevel, builder::Builder, context::*, execution_engine::JitFunction, module::*, types::{BasicType, BasicTypeEnum, FunctionType}, values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue}};
use crate::{ast::{self, BlockItem, Expression, GenericScope}, error::{CompileError, EyeError}, lexer::tokens::SourcePos, types::{FloatType, IntType, Primitive}};

enum VariableValue<'ctx> {
    Arg(u32),
    Ptr(PointerValue<'ctx>)
}

type CodegenScope<'p, 'ctx> = GenericScope<'p, inkwell::types::FunctionType<'ctx>, BasicTypeEnum<'ctx>, VariableValue<'ctx>, BasicTypeEnum<'ctx>>;

pub fn generate_module<'ctx>(module: &'ctx ast::Module, ctx: &'ctx Context) -> Result<JitFunction<'ctx, unsafe extern "C" fn() -> i32>, EyeError> {
    let mut codegen = Codegen::new(&ctx, &module);
    codegen.get_function("main")?;
    codegen.finish();

    let execution_engine = codegen.llvm_module.create_jit_execution_engine(OptimizationLevel::None).unwrap();

    let main: JitFunction<'ctx, unsafe extern "C" fn() -> i32> = unsafe { execution_engine.get_function("main").unwrap() };
    Ok(main)
}


pub struct Codegen<'ctx> {
    ctx: &'ctx Context,
    module: &'ctx ast::Module,
    global_scope: CodegenScope<'ctx, 'ctx>,
    pub llvm_module: Module<'ctx>,
    builder: Builder<'ctx>,
    functions: HashMap<String, (FunctionValue<'ctx>, bool)>,
}

impl<'ctx> Codegen<'ctx> {

    pub fn new(ctx: &'ctx Context, module: &'ctx ast::Module) -> Self {
        let global_scope = CodegenScope::new();
        Self { ctx, module, global_scope, llvm_module: ctx.create_module("main"), builder: ctx.create_builder(), functions: HashMap::new() }
    }

    pub fn get_function(&mut self, name: &str) -> Result<FunctionValue<'ctx>, EyeError> {
        if let Some(existing_func) = self.functions.get(name) {
            Ok(existing_func.0)
        } else {
            let func = self.module.functions.get(name).ok_or_else(|| EyeError::CompileError(CompileError::UnknownFunction(name.to_owned()), SourcePos::new(0, 0), SourcePos::new(0, 0)))?;
            let func_type = self.get_function_type(func)?;
            let llvm_func = self.llvm_module.add_function(name, func_type, None);
            
            self.functions.insert(name.to_owned(), (llvm_func, false));
            Ok(llvm_func)
        }
        
    }

    fn get_function_type(&mut self, func: &ast::Function) -> Result<FunctionType<'ctx>, EyeError> {
        let return_type = self.get_type(&func.return_type)?;
        let mut arg_types = Vec::with_capacity(func.args.len());
        for (_name, ty) in &func.args {
            arg_types.push(self.get_type(ty)?)
        }
        Ok(return_type.fn_type(&arg_types, false))
    }

    fn get_type(&self, ty: &ast::UnresolvedType) -> Result<BasicTypeEnum<'ctx>, EyeError> {
        match ty {
            ast::UnresolvedType::Primitive(primitive) => {
                Ok(match primitive {
                    Primitive::Integer(int_type) => match int_type {
                            IntType::U8   | IntType::I8   => self.ctx.i8_type().as_basic_type_enum(),
                            IntType::U16  | IntType::I16  => self.ctx.i16_type().as_basic_type_enum(),
                            IntType::U32  | IntType::I32  => self.ctx.i32_type().as_basic_type_enum(),
                            IntType::U64  | IntType::I64  => self.ctx.i64_type().as_basic_type_enum(),
                            IntType::U128 | IntType::I128 => self.ctx.i128_type().as_basic_type_enum(),
                    },
                    Primitive::Float(float_type) => match float_type {
                        FloatType::F32 => self.ctx.f32_type().as_basic_type_enum(),
                        FloatType::F64 => self.ctx.f64_type().as_basic_type_enum()
                    }
                    Primitive::Bool => self.ctx.bool_type().as_basic_type_enum(),
                    _ => todo!()
                })
            },
            ast::UnresolvedType::Unresolved(name) => {
                let type_struct: &ast::Struct = self.module.structs.get(name).ok_or_else(|| EyeError::CompileError(CompileError::UnknownType(name.clone()), SourcePos::new(0, 0), SourcePos::new(0, 0)))?;
                let mut member_types: Vec<BasicTypeEnum> = Vec::with_capacity(type_struct.members.len());
                for (_member_name, member_type) in &type_struct.members {
                    let resolved_type = self.get_type(member_type)?;
                    member_types.push(resolved_type);
                }

                Ok(self.ctx.struct_type(&member_types, false).as_basic_type_enum())
            }
        }
    }

    pub fn finish(&mut self) {
        for (name, (value, body_generated)) in &self.functions {
            if !*body_generated {
                self.generate_func_body(*value, &self.module.functions[name]);
            }
        }
        self.functions.iter_mut().for_each(|f| f.1.1 = true);   // set body_generated to true for all functions
    }
    
    fn generate_func_body(&self, func_val: FunctionValue<'ctx>, func: &ast::Function) {
        let mut func_scope = self.global_scope.create_inner();
        for (i, (arg_name, _)) in func.args.iter().enumerate() {
            func_scope.register_variable(arg_name.clone(), VariableValue::Arg(i as u32), true);
        }
        self.gen_block(func_val, &func.body, &&func_scope)
    }

    fn gen_block(&self, func: FunctionValue<'ctx>, block: &ast::Block, parent: &CodegenScope<'_, 'ctx>) {
        let mut scope = parent.create_inner();

        let bb = self.ctx.append_basic_block(func, "block");
        self.builder.position_at_end(bb);
        for item in &block.items {
            self.gen_block_item(func, item, &mut scope);
        }
    }

    fn gen_block_item(&self, func: FunctionValue<'ctx>, item: &ast::BlockItem, scope: &mut CodegenScope<'_, 'ctx>) {
        match item {
            BlockItem::Block(block) => self.gen_block(func, block, scope),
            BlockItem::Declare(name, type_opt, value_opt) => {
                let ty = self.get_type(type_opt.as_ref().unwrap()).unwrap();
                let ptr = self.builder.build_alloca(ty, "");
                if let Some(value) = value_opt {
                    let expr = self.gen_expr(func, &value, scope).unwrap();
                    self.builder.build_store(ptr, expr);
                }
                scope.register_variable(name.clone(), VariableValue::Ptr(ptr), value_opt.is_some())
            },
            BlockItem::Expression(expr) => { self.gen_expr(func, expr, scope); },
            BlockItem::Assign(name, val) => {
                let var = &scope.resolve_variable(name).unwrap().0;
                match var {
                    VariableValue::Arg(_) => panic!("Can't assign to arguments right now"),
                    &VariableValue::Ptr(ptr) => {
                        self.builder.build_store(ptr, self.gen_expr(func, val, scope).unwrap());
                    }
                }
            }
        }
    }

    fn gen_expr(&self, func: FunctionValue<'ctx>, expr: &ast::Expression, scope: &mut CodegenScope<'_, 'ctx>) -> Option<BasicValueEnum> {
        match &expr {
            Expression::IntLiteral(val) => {
                use IntType::*;
                Some(match val.ty.unwrap() {
                    U8   | I8   => self.ctx.i8_type()  .const_int(val.unsigned_val as u64, val.sign),
                    U16  | I16  => self.ctx.i16_type() .const_int(val.unsigned_val as u64, val.sign),
                    U32  | I32  => self.ctx.i32_type() .const_int(val.unsigned_val as u64, val.sign),
                    U64  | I64  => self.ctx.i64_type() .const_int(val.unsigned_val as u64, val.sign),
                    U128 | I128 => self.ctx.i128_type().const_int(val.unsigned_val as u64, val.sign),
                }.as_basic_value_enum())
            },
            Expression::BoolLiteral(val) => Some(self.ctx.bool_type().const_int(if *val {1} else {0}, false).as_basic_value_enum()),
            Expression::FloatLiteral(val) => {
                Some(match val.ty.unwrap() {
                    FloatType::F32 => self.ctx.f32_type(),
                    FloatType::F64 => self.ctx.f64_type()
                }.const_float(val.val).as_basic_value_enum())
            },
            Expression::Variable(var) => {
                Some(match scope.resolve_variable(var).unwrap().0 {
                    VariableValue::Arg(index) => func.get_nth_param(index).unwrap(),
                    VariableValue::Ptr(ptr) => self.builder.build_load(ptr, "")
                })
            },
            Expression::If(_, _, _) => todo!(),
            Expression::Return(ret_value) => {
                match ret_value {
                    Some(ret) => self.builder.build_aggregate_return(&[self.gen_expr(func, ret, scope).unwrap()]),
                    None => self.builder.build_return(None)
                };
                None
            },
            _ => todo!()
        }
    }

}
*/