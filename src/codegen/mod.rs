
use std::collections::HashMap;

//use inkwell::
use inkwell::{OptimizationLevel, builder::Builder, context::*, execution_engine::JitFunction, module::*, types::{BasicType, BasicTypeEnum, FunctionType}, values::{BasicValue, BasicValueEnum, FunctionValue}};

use crate::{ast::{self, BlockItem, Expression}, error::{CompileError, EyeError}, lexer::tokens::SourcePos, types::{IntType, Primitive}};

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
    pub llvm_module: Module<'ctx>,
    builder: Builder<'ctx>,
    functions: HashMap<String, (FunctionValue<'ctx>, bool)>,
}

impl<'ctx> Codegen<'ctx> {

    pub fn new(ctx: &'ctx Context, module: &'ctx ast::Module) -> Self {
        Self { ctx, module, llvm_module: ctx.create_module("main"), builder: ctx.create_builder(), functions: HashMap::new() }
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
                    Primitive::Integer(IntType::I8) => self.ctx.i8_type().as_basic_type_enum(),
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
    
    fn generate_func_body(&self, func_val: FunctionValue, func: &ast::Function) {
        self.gen_block(func_val, &func.body)
    }

    fn gen_block(&self, func: FunctionValue, block: &ast::Block) {
        let bb = self.ctx.append_basic_block(func, "block");
        self.builder.position_at_end(bb);
        for item in &block.items {
            self.gen_block_item(func, item);
        }
    }

    fn gen_block_item(&self, func: FunctionValue, item: &ast::BlockItem) {
        match item {
            BlockItem::Block(block) => self.gen_block(func, block),
            BlockItem::Declare(name, type_opt, value_opt) => {
                todo!()
            },
            BlockItem::Expression(expr) => todo!(),//self.gen_expr(func, expr) ,
            BlockItem::Assign(name, val) => todo!()
        }
    }

    /*fn gen_expr(&self, func: FunctionValue, expr: &ast::Expression) -> Result<BasicValueEnum, EyeError> {
        match expr {
            Expression::BoolLiteral(val) => Ok(self.ctx.bool_type().const_int(if *val {1} else {0}, false).as_basic_value_enum()),
            Expression::FloatLiteral(float) => {}
        }
    }*/

}

pub fn gen(module: &Module) {
    let mut context = Context::create();
    gen_module(&mut context);
}


fn gen_module(ctx: &mut Context) {
    let module = ctx.create_module("main");
}