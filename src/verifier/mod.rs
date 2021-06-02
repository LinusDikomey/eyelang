use std::u128;

use crate::{ast::{Block, BlockItem, Expression, Function, Module, ResolvedType, Scope, VariableType}, error::{CompileError, EyeError}, types::Primitive};


pub fn verify(module: &Module) -> Result<(), EyeError> {
    let mut global_scope = module.clone().to_scope();
    verify_module(&mut global_scope, module)?;
    Ok(())
}

struct FunctionType {
    return_type: ResolvedType,
    args: Vec<(String, ResolvedType)>
}

fn verify_module(scope: &mut Scope, module: &Module) -> Result<(), EyeError> {
    for (_name, func) in &module.functions {
        verify_func(scope, func)?;
    }
    Ok(())
}

fn verify_func(scope: &mut Scope, func: &Function) -> Result<FunctionType, EyeError> {
    let func_type = resolve_function_type(scope, func)?;
    let mut function_scope = scope.create_function(func_type.return_type.clone());
    verify_block(&mut function_scope, &func.body)?;
    Ok(func_type)
}

fn verify_block(scope: &mut Scope, block: &Block) -> Result<(), EyeError> {
    let mut scope: Scope<'_> = scope.create_inner();

    for item in &block.items {
        let result = verify_block_item(&mut scope, item);
        if let Err(err) = result {
            return Err(err);
        }
        drop(result);
    }
    Ok(())
}

fn verify_block_item(scope: &mut Scope, item: &BlockItem) -> Result<(), EyeError> {
    match item {
        BlockItem::Block(inner_block) => verify_block(scope, &inner_block)?,
        BlockItem::Declare(name, ty, assign_val) => {
            let variable_type = match ty {
                Some(ty) => {
                    let resolved_type = scope.resolve_type(ty)?;
                    if let Some(assign_expr) = assign_val {
                        let mut var_ty = VariableType::Known(resolved_type);
                        verify_expr(scope, assign_expr, &mut var_ty)?;
                        var_ty
                    } else {
                        VariableType::Known(resolved_type)
                    }
                },
                None => { 
                    if let Some(assign_expr) = assign_val {
                        let mut var_ty = VariableType::Any;
                        verify_expr(scope, assign_expr, &mut var_ty)?;
                        var_ty
                    } else {
                        VariableType::Any
                    }
                }
            };
            scope.register_variable(name.clone(), variable_type, assign_val.is_some());
        },
        BlockItem::Assign(name, val) => {
            let (ty, _assigned) = scope.resolve_variable(name)?;
            let mut ty_clone = ty.clone();
            verify_expr(scope, val, &mut ty_clone)?;
            //TODO: HERE
        },
        BlockItem::Expression(expr) => {
            verify_expr(scope, &expr, &mut VariableType::Any)?;
        }
    }
    Ok(())
}

/// returns: wether the expected type was modified
fn verify_expr(scope: &mut Scope, expr: &Expression, expected_type: &mut VariableType) -> Result<bool, EyeError> {
    print!("Verifying expression: expected type: {:?}, expr: {:?}", expected_type, expr);
    let ty = match expr {
        Expression::Return(return_val) => {
            if let Some(expected_return_type) = scope.expected_return_type() {
                if let Some(return_expr) = return_val {
                    verify_expr(scope, return_expr, &mut VariableType::Known(expected_return_type))?;
                } else {
                    return Err(EyeError::CompileErrorNoPos(CompileError::MissingReturnValue))
                }
            }
            // a return never returns anyting from the expression itself because it exits the function
            VariableType::Known(ResolvedType::Primitive(Primitive::Void))
        },
        Expression::IntLiteral(int_literal) => {
            if let Some(int_type) = int_literal.ty {
                VariableType::Known(ResolvedType::Primitive(Primitive::Integer(int_type)))
            } else {
                int_literal.as_variable_type()
            }
        },
        Expression::FloatLiteral(float_literal) => {
            if let Some(float_type) = float_literal.ty {
                VariableType::Known(ResolvedType::Primitive(Primitive::Float(float_type)))
            } else {
                match expected_type {
                    VariableType::Known(ResolvedType::Primitive(Primitive::Float(float_type))) => {
                        if float_literal.fits_into_type(float_type) {
                            VariableType::Known(ResolvedType::Primitive(Primitive::Float(*float_type)))
                        } else {
                            return Err(EyeError::CompileErrorNoPos(CompileError::FloatLiteralOutOfRange))
                        }
                    },
                    VariableType::Float(_) | VariableType::Any => {
                        VariableType::Float(float_literal.clone())
                    },
                    _ => return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType)),
                }
            }
        },
        Expression::StringLiteral(_) => VariableType::Known(ResolvedType::Primitive(Primitive::String)),
        Expression::BoolLiteral(_) => VariableType::Known(ResolvedType::Primitive(Primitive::Bool)),
        Expression::Variable(name) => {
            let (var_type, assigned) = scope.resolve_variable(name)?;   //TODO: var_type could be updated based on expected type here
            if !assigned {
                eprintln!("Tried to use a variable that could be unassigned"); //TODO: turn this into a hard error when assigned check is complete
                //return Err(EyeError::CompileErrorNoPos(CompileError::UseOfUnassignedVariable));
            }
            let var_type_clone = var_type.clone();
            if expected_type.is_more_precise_than(&var_type_clone) {
                scope.specify_variable_type(name, expected_type.clone());
            }
            var_type_clone
        }
    };
    let new_expected_type: Option<VariableType> = match expected_type {
        VariableType::Any => Some(ty),
        VariableType::Integer(unsigned_val, sign) => {
            match ty {
                VariableType::Integer(found_unsigned_val, found_sign) => Some(VariableType::Integer(u128::max(*unsigned_val, found_unsigned_val), *sign | found_sign)), // both expected and found are variable integer types, always take bigger value
                _ => return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))
            }
        },
        VariableType::Float(_literal) => {
            match ty {
                VariableType::Float(_found_literal) => None, //don't change max value information right now //TODO: float range type checking
                _ => return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))
            }
        },
        VariableType::Known(expected) => {  // the expected type is precisely known
            match expected {
                ResolvedType::Primitive(Primitive::Integer(expected_int_type)) => {   // an integer type is expected
                    match ty {
                        VariableType::Integer(val, sign) => {       // a dynamic integer type was provided, check size constraints of expected type and continue
                            if sign && !expected_int_type.is_signed() || val > expected_int_type.max_val() {
                                return Err(EyeError::CompileErrorNoPos(CompileError::IntLiteralOutOfRange))
                            }
                            // if the new value would fit into the integer type, proceed
                            None
                        },
                        VariableType::Known(ResolvedType::Primitive(Primitive::Integer(found_int_type))) => {    // the provided value is also a concrete integer type, only continue if they match
                            if *expected_int_type != found_int_type {
                                return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))
                            }
                            None
                        }
                        _ => return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))
                    }
                },
                ResolvedType::Primitive(Primitive::Float(expected_float_type)) => {   // an float type is expected
                    match ty {
                        VariableType::Float(found_literal) => {       // a dynamic float type was provided, check size constraints of expected type and continue  //TODO: size constraints not yet implemented
                            if !found_literal.fits_into_type(expected_float_type) {
                                return Err(EyeError::CompileErrorNoPos(CompileError::IntLiteralOutOfRange))
                            }
                            // if the new value would fit into the float type, proceed
                            None
                        },
                        VariableType::Known(ResolvedType::Primitive(Primitive::Float(found_float_type))) => {    // the provided value is also a concrete integer type, only continue if they match
                            if *expected_float_type != found_float_type {
                                return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))
                            }
                            None
                        }
                        _ => return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))
                    }
                },
                _ => {
                    match ty {
                        VariableType::Any => unreachable!(), // an expression should never contain an any type (for now)
                        VariableType::Known(found_type) => {
                            if *expected == found_type {  // if the type of the expression is also known, proceed if they match
                                None
                            } else {
                                return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))
                            }
                        },
                        _ => return Err(EyeError::CompileErrorNoPos(CompileError::UnexpectedType))      // not matching
                    }
                }
            }
        }
    };
    if let Some(new) = new_expected_type {
        println!("   ... new type: {:?}", new);
        *expected_type = new;
        Ok(true)
    } else {
        println!("   ... unchanged");
        Ok(false)
    }
}

fn resolve_function_type(scope: &Scope, func: &Function) -> Result<FunctionType, EyeError> {
    let return_type = scope.resolve_type(&func.return_type)?;
    let mut args = Vec::with_capacity(func.args.len());
    for (name, ty) in &func.args {
        args.push((name.clone(), scope.resolve_type(ty)?));
    }
    Ok(FunctionType{return_type, args})
}

/*fn resolve_function_type_by_name<'a>(scope: &'a Scope, name: &str) -> Result<(FunctionType, Function), EyeError> {
    let func = scope.resolve_function(name)?.clone();
    
    Ok((resolve_function_type(scope, &func)?, func))
}*/