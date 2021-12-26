use core::panic;
use std::{fmt, collections::HashMap, io::{stdin, BufRead, Write}};

use crate::{typing::tir::{self, Module, TypeRef}, ast::{self, BlockItem, UnresolvedType}, types::{IntType, FloatType, Primitive}, lexer::tokens::Operator};

#[derive(Clone, Debug)]
pub enum Value {
    Unit,
    Unassigned,

    Function(tir::Function),
    Type(tir::Type),

    I8(i8),
    I16(i16),
    I32(i32),
    I64(i64),
    I128(i128),

    U8(u8),
    U16(u16),
    U32(u32),
    U64(u64),
    U128(u128),
    UnsizedInt(i128),

    F32(f32),
    F64(f64),
    UnsizedFloat(f64),

    String(String),
    Bool(bool),

    Struct(HashMap<String, Value>),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Value::*;
        match self {
            Unit => write!(f, "()"),
            Unassigned => write!(f, "[UNASSIGNED]"),
            Function(func) => write!(f, "({}) -> {}", 
                func.header().params.iter()
                    .map(|p| format!("{}: {}", p.0, p.1))
                    .intersperse(", ".to_owned()).collect::<std::string::String>(),
                func.header().return_type),
            Type(tir::Type::Struct(struc)) => write!(f, "{}", struc),
        
            I8(x) => write!(f, "{}", x),
            I16(x) => write!(f, "{}", x),
            I32(x) => write!(f, "{}", x),
            I64(x) => write!(f, "{}", x),
            I128(x) => write!(f, "{}", x),
        
            U8(x) => write!(f, "{}", x),
            U16(x) => write!(f, "{}", x),
            U32(x) => write!(f, "{}", x),
            U64(x) => write!(f, "{}", x),
            U128(x) => write!(f, "{}", x),
            UnsizedInt(x) => write!(f, "UNSIZED[{}]", x),
        
            F32(x) => write!(f, "{}", x),
            F64(x) => write!(f, "{}", x),
            UnsizedFloat(x) => write!(f, "UNSIZED[{}]", x),
        
            String(s) => write!(f, "{}", s),
            Bool(b) => write!(f, "{}", b),
        
            Struct(fields) => {
                write!(f, "{{\n")?;
                for (name, val) in fields {
                    write!(f, "\t{}: {}", name, val)?;
                }
                write!(f, "}}")
            }
        }
    }
}

pub struct Scope {
    parent: Option<*mut Scope>,
    values: HashMap<String, Value>,
    expected_return_type: Option<UnresolvedType>
}
impl Scope {
    pub fn new() -> Self {
        Self { parent: None, values: HashMap::new(), expected_return_type: None }
    }
    pub fn with_parent(parent: &mut Scope) -> Self {
        Self { parent: Some(parent as _), values: HashMap::new(), expected_return_type: None }
    }
    pub fn from_module(module: Module) -> Self {
        let mut s = Scope::new();
        for (name, func) in module.functions {
            s.values.insert(name.into_inner(), Value::Function(func));
        }
        for (name, ty) in module.types {
            s.values.insert(name.into_inner(), Value::Type(ty));
        }
        s
    }
    pub fn resolve(&self, name: &str) -> (&Value, &Self) {
        if let Some(v) = self.values.get(name) {
            (v, self)
        } else {
            if let Some(parent) = &self.parent {
                unsafe { &**parent }.resolve(name)
            } else {
                panic!("Invalid reference: {}", name)
            }
        }
    }
    pub fn resolve_mut(&mut self, name: &str) -> &mut Value {
        if let Some(v) = self.values.get_mut(name) {
            v
        } else {
            if let Some(parent) = &mut self.parent {
                unsafe { &mut **parent }.resolve_mut(name)
            } else {
                panic!("Invalid reference: {}", name)
            }
        }
    }

    pub fn outer(&mut self) -> &mut Scope {
        match self.parent {
            Some(parent) => unsafe { &mut *parent }.outer(),
            None => self
        }
    }

    pub fn expected_return_type(&self) -> &UnresolvedType {
        match &self.expected_return_type {
            Some(ty) => ty,
            None => if let Some(parent) = self.parent {
                unsafe { &*parent }.expected_return_type()
            } else {
                panic!("Missing expected return type")
            }
        }
    }
}

pub fn eval_function<'a>(scope: &mut Scope, f: &tir::Function, args: Vec<Value>) -> Value {
    match &f.intrinsic {
        Some(intrinsic) => {
            let val = match intrinsic {
                tir::Intrinsic::Print => {
                    let newline = match args.len() {
                        1 => true,
                        2 => {
                            let Value::Bool(newline) = &args[1] else { panic!("invalid print() arg")};
                            *newline
                        }
                        _ => panic!("Invalid print() arg count")
                    };
                    print!("{}{}", &args[0], if newline {"\n"} else {""});
                    Value::Unit
                },
                tir::Intrinsic::Read => {
                    match args.len() {
                        0 => {}
                        1 => {
                            let Value::String(s) = &args[0] else { panic!("Invalid read() arg") };
                            print!("{}", s);
                            std::io::stdout().flush().unwrap();
                        }
                        _ => panic!("Invalid read() arg count")
                    }
                    Value::String(stdin().lock().lines().next().unwrap().unwrap())
                }
                tir::Intrinsic::Parse => {
                    assert_eq!(args.len(), 1);
                    let Value::String(s) = &args[0] else { panic!("Invalid parse() argument") };
                    Value::I32(s.parse().unwrap())
                }
            };
            return val;
        },
        None => ()
    }
    assert_eq!(f.header.params.len(), args.len());

    let mut scope = Scope::with_parent(scope);
    scope.expected_return_type = Some(as_unresolved(&f.header().return_type));
    for ((arg_name, _), arg_val) in f.header.params.iter().zip(args) {
        scope.values.insert(arg_name.clone(), arg_val);
    }

    let v = eval_block(&mut scope, &f.ast.body).value();
    v
}

#[derive(Debug)]
enum ValueOrReturn {
    Value(Value),
    Return(Value)
}
impl<'a> ValueOrReturn {
    fn value(self) -> Value {
        match self {
            Self::Value(v) | Self::Return(v) => v
        }
    }
}

macro_rules! get_or_ret {
    ($e: expr) => {
        match $e {
            ValueOrReturn::Value(v) => v,
            ret@ValueOrReturn::Return(_) => return ret
        }
    };
}

fn eval_block(scope: &mut Scope, block: &ast::Block) -> ValueOrReturn {
    let mut scope: Scope = Scope::with_parent(scope);
    for item in &block.items {
        match item {
            BlockItem::Block(block) => {
                get_or_ret!(eval_block(&mut scope, block));
            },
            BlockItem::Declare(name, ty, expr) => {
                let val = if let Some(e) = expr {
                    get_or_ret!(eval_expr(&mut scope, e, ty.as_ref()))
                } else {
                    Value::Unassigned 
                };
                scope.values.insert(name.clone(), val);
            },
            BlockItem::Assign(var, expr) => {
                *scope.resolve_mut(var) = get_or_ret!(eval_expr(&mut scope, expr, None)); //TODO set expected type from value
            },
            BlockItem::Expression(expr) => {
                get_or_ret!(eval_expr(&mut scope, expr, None));
            }
        }
    }
    ValueOrReturn::Value(Value::Unit)
}

fn eval_expr(scope: &mut Scope, expr: &ast::Expression, mut expected: Option<&UnresolvedType>) -> ValueOrReturn {
    use ast::Expression::*;
    let val = match expr {
        Return(ret) => {
            return ValueOrReturn::Return(match ret {
                Some(ret) => eval_expr(scope, ret, Some(&scope.expected_return_type().clone())).value(),
                None => Value::Unit
            });
        },
        IntLiteral(lit) => {
            match lit.ty {
                Some(IntType::I8) => Value::I8(lit.unsigned_val as i8 * if lit.sign {-1} else {1}),
                Some(IntType::I16) => Value::I16(lit.unsigned_val as i16 * if lit.sign {-1} else {1}),
                Some(IntType::I32) => Value::I32(lit.unsigned_val as i32 * if lit.sign {-1} else {1}),
                Some(IntType::I64) => Value::I64(lit.unsigned_val as i64 * if lit.sign {-1} else {1}),
                Some(IntType::I128) => Value::I128(lit.unsigned_val as i128 * if lit.sign {-1} else {1}),

                Some(IntType::U8) => Value::U8(lit.unsigned_val as u8),
                Some(IntType::U16) => Value::U16(lit.unsigned_val as u16),
                Some(IntType::U32) => Value::U32(lit.unsigned_val as u32),
                Some(IntType::U64) => Value::U64(lit.unsigned_val as u64),
                Some(IntType::U128) => Value::U128(lit.unsigned_val as u128),

                None => Value::UnsizedInt(lit.unsigned_val as i128 * if lit.sign {-1} else {1})
            }
        },
        FloatLiteral(lit) => {
            match lit.ty {
                Some(FloatType::F32) => Value::F32(lit.val as f32),
                Some(FloatType::F64) => Value::F64(lit.val),
                None => Value::UnsizedFloat(lit.val)
            }
        },
        StringLiteral(s) => Value::String(s.clone()),
        BoolLiteral(b) => Value::Bool(*b),
        Variable(name) => scope.resolve(name).0.clone(),
        If(cond, then_block, else_block) => {
            let Value::Bool(cond_true) = get_or_ret!(
                eval_expr(scope, cond, Some(&UnresolvedType::Primitive(Primitive::Bool)))
            ) else { panic!("bool expected in if condition!") };
            if cond_true {
                get_or_ret!(eval_block(scope, then_block))
            } else {
                if let Some(else_block) = else_block {
                    get_or_ret!(eval_block(scope, else_block))
                } else {
                    Value::Unit
                }
            }
        }
        FunctionCall(expr, args) => {
            let func = get_or_ret!(eval_expr(scope, expr, None));
            let mut arg_vals = Vec::with_capacity(args.len());
            match func {
                Value::Function(func) => {
                    for (arg, (_, ty)) in args.iter().zip(func.header().params.iter()) {
                        arg_vals.push(get_or_ret!(eval_expr(scope, arg, Some(&as_unresolved(ty)))));
                    }
                    eval_function(scope.outer(), &func, arg_vals) //TODO: proper scope
                }
                _ => panic!("Tried to call non-function value as function")
            }
        }
        BinOp(op, sides) => {
            let (lhs, rhs) = &**sides;
            if let Operator::LT | Operator::LE | Operator::GT | Operator::GE = op {
                expected = None;
            };
            let lhs = get_or_ret!(eval_expr(scope, lhs, expected));
            let rhs_expected = if expected.is_none() {
                use Value::*;
                match lhs {
                    U8(_) => Some(Primitive::Integer(IntType::U8)),
                    U16(_) => Some(Primitive::Integer(IntType::U16)),
                    U32(_) => Some(Primitive::Integer(IntType::U32)),
                    U64(_) => Some(Primitive::Integer(IntType::U64)),
                    U128(_) => Some(Primitive::Integer(IntType::U128)),
                    
                    I8(_) => Some(Primitive::Integer(IntType::I8)),
                    I16(_) => Some(Primitive::Integer(IntType::I16)),
                    I32(_) => Some(Primitive::Integer(IntType::I32)),
                    I64(_) => Some(Primitive::Integer(IntType::I64)),
                    I128(_) => Some(Primitive::Integer(IntType::I128)),

                    F32(_) => Some(Primitive::Float(FloatType::F32)),
                    F64(_) => Some(Primitive::Float(FloatType::F64)),

                    _ => None
                }.map(|p| UnresolvedType::Primitive(p))
            } else { expected.map(|t| t.clone()) };
            let rhs = get_or_ret!(eval_expr(scope, rhs, rhs_expected.as_ref()));
            macro_rules! op_match {
                ($($p: tt)*) => {
                    match (op, lhs, rhs) {
                        $((Operator::Add, Value::$p(l), Value::$p(r)) => Value::$p(l + r),)*
                        $((Operator::Sub, Value::$p(l), Value::$p(r)) => Value::$p(l - r),)*
                        $((Operator::Mul, Value::$p(l), Value::$p(r)) => Value::$p(l * r),)*
                        $((Operator::Div, Value::$p(l), Value::$p(r)) => Value::$p(l / r),)*
                        
                        $((Operator::LT, Value::$p(l), Value::$p(r)) => Value::Bool(l <  r),)*
                        $((Operator::LE, Value::$p(l), Value::$p(r)) => Value::Bool(l <= r),)*
                        $((Operator::GT, Value::$p(l), Value::$p(r)) => Value::Bool(l >  r),)*
                        $((Operator::GE, Value::$p(l), Value::$p(r)) => Value::Bool(l >= r),)*

                        
                        (op, l, r) => panic!("Invalid operation: {:?} for values: {:?} and {:?}", op, l, r)
                    }
                }
            }
            op_match!(U8 U16 U32 U64 U128 I8 I16 I32 I64 I128 F32 F64)
        }
    };

    //println!("Adjusting expr val: {:?}, expected: {:?}", val, expected);
    let val = match val {
        Value::UnsizedInt(int_val) => match expected {
            Some(UnresolvedType::Primitive(Primitive::Integer(int))) => match int {
                IntType::U8 => Value::U8(int_val.try_into().unwrap()),
                IntType::U16 => Value::U16(int_val.try_into().unwrap()),
                IntType::U32 => Value::U32(int_val.try_into().unwrap()),
                IntType::U64 => Value::U64(int_val.try_into().unwrap()),
                IntType::U128 => Value::U128(int_val.try_into().unwrap()),

                IntType::I8 => Value::I8(int_val.try_into().unwrap()),
                IntType::I16 => Value::I16(int_val.try_into().unwrap()),
                IntType::I32 => Value::I32(int_val.try_into().unwrap()),
                IntType::I64 => Value::I64(int_val.try_into().unwrap()),
                IntType::I128 => Value::I128(int_val),
            }
            None => Value::I128(int_val),
            x => panic!("Invalid assignment, expected: {:?}, found: {:?}", x, val),
        }
        Value::UnsizedFloat(float_val) => match expected {
            Some(UnresolvedType::Primitive(Primitive::Float(FloatType::F32))) => Value::F32(float_val as f32),
            Some(UnresolvedType::Primitive(Primitive::Float(FloatType::F64))) => Value::F64(float_val),
            None => Value::F64(float_val),
            _ => panic!("Invalid assignment")
        },
        other => other
    };
    //println!("\t adjusted: {:?}", val);
    ValueOrReturn::Value(val)
}

fn as_unresolved(ty: &TypeRef) -> UnresolvedType {
    match ty {
        TypeRef::Primitive(prim) => UnresolvedType::Primitive(*prim),
        TypeRef::Resolved(res) => UnresolvedType::Unresolved(res.clone().into_inner())
    }
}