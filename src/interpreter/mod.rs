use core::panic;
use std::{fmt, collections::HashMap, io::{stdin, BufRead, Write}};

use crate::{typing::tir::{self, Module, TypeRef}, ast::{self, BlockItem, UnresolvedType, LValue, Definition, BlockOrExpr}, types::{IntType, FloatType, Primitive}, lexer::tokens::Operator};

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
                write!(f, "{{")?;
                for (i, (name, val)) in fields.iter().enumerate() {
                    write!(f, "{}{}: {}", if i == 0 {""} else {", "}, name, val)?;
                }
                write!(f, "}}")
            }
        }
    }
}
impl Value {
    pub fn get_type(&self) -> Option<UnresolvedType> {
        use Primitive::*;
        Some(UnresolvedType::Primitive(match self {
            Value::Bool(_) => Bool,
            Value::String(_) => String,

            Value::U8(_) => Integer(IntType::U8),
            Value::U16(_) => Integer(IntType::U16),
            Value::U32(_) => Integer(IntType::U32),
            Value::U64(_) => Integer(IntType::U64),
            Value::U128(_) => Integer(IntType::U128),

            Value::I8(_) => Integer(IntType::I8),
            Value::I16(_) => Integer(IntType::I16),
            Value::I32(_) => Integer(IntType::I32),
            Value::I64(_) => Integer(IntType::I64),
            Value::I128(_) => Integer(IntType::I128),

            Value::F32(_) => Float(FloatType::F32),
            Value::F64(_) => Float(FloatType::F64),

            Value::Unit => Unit,

            Value::UnsizedInt(_) | Value::UnsizedFloat(_) 
                => panic!("Unassigned/unsized values shouldn't be typechecked"),
            Value::Unassigned | Value::Struct(_) | Value::Function(_) | Value::Type(_) => return None
        }))
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
                    if args.len() == 0 {
                        panic!("print() with zero args doesn't make sense");
                    }
                    for arg in args {
                        print!("{}", arg);
                    }
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

    let v = eval_block_or_expr(&mut scope, &f.ast.body, Some(&as_unresolved(&f.header().return_type))).value();
    if let Some(ty) = v.get_type() {
        let expected = as_unresolved(&f.header().return_type);
        if ty != expected {
            panic!("Mismatched return type, expected: {:?}, found: {:?}",
                expected,
                ty
            )
        }
    }
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

fn eval_block_or_expr(scope: &mut Scope, b: &ast::BlockOrExpr, expected: Option<&UnresolvedType>) -> ValueOrReturn {
    match b {
        ast::BlockOrExpr::Block(block) => eval_block(scope, block),
        ast::BlockOrExpr::Expr(expr) => {
            eval_expr(scope, expr, expected)
        }
    }
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
            BlockItem::Assign(l_val, expr) => {
                let val = eval_lvalue(&mut scope, l_val);
                let ty = val.get_type();
                // the lvalue has to be evaluated again so scope isn't borrowed when evaluating the expression
                *eval_lvalue(&mut scope, l_val) = get_or_ret!(eval_expr(&mut scope, expr, ty.as_ref()));
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
        Return(ret) => return ValueOrReturn::Return(
            eval_expr(scope, ret, Some(&scope.expected_return_type().clone())).value(),
        ),
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
        If(box ast::If { cond, then, else_ }) => {
            let Value::Bool(cond_true) = get_or_ret!(
                eval_expr(scope, cond, Some(&UnresolvedType::Primitive(Primitive::Bool)))
            ) else { panic!("bool expected in if condition!") };
            if cond_true {
                get_or_ret!(eval_block_or_expr(scope, then, expected))
            } else {
                if let Some(else_block) = else_ {
                    get_or_ret!(eval_block_or_expr(scope, else_block, expected))
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
                    if func.intrinsic.is_none() && args.len() != func.header().params.len() {
                        panic!("Invalid arg count, expected: {}, found: {}", 
                            func.header().params.len(),
                            args.len(), 
                        );
                    }
                    let mut args = args.iter();
                    for (_, ty) in &func.header().params {
                        let arg  = args.next().expect("Not enough arguments to function");
                        arg_vals.push(get_or_ret!(eval_expr(scope, arg, Some(&as_unresolved(ty)))));
                    }

                    if let Some((_, ty)) = &func.header().vararg {
                        for arg in args {
                            arg_vals.push(get_or_ret!(eval_expr(scope, arg, Some(&as_unresolved(ty)))));
                        }
                    }
                    
                    eval_function(scope.outer(), &func, arg_vals) //TODO: proper scope
                }
                Value::Type(tir::Type::Struct(struc)) => {
                    if args.len() != struc.members.len() {
                        panic!("Invalid constructor argument count, expected: {}, found: {}",
                            struc.members.len(),
                            args.len(),
                        );
                    }
                    let mut values = HashMap::new();
                    for (arg, (name, ty)) in args.iter().zip(&struc.members) {
                        values.insert(name.clone(), get_or_ret!(eval_expr(scope, arg, Some(&as_unresolved(ty)))));
                    }
                    Value::Struct(values)
                }
                _ => panic!("Tried to call non-function value as function")
            }
        }
        Negate(inner) => {
            macro_rules! un_op {
                ($val: expr, $($p: tt)*) => {
                    match $val {
                        $(
                            Value::$p(x) => Value::$p(-x),
                        )*
                        _ => panic!("Invalid operation '-' for value: {:?}", $val)
                    }
                }
            }
            un_op!{get_or_ret!(eval_expr(scope, inner, expected)),
                I8 I16 I32 I64 I128 F32 F64
            }
        }
        BinOp(op, sides) => {
            let (lhs, rhs) = &**sides;
            if let Operator::LT | Operator::LE | Operator::GT | Operator::GE | Operator::Equals = op {
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
                (num: $($p: tt),*; eq: $($eq_only: tt),*) => {
                    match (op, lhs, rhs) {
                        $((Operator::Add, Value::$p(l), Value::$p(r)) => Value::$p(l + r),)*
                        $((Operator::Sub, Value::$p(l), Value::$p(r)) => Value::$p(l - r),)*
                        $((Operator::Mul, Value::$p(l), Value::$p(r)) => Value::$p(l * r),)*
                        $((Operator::Div, Value::$p(l), Value::$p(r)) => Value::$p(l / r),)*
                        
                        $((Operator::Equals, Value::$p(l), Value::$p(r)) => Value::Bool(l == r),)*
                        $((Operator::Equals, Value::$eq_only(l), Value::$eq_only(r)) => Value::Bool(l == r),)*

                        $((Operator::LT, Value::$p(l), Value::$p(r)) => Value::Bool(l <  r),)*
                        $((Operator::LE, Value::$p(l), Value::$p(r)) => Value::Bool(l <= r),)*
                        $((Operator::GT, Value::$p(l), Value::$p(r)) => Value::Bool(l >  r),)*
                        $((Operator::GE, Value::$p(l), Value::$p(r)) => Value::Bool(l >= r),)*

                        
                        (op, l, r) => panic!("Invalid operation: {:?} for values: {:?} and {:?}", op, l, r)
                    }
                }
            }
            op_match!(
                num: U8, U16, U32, U64, U128, I8, I16, I32, I64, I128, F32, F64;
                eq: String, Bool 
            )
        }
        MemberAccess(expr, member_name) => {
            match get_or_ret!(eval_expr(scope, expr, None)) {
                Value::Struct(members) => {
                    members[member_name].clone()
                }
                val => panic!("Can't access non-struct member {} of {:?}", member_name, val)
            }
        }
        Cast(target_ty, expr) => {
            macro_rules! cast {
                ($v: expr, $target: expr, $($from: tt => $to: tt : $to_t: pat,)*) => {
                    let v = $v;
                    let t = $target;
                    match (&v, &t) {
                        $(
                            (Value::$from(x), $to_t) => Value::$to(*x as _),
                        )*
                        _ => panic!("Invalid cast from {:?} to {}", v, t)
                    }
                }
            }

            cast!{get_or_ret!(eval_expr(scope, expr, None)), target_ty,
                U8 => U8: Primitive::Integer(IntType::U8),
                U8 => U16: Primitive::Integer(IntType::U16),
                U8 => U32: Primitive::Integer(IntType::U32),
                U8 => U64: Primitive::Integer(IntType::U64),
                U8 => U128: Primitive::Integer(IntType::U128),
                U8 => I8: Primitive::Integer(IntType::I8),
                U8 => I16: Primitive::Integer(IntType::I16),
                U8 => I32: Primitive::Integer(IntType::I32),
                U8 => I64: Primitive::Integer(IntType::I64),
                U8 => I128: Primitive::Integer(IntType::I128),
                U8 => F32: Primitive::Float(FloatType::F32),
                U8 => F64: Primitive::Float(FloatType::F64),
                U16 => U8: Primitive::Integer(IntType::U8),
                U16 => U16: Primitive::Integer(IntType::U16),
                U16 => U32: Primitive::Integer(IntType::U32),
                U16 => U64: Primitive::Integer(IntType::U64),
                U16 => U128: Primitive::Integer(IntType::U128),
                U16 => I8: Primitive::Integer(IntType::I8),
                U16 => I16: Primitive::Integer(IntType::I16),
                U16 => I32: Primitive::Integer(IntType::I32),
                U16 => I64: Primitive::Integer(IntType::I64),
                U16 => I128: Primitive::Integer(IntType::I128),
                U16 => F32: Primitive::Float(FloatType::F32),
                U16 => F64: Primitive::Float(FloatType::F64),
                U32 => U8: Primitive::Integer(IntType::U8),
                U32 => U16: Primitive::Integer(IntType::U16),
                U32 => U32: Primitive::Integer(IntType::U32),
                U32 => U64: Primitive::Integer(IntType::U64),
                U32 => U128: Primitive::Integer(IntType::U128),
                U32 => I8: Primitive::Integer(IntType::I8),
                U32 => I16: Primitive::Integer(IntType::I16),
                U32 => I32: Primitive::Integer(IntType::I32),
                U32 => I64: Primitive::Integer(IntType::I64),
                U32 => I128: Primitive::Integer(IntType::I128),
                U32 => F32: Primitive::Float(FloatType::F32),
                U32 => F64: Primitive::Float(FloatType::F64),
                U64 => U8: Primitive::Integer(IntType::U8),
                U64 => U16: Primitive::Integer(IntType::U16),
                U64 => U32: Primitive::Integer(IntType::U32),
                U64 => U64: Primitive::Integer(IntType::U64),
                U64 => U128: Primitive::Integer(IntType::U128),
                U64 => I8: Primitive::Integer(IntType::I8),
                U64 => I16: Primitive::Integer(IntType::I16),
                U64 => I32: Primitive::Integer(IntType::I32),
                U64 => I64: Primitive::Integer(IntType::I64),
                U64 => I128: Primitive::Integer(IntType::I128),
                U64 => F32: Primitive::Float(FloatType::F32),
                U64 => F64: Primitive::Float(FloatType::F64),
                U128 => U8: Primitive::Integer(IntType::U8),
                U128 => U16: Primitive::Integer(IntType::U16),
                U128 => U32: Primitive::Integer(IntType::U32),
                U128 => U64: Primitive::Integer(IntType::U64),
                U128 => U128: Primitive::Integer(IntType::U128),
                U128 => I8: Primitive::Integer(IntType::I8),
                U128 => I16: Primitive::Integer(IntType::I16),
                U128 => I32: Primitive::Integer(IntType::I32),
                U128 => I64: Primitive::Integer(IntType::I64),
                U128 => I128: Primitive::Integer(IntType::I128),
                U128 => F32: Primitive::Float(FloatType::F32),
                U128 => F64: Primitive::Float(FloatType::F64),

                I8 => U8: Primitive::Integer(IntType::U8),
                I8 => U16: Primitive::Integer(IntType::U16),
                I8 => U32: Primitive::Integer(IntType::U32),
                I8 => U64: Primitive::Integer(IntType::U64),
                I8 => U128: Primitive::Integer(IntType::U128),
                I8 => I8: Primitive::Integer(IntType::I8),
                I8 => I16: Primitive::Integer(IntType::I16),
                I8 => I32: Primitive::Integer(IntType::I32),
                I8 => I64: Primitive::Integer(IntType::I64),
                I8 => I128: Primitive::Integer(IntType::I128),
                I8 => F32: Primitive::Float(FloatType::F32),
                I8 => F64: Primitive::Float(FloatType::F64),
                I16 => U8: Primitive::Integer(IntType::U8),
                I16 => U16: Primitive::Integer(IntType::U16),
                I16 => U32: Primitive::Integer(IntType::U32),
                I16 => U64: Primitive::Integer(IntType::U64),
                I16 => U128: Primitive::Integer(IntType::U128),
                I16 => I8: Primitive::Integer(IntType::I8),
                I16 => I16: Primitive::Integer(IntType::I16),
                I16 => I32: Primitive::Integer(IntType::I32),
                I16 => I64: Primitive::Integer(IntType::I64),
                I16 => I128: Primitive::Integer(IntType::I128),
                I16 => F32: Primitive::Float(FloatType::F32),
                I16 => F64: Primitive::Float(FloatType::F64),
                I32 => U8: Primitive::Integer(IntType::U8),
                I32 => U16: Primitive::Integer(IntType::U16),
                I32 => U32: Primitive::Integer(IntType::U32),
                I32 => U64: Primitive::Integer(IntType::U64),
                I32 => U128: Primitive::Integer(IntType::U128),
                I32 => I8: Primitive::Integer(IntType::I8),
                I32 => I16: Primitive::Integer(IntType::I16),
                I32 => I32: Primitive::Integer(IntType::I32),
                I32 => I64: Primitive::Integer(IntType::I64),
                I32 => I128: Primitive::Integer(IntType::I128),
                I32 => F32: Primitive::Float(FloatType::F32),
                I32 => F64: Primitive::Float(FloatType::F64),
                I64 => U8: Primitive::Integer(IntType::U8),
                I64 => U16: Primitive::Integer(IntType::U16),
                I64 => U32: Primitive::Integer(IntType::U32),
                I64 => U64: Primitive::Integer(IntType::U64),
                I64 => U128: Primitive::Integer(IntType::U128),
                I64 => I8: Primitive::Integer(IntType::I8),
                I64 => I16: Primitive::Integer(IntType::I16),
                I64 => I32: Primitive::Integer(IntType::I32),
                I64 => I64: Primitive::Integer(IntType::I64),
                I64 => I128: Primitive::Integer(IntType::I128),
                I64 => F32: Primitive::Float(FloatType::F32),
                I64 => F64: Primitive::Float(FloatType::F64),
                I128 => U8: Primitive::Integer(IntType::U8),
                I128 => U16: Primitive::Integer(IntType::U16),
                I128 => U32: Primitive::Integer(IntType::U32),
                I128 => U64: Primitive::Integer(IntType::U64),
                I128 => U128: Primitive::Integer(IntType::U128),
                I128 => I8: Primitive::Integer(IntType::I8),
                I128 => I16: Primitive::Integer(IntType::I16),
                I128 => I32: Primitive::Integer(IntType::I32),
                I128 => I64: Primitive::Integer(IntType::I64),
                I128 => I128: Primitive::Integer(IntType::I128),
                I128 => F32: Primitive::Float(FloatType::F32),
                I128 => F64: Primitive::Float(FloatType::F64),

            }
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
    ValueOrReturn::Value(val)
}

fn eval_lvalue<'a>(scope: &'a mut Scope, l_val: &LValue) -> &'a mut Value {
    match l_val {
        LValue::Variable(var) => scope.resolve_mut(var),
        LValue::Member(inner, member) => {
            match eval_lvalue(scope, inner) {
                Value::Struct(members) => members.get_mut(member).expect("Member not found"),
                val => panic!("Can't access non-struct type member '{}' of value: {:?}", member, val)
            }
        }
    }
}

fn as_unresolved(ty: &TypeRef) -> UnresolvedType {
    match ty {
        TypeRef::Primitive(prim) => UnresolvedType::Primitive(*prim),
        TypeRef::Resolved(res) => UnresolvedType::Unresolved(res.clone().into_inner())
    }
}


pub fn insert_intrinsics(module: &mut ast::Module) {
    module.definitions.insert("print".to_owned(), Definition::Function(ast::Function {
        body: BlockOrExpr::Block(ast::Block { items: Vec::new(), defs: HashMap::new() }),
        params: Vec::new(),
        vararg: Some(("args".to_owned(), ast::UnresolvedType::Primitive(Primitive::String))),
        return_type: ast::UnresolvedType::Primitive(Primitive::Unit)
    }));
    module.definitions.insert("read".to_owned(), Definition::Function(ast::Function {
        body: BlockOrExpr::Block(ast::Block { items: Vec::new(), defs: HashMap::new() }),
        params: vec![("s".to_owned(), ast::UnresolvedType::Primitive(Primitive::String))],
        vararg: None,
        return_type: ast::UnresolvedType::Primitive(Primitive::String)
    }));
    module.definitions.insert("parse".to_owned(), Definition::Function(ast::Function {
        body: BlockOrExpr::Block(ast::Block { items: Vec::new(), defs: HashMap::new() }),
        params: vec![("s".to_owned(), ast::UnresolvedType::Primitive(Primitive::String))],
        vararg: None,
        return_type: ast::UnresolvedType::Primitive(Primitive::Integer(IntType::I32))
    }));
}