use core::panic;
use std::{fmt, collections::HashMap, io::{stdin, BufRead, Write}, mem::ManuallyDrop};

use crate::{ast::{self, BlockItem, UnresolvedType, LValue, Definition, BlockOrExpr}, types::{IntType, FloatType, Primitive}, lexer::tokens::Operator, ir::{self, TypeRef}};

#[derive(Clone, Debug)]
pub enum Value {
    Unit,
    Unassigned,

    Function(ir::Function),
    Type(ir::Type),

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
            Type(ir::Type::Struct(_, struc)) => write!(f, "{}", struc),
        
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
    pub fn get_type(&self) -> Option<TypeRef> {
        use Primitive::*;
        Some(TypeRef::Primitive(match self {
            Value::Bool(_) => Bool,
            Value::String(_) => String,

            Value::U8(_) => U8,
            Value::U16(_) => U16,
            Value::U32(_) => U32,
            Value::U64(_) => U64,
            Value::U128(_) => U128,

            Value::I8(_) => I8,
            Value::I16(_) => I16,
            Value::I32(_) => I32,
            Value::I64(_) => I64,
            Value::I128(_) => I128,

            Value::F32(_) => F32,
            Value::F64(_) => F64,

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
    expected_return_type: Option<TypeRef>
}
impl Scope {
    pub fn new() -> Self {
        Self { parent: None, values: HashMap::new(), expected_return_type: None }
    }
    pub fn with_parent(parent: &mut Scope) -> Self {
        Self { parent: Some(parent as _), values: HashMap::new(), expected_return_type: None }
    }
    pub fn from_module(module: ir::IrModule) -> Self {
        let mut s = Scope::new();

        let mut funcs = ManuallyDrop::new(module.funcs);
        let mut types = ManuallyDrop::new(module.types);

        // SAFETY: funcs and types are taken out and left uninitialized. They are all taken exactly once because
        // they are all defined in the symbols map.
        #[allow(invalid_value)]
        for (name, (symbol_ty, key)) in module.symbols {
            s.values.insert(name, match symbol_ty {
                ir::SymbolType::Func => Value::Function(std::mem::replace(
                    &mut funcs[key.idx()],
                    unsafe { std::mem::MaybeUninit::uninit().assume_init() }
                )),
                ir::SymbolType::Type => Value::Type(std::mem::replace(
                    &mut types[key.idx()],
                    unsafe { std::mem::MaybeUninit::uninit().assume_init() }
                )),
            });
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

    pub fn expected_return_type(&self) -> TypeRef {
        match self.expected_return_type {
            Some(ty) => ty,
            None => if let Some(parent) = self.parent {
                unsafe { &*parent }.expected_return_type()
            } else {
                panic!("Missing expected return type")
            }
        }
    }

    /// temporary function for resolving ast types
    fn resolve_type(&self, name: &str) -> TypeRef {
        if let Some(Value::Type(ir::Type::Struct(key, _))) = self.values.get(name) {
            return TypeRef::Resolved(*key);
        } else {
            if let Some(parent) = self.parent {
                return unsafe { &*parent }.resolve_type(name);
            }
        }
        panic!("Missing type {name:?}")
    }
}

pub fn eval_function<'a>(scope: &mut Scope, f: &ir::Function, args: Vec<Value>) -> Value {
    match &f.intrinsic {
        Some(intrinsic) => {
            let val = match intrinsic {
                ir::Intrinsic::Print => {
                    if args.len() == 0 {
                        panic!("print() with zero args doesn't make sense");
                    }
                    for arg in args {
                        print!("{}", arg);
                    }
                    Value::Unit
                },
                ir::Intrinsic::Read => {
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
                ir::Intrinsic::Parse => {
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
    scope.expected_return_type = Some(f.header().return_type);
    for ((arg_name, _), arg_val) in f.header.params.iter().zip(args) {
        scope.values.insert(arg_name.clone(), arg_val);
    }

    let v = eval_block_or_expr(&mut scope, &f.ast.body, Some(f.header().return_type)).value();
    if let Some(ty) = v.get_type() {
        let expected = f.header().return_type;
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

fn to_type_ref(unresolved: &UnresolvedType, scope: &Scope) -> TypeRef {
    match unresolved {
        UnresolvedType::Primitive(p) => TypeRef::Primitive(*p),
        UnresolvedType::Unresolved(name) => scope.resolve_type(name)
    }
}

fn eval_block_or_expr(scope: &mut Scope, b: &ast::BlockOrExpr, expected: Option<TypeRef>) -> ValueOrReturn {
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
                    let expected = ty.as_ref().map(|ty| to_type_ref(ty, &scope));
                    get_or_ret!(eval_expr(&mut scope, e, expected))
                } else {
                    Value::Unassigned 
                };
                scope.values.insert(name.clone(), val);
            },
            BlockItem::Assign(l_val, expr) => {
                let val = eval_lvalue(&mut scope, l_val);
                let ty = val.get_type();
                // the lvalue has to be evaluated again so scope isn't borrowed when evaluating the expression
                *eval_lvalue(&mut scope, l_val) = get_or_ret!(eval_expr(&mut scope, expr, ty));
            },
            BlockItem::Expression(expr) => {
                get_or_ret!(eval_expr(&mut scope, expr, None));
            }
        }
    }
    ValueOrReturn::Value(Value::Unit)
}

fn eval_expr(scope: &mut Scope, expr: &ast::Expression, mut expected: Option<TypeRef>) -> ValueOrReturn {
    use ast::Expression::*;
    let val = match expr {
        Return(ret) => return ValueOrReturn::Return(
            eval_expr(scope, ret, Some(scope.expected_return_type())).value(),
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
                eval_expr(scope, cond, Some(TypeRef::Primitive(Primitive::Bool)))
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
                        arg_vals.push(get_or_ret!(eval_expr(scope, arg, Some(*ty))));
                    }

                    if let Some((_, ty)) = &func.header().vararg {
                        for arg in args {
                            arg_vals.push(get_or_ret!(eval_expr(scope, arg, Some(*ty))));
                        }
                    }
                    
                    eval_function(scope.outer(), &func, arg_vals) //TODO: proper scope
                }
                Value::Type(ir::Type::Struct(_, struc)) => {
                    if args.len() != struc.members.len() {
                        panic!("Invalid constructor argument count, expected: {}, found: {}",
                            struc.members.len(),
                            args.len(),
                        );
                    }
                    let mut values = HashMap::new();
                    for (arg, (name, ty)) in args.iter().zip(&struc.members) {
                        values.insert(name.clone(), get_or_ret!(eval_expr(scope, arg, Some(*ty))));
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
                    U8(_) => Some(Primitive::U8),
                    U16(_) => Some(Primitive::U16),
                    U32(_) => Some(Primitive::U32),
                    U64(_) => Some(Primitive::U64),
                    U128(_) => Some(Primitive::U128),
                    
                    I8(_) => Some(Primitive::I8),
                    I16(_) => Some(Primitive::I16),
                    I32(_) => Some(Primitive::I32),
                    I64(_) => Some(Primitive::I64),
                    I128(_) => Some(Primitive::I128),

                    F32(_) => Some(Primitive::F32),
                    F64(_) => Some(Primitive::F64),

                    _ => None
                }.map(TypeRef::Primitive)
            } else { expected.map(|t| t.clone()) };
            let rhs = get_or_ret!(eval_expr(scope, rhs, rhs_expected));
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
                U8 => U8: Primitive::U8,
                U8 => U16: Primitive::U16,
                U8 => U32: Primitive::U32,
                U8 => U64: Primitive::U64,
                U8 => U128: Primitive::U128,
                U8 => I8: Primitive::I8,
                U8 => I16: Primitive::I16,
                U8 => I32: Primitive::I32,
                U8 => I64: Primitive::I64,
                U8 => I128: Primitive::I128,
                U8 => F32: Primitive::F32,
                U8 => F64: Primitive::F64,
                U16 => U8: Primitive::U8,
                U16 => U16: Primitive::U16,
                U16 => U32: Primitive::U32,
                U16 => U64: Primitive::U64,
                U16 => U128: Primitive::U128,
                U16 => I8: Primitive::I8,
                U16 => I16: Primitive::I16,
                U16 => I32: Primitive::I32,
                U16 => I64: Primitive::I64,
                U16 => I128: Primitive::I128,
                U16 => F32: Primitive::F32,
                U16 => F64: Primitive::F64,
                U32 => U8: Primitive::U8,
                U32 => U16: Primitive::U16,
                U32 => U32: Primitive::U32,
                U32 => U64: Primitive::U64,
                U32 => U128: Primitive::U128,
                U32 => I8: Primitive::I8,
                U32 => I16: Primitive::I16,
                U32 => I32: Primitive::I32,
                U32 => I64: Primitive::I64,
                U32 => I128: Primitive::I128,
                U32 => F32: Primitive::F32,
                U32 => F64: Primitive::F64,
                U64 => U8: Primitive::U8,
                U64 => U16: Primitive::U16,
                U64 => U32: Primitive::U32,
                U64 => U64: Primitive::U64,
                U64 => U128: Primitive::U128,
                U64 => I8: Primitive::I8,
                U64 => I16: Primitive::I16,
                U64 => I32: Primitive::I32,
                U64 => I64: Primitive::I64,
                U64 => I128: Primitive::I128,
                U64 => F32: Primitive::F32,
                U64 => F64: Primitive::F64,
                U128 => U8: Primitive::U8,
                U128 => U16: Primitive::U16,
                U128 => U32: Primitive::U32,
                U128 => U64: Primitive::U64,
                U128 => U128: Primitive::U128,
                U128 => I8: Primitive::I8,
                U128 => I16: Primitive::I16,
                U128 => I32: Primitive::I32,
                U128 => I64: Primitive::I64,
                U128 => I128: Primitive::I128,
                U128 => F32: Primitive::F32,
                U128 => F64: Primitive::F64,

                I8 => U8: Primitive::U8,
                I8 => U16: Primitive::U16,
                I8 => U32: Primitive::U32,
                I8 => U64: Primitive::U64,
                I8 => U128: Primitive::U128,
                I8 => I8: Primitive::I8,
                I8 => I16: Primitive::I16,
                I8 => I32: Primitive::I32,
                I8 => I64: Primitive::I64,
                I8 => I128: Primitive::I128,
                I8 => F32: Primitive::F32,
                I8 => F64: Primitive::F64,
                I16 => U8: Primitive::U8,
                I16 => U16: Primitive::U16,
                I16 => U32: Primitive::U32,
                I16 => U64: Primitive::U64,
                I16 => U128: Primitive::U128,
                I16 => I8: Primitive::I8,
                I16 => I16: Primitive::I16,
                I16 => I32: Primitive::I32,
                I16 => I64: Primitive::I64,
                I16 => I128: Primitive::I128,
                I16 => F32: Primitive::F32,
                I16 => F64: Primitive::F64,
                I32 => U8: Primitive::U8,
                I32 => U16: Primitive::U16,
                I32 => U32: Primitive::U32,
                I32 => U64: Primitive::U64,
                I32 => U128: Primitive::U128,
                I32 => I8: Primitive::I8,
                I32 => I16: Primitive::I16,
                I32 => I32: Primitive::I32,
                I32 => I64: Primitive::I64,
                I32 => I128: Primitive::I128,
                I32 => F32: Primitive::F32,
                I32 => F64: Primitive::F64,
                I64 => U8: Primitive::U8,
                I64 => U16: Primitive::U16,
                I64 => U32: Primitive::U32,
                I64 => U64: Primitive::U64,
                I64 => U128: Primitive::U128,
                I64 => I8: Primitive::I8,
                I64 => I16: Primitive::I16,
                I64 => I32: Primitive::I32,
                I64 => I64: Primitive::I64,
                I64 => I128: Primitive::I128,
                I64 => F32: Primitive::F32,
                I64 => F64: Primitive::F64,
                I128 => U8: Primitive::U8,
                I128 => U16: Primitive::U16,
                I128 => U32: Primitive::U32,
                I128 => U64: Primitive::U64,
                I128 => U128: Primitive::U128,
                I128 => I8: Primitive::I8,
                I128 => I16: Primitive::I16,
                I128 => I32: Primitive::I32,
                I128 => I64: Primitive::I64,
                I128 => I128: Primitive::I128,
                I128 => F32: Primitive::F32,
                I128 => F64: Primitive::F64,

            }
        }
    };

    //println!("Adjusting expr val: {:?}, expected: {:?}", val, expected);
    let val = match val {
        Value::UnsizedInt(int_val) => {
            expected
            .map_or(Some(Value::I128(int_val)), |expected| {
                let TypeRef::Primitive(p) = expected else { return None };
                let Some(int_ty) = p.as_int() else { return None };
                Some(match int_ty {
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
                })
            })
            .unwrap_or_else(|| panic!("Invalid assignment, expected: {:?}, found: {:?}", expected, val))
        }
        Value::UnsizedFloat(float_val) => {
            expected.map_or(Some(Value::F64(float_val)), |expected| {
                let TypeRef::Primitive(p) = expected else { return None };
                let Some(float_ty) = p.as_float() else { return None };
                Some(match float_ty {
                    FloatType::F32 => Value::F32(float_val as f32),
                    FloatType::F64 => Value::F64(float_val)
                })
            })
            .unwrap_or_else(|| panic!("Invalid assignment, expected: {:?}, found: {:?}", expected, val))

        }
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

/*fn as_unresolved(ty: &ir::TypeRef) -> UnresolvedType {
    match ty {
        ir::TypeRef::Primitive(prim) => UnresolvedType::Primitive(*prim),
        ir::TypeRef::Resolved(res) => UnresolvedType::Unresolved(res)
    }
}*/


pub fn insert_intrinsics(module: &mut ast::Module) {
    module.definitions.insert("print".to_owned(), Definition::Function(ast::Function {
        body: BlockOrExpr::Block(ast::Block { items: Vec::new(), defs: HashMap::new() }),
        params: Vec::new(),
        vararg: Some(("args".to_owned(), ast::UnresolvedType::Primitive(Primitive::String), 0, 0)),
        return_type: (ast::UnresolvedType::Primitive(Primitive::Unit), 0, 0)
    }));
    module.definitions.insert("read".to_owned(), Definition::Function(ast::Function {
        body: BlockOrExpr::Block(ast::Block { items: Vec::new(), defs: HashMap::new() }),
        params: vec![("s".to_owned(), ast::UnresolvedType::Primitive(Primitive::String), 0, 0)],
        vararg: None,
        return_type: (ast::UnresolvedType::Primitive(Primitive::String), 0, 0)
    }));
    module.definitions.insert("parse".to_owned(), Definition::Function(ast::Function {
        body: BlockOrExpr::Block(ast::Block { items: Vec::new(), defs: HashMap::new() }),
        params: vec![("s".to_owned(), ast::UnresolvedType::Primitive(Primitive::String), 0, 0)],
        vararg: None,
        return_type: (ast::UnresolvedType::Primitive(Primitive::I32), 0, 0)
    }));
}