use core::panic;
use std::{fmt, collections::HashMap};

use crate::{
    ast::{self, BlockItem, UnresolvedType, LValue},
    types::{IntType, FloatType, Primitive},
    lexer::tokens::Operator,
    ir::{self, TypeRef, SymbolKey}
};

#[derive(Clone, Debug)]
pub enum Value {
    Unit,
    Unassigned,

    Function(SymbolKey),
    Type(SymbolKey),

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

    Struct(Box<(SymbolKey, Vec<Value>)>), // Box<HashMap<String, Value>>
}
pub struct ValueFmtAdaptor<'a> {
    value: &'a Value,
    module: &'a ir::Module
}
impl fmt::Display for ValueFmtAdaptor<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.value.fmt_with_module(f, self.module)
    }
}
impl Value {
    pub fn adapt_fmt<'a>(&'a self, module: &'a ir::Module) -> ValueFmtAdaptor<'a> {
        ValueFmtAdaptor { value: self, module }
    }
    pub fn fmt_with_module(&self, f: &mut fmt::Formatter<'_>, module: &ir::Module) -> fmt::Result {
        use Value::*;
        match self {
            Unit => write!(f, "()"),
            Unassigned => write!(f, "[UNASSIGNED]"),
            Function(key) => {
                let func = &module.funcs[key.idx()];
                write!(f, "({}) -> {}", 
                    func.header().params.iter()
                        .map(|p| format!("{}: {}", p.0, p.1))
                        .intersperse(", ".to_owned()).collect::<std::string::String>(),
                    func.header().return_type
                )
            }
            Type(key) => {
                let ir::TypeDef::Struct(struc) = &module.types[key.idx()];
                write!(f, "{}", struc)
            }
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
        
            Struct(box (symbol, fields)) => {
                let ir::TypeDef::Struct(struc) = &module.types[symbol.idx()];
                write!(f, "{{")?;
                for ((i, val), (name, _)) in fields.iter().enumerate().zip(&struc.members) {
                    if i != 0 {
                        f.write_str(", ")?;
                    }
                    f.write_str(name)?;
                    f.write_str(": ")?;
                    val.fmt_with_module(f, module)?;
                }
                write!(f, "}}")
            }
        }
    }
    
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

pub struct Scope<'m> {
    parent: Option<*mut Scope<'m>>,
    values: HashMap<String, Value>,
    module: &'m ir::Module,
    expected_return_type: Option<TypeRef>
}
impl<'m> Scope<'m> {
    /*pub fn new() -> Self {
        Self { parent: None, values: HashMap::new(), mo, expected_return_type: None }
    }*/
    pub fn with_parent<'p>(parent: &mut Scope<'m>) -> Self {
        Self {
            parent: Some(parent as _),
            values: HashMap::new(),
            module: parent.module,
            expected_return_type: None
        }
    }
    pub fn from_module(module: &'m ir::Module) -> Self {
        let mut values = HashMap::new();

        for (name, (symbol_ty, key)) in &module.symbols {
            values.insert(name.to_owned(), match symbol_ty {
                ir::SymbolType::Func => Value::Function(*key),
                ir::SymbolType::Type => Value::Type(*key),
            });
        }
        Scope {
            parent: None,
            values,
            module,
            expected_return_type: None
        }
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

    /// Resolves a value and returns a mutable reference to it. Also returns
    /// a reference to the module for preventing borrowing problems.
    pub fn resolve_mut<'a>(&'a mut self, name: &str) -> (&'a mut Value, &'m ir::Module) {
        if let Some(v) = self.values.get_mut(name) {
            (v, self.module)
        } else {
            if let Some(parent) = &mut self.parent {
                unsafe { &mut **parent }.resolve_mut(name)
            } else {
                panic!("Invalid reference: {}", name)
            }
        }
    }

    pub fn outer(&mut self) -> &mut Scope<'m> {
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
        if let Some(Value::Type(key)) = self.values.get(name) {
            return TypeRef::Resolved(*key);
        } else {
            if let Some(parent) = self.parent {
                return unsafe { &*parent }.resolve_type(name);
            }
        }
        panic!("Missing type {name:?}")
    }
}

pub fn eval_function<R: std::io::BufRead, W: std::io::Write>
(io: &mut (R, W), scope: &mut Scope, f: &ir::Function, args: &[Value]) -> Value {
    match &f.intrinsic {
        Some(intrinsic) => {
            let val = match intrinsic {
                ir::Intrinsic::Print => {
                    if args.len() == 0 {
                        panic!("print() with zero args doesn't make sense");
                    }
                    for arg in args {
                        write!(io.1, "{}", arg.adapt_fmt(scope.module)).unwrap();
                    }
                    Value::Unit
                },
                ir::Intrinsic::Read => {
                    match args.len() {
                        0 => {}
                        1 => {
                            let Value::String(s) = &args[0] else { panic!("Invalid read() arg") };
                            write!(io.1, "{s}").unwrap();
                            io.1.flush().unwrap();
                        }
                        _ => panic!("Invalid read() arg count")
                    }
                    let mut buf = String::new();
                    io.0.read_line(&mut buf).unwrap();
                    if let Some(b'\n') = buf.bytes().last() {
                        buf.pop().expect("newline byte expected");
                    }
                    Value::String(buf)
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
        scope.values.insert(arg_name.clone(), arg_val.clone());
    }

    let v = eval_block_or_expr(io, &mut scope, f.ast.body.as_ref().expect("Can't interpret extern functions"), Some(f.header().return_type)).value();
    if let Some(ty) = v.get_type() {
        let expected = f.header().return_type;
        if ty != expected {
            panic!("Mismatched return type, expected: {:?}, found: {:?}",
                expected,
                ty
            )
        }
    }

    io.1.flush().unwrap();

    v
}

#[derive(Debug)]
enum ValueOrReturn {
    Value(Value),
    Return(Value)
}
impl ValueOrReturn {
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

fn eval_block_or_expr<'a, R: std::io::BufRead, W: std::io::Write>
(io: &mut (R, W), scope: &'a mut Scope, b: &ast::BlockOrExpr, expected: Option<TypeRef>) -> ValueOrReturn {
    match b {
        ast::BlockOrExpr::Block(block) => eval_block(io, scope, block),
        ast::BlockOrExpr::Expr(expr) => {
            eval_expr(io, scope, expr, expected)
        }
    }
}

fn eval_block<'a, 'm, R: std::io::BufRead, W: std::io::Write>
(io: &mut (R, W), scope: &'a mut Scope<'m>, block: &ast::Block) -> ValueOrReturn {
    let mut scope = Scope::with_parent(scope);
    for item in &block.items {
        match item {
            BlockItem::Block(block) => {
                get_or_ret!(eval_block(io, &mut scope, block));
            },
            BlockItem::Declare(name, _index, ty, expr) => {
                let val = if let Some(e) = expr {
                    let expected = ty.as_ref().map(|ty| to_type_ref(ty, &scope));
                    get_or_ret!(eval_expr(io, &mut scope, e, expected))
                } else {
                    Value::Unassigned 
                };
                scope.values.insert(name.clone(), val);
            },
            BlockItem::Assign(l_val, expr) => {
                let val = eval_lvalue(&mut scope, l_val).0;
                let ty = val.get_type();
                // the lvalue has to be evaluated again so scope isn't borrowed when evaluating the expression
                *eval_lvalue(&mut scope, l_val).0 = get_or_ret!(eval_expr(io, &mut scope, expr, ty));
            },
            BlockItem::Expression(expr) => {
                get_or_ret!(eval_expr(io, &mut scope, expr, None));
            }
        }
    }
    ValueOrReturn::Value(Value::Unit)
}

fn eval_expr<R: std::io::BufRead, W: std::io::Write>
(io: &mut (R, W), scope: &mut Scope, expr: &ast::Expression, mut expected: Option<TypeRef>) -> ValueOrReturn {
    use ast::Expression::*;
    let val = match expr {
        Return(ret) => return ValueOrReturn::Return(
            eval_expr(io, scope, ret, Some(scope.expected_return_type())).value(),
        ),
        IntLiteral(lit) => {
            match lit.ty {
                Some(IntType::I8) => Value::I8(lit.val as i8),
                Some(IntType::I16) => Value::I16(lit.val as i16),
                Some(IntType::I32) => Value::I32(lit.val as i32),
                Some(IntType::I64) => Value::I64(lit.val as i64),
                Some(IntType::I128) => Value::I128(lit.val as i128),

                Some(IntType::U8) => Value::U8(lit.val as u8),
                Some(IntType::U16) => Value::U16(lit.val as u16),
                Some(IntType::U32) => Value::U32(lit.val as u32),
                Some(IntType::U64) => Value::U64(lit.val as u64),
                Some(IntType::U128) => Value::U128(lit.val as u128),

                None => Value::UnsizedInt(lit.val as i128)
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
        Unit => Value::Unit,
        Variable(name) => scope.resolve(name).0.clone(),
        If(box ast::If { cond, then, else_ }) => {
            let Value::Bool(cond_true) = get_or_ret!(
                eval_expr(io, scope, cond, Some(TypeRef::Primitive(Primitive::Bool)))
            ) else { panic!("bool expected in if condition!") };
            if cond_true {
                get_or_ret!(eval_block_or_expr(io, scope, then, expected))
            } else {
                if let Some(else_block) = else_ {
                    get_or_ret!(eval_block_or_expr(io, scope, else_block, expected))
                } else {
                    Value::Unit
                }
            }
        }
        FunctionCall(expr, args) => {
            let func = get_or_ret!(eval_expr(io, scope, expr, None));
            let mut arg_vals = Vec::with_capacity(args.len());
            match func {
                Value::Function(func) => {
                    let func = &scope.module.funcs[func.idx() as usize];
                    if func.intrinsic.is_none() && args.len() != func.header().params.len() {
                        panic!("Invalid arg count, expected: {}, found: {}", 
                            func.header().params.len(),
                            args.len(), 
                        );
                    }
                    let mut args = args.iter();
                    for (_, ty) in &func.header().params {
                        let arg  = args.next().expect("Not enough arguments to function");
                        arg_vals.push(get_or_ret!(eval_expr(io, scope, arg, Some(*ty))));
                    }

                    if func.header().varargs {
                        for arg in args {
                            arg_vals.push(get_or_ret!(eval_expr(io, scope, arg, None)));
                        }
                    }
                    
                    eval_function(io, scope.outer(), &func, &arg_vals) //TODO: proper scope
                }
                Value::Type(key) => {
                    let ir::TypeDef::Struct(struc) = &scope.module.types[key.idx()];
                    if args.len() != struc.members.len() {
                        panic!("Invalid constructor argument count, expected: {}, found: {}",
                            struc.members.len(),
                            args.len(),
                        );
                    }
                    let mut values = Vec::new();
                    for (arg, (_, ty)) in args.iter().zip(&struc.members) {
                        values.push(get_or_ret!(eval_expr(io, scope, arg, Some(*ty))));
                    }
                    Value::Struct(Box::new((key, values)))
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
            un_op!{get_or_ret!(eval_expr(io, scope, inner, expected)),
                I8 I16 I32 I64 I128 F32 F64
            }
        }
        BinOp(op, sides) => {
            let (lhs, rhs) = &**sides;
            if let Operator::LT | Operator::LE | Operator::GT | Operator::GE | Operator::Equals = op {
                expected = None;
            };
            let lhs = get_or_ret!(eval_expr(io, scope, lhs, expected));
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
            let rhs = get_or_ret!(eval_expr(io, scope, rhs, rhs_expected));
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
            match get_or_ret!(eval_expr(io, scope, expr, None)) {
                Value::Struct(box (type_key, members)) => {
                    let ir::TypeDef::Struct(struc) = &scope.module.types[type_key.idx()];
                    debug_assert_eq!(members.len(), struc.members.len());
                    let i = struc.members.iter()
                        .enumerate()
                        .find(|(_, (name, _))| name == member_name)
                        .expect("Unknown member").0;
                    members[i].clone()
                }
                val => panic!("Can't access member {} of non-struct {:?}", member_name, val)
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

            let val = get_or_ret!(eval_expr(io, scope, expr, None));

            if *target_ty == Primitive::String {
                Value::String(format!("{}", val.adapt_fmt(scope.module)))
            } else {
                cast!{val, target_ty,
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
        }
    };

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

fn eval_lvalue<'a, 'm>(scope: &'a mut Scope<'m>, l_val: &LValue) -> (&'a mut Value, &'m ir::Module) {
    match l_val {
        LValue::Variable(_, var) => scope.resolve_mut(var),
        LValue::Member(inner, member) => {
            match eval_lvalue(scope, inner) {
                (Value::Struct(box (type_key, members)), module) => {
                    let ir::TypeDef::Struct(struc) = &module.types[type_key.idx()];
                    (
                        &mut members[struc.member_index(member).unwrap_or_else(|| panic!("Invalid member {member}"))],
                        module
                    )
                }
                val => panic!("Can't access non-struct type member '{}' of value: {:?}", member, val.0)
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