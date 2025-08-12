use crate::{instructions, primitives};

primitives! {
    Unit = 0
    I1 = 1
    I8 = 1
    I16 = 2
    I32 = 4
    I64 = 8
    I128 = 16
    U8 = 1
    U16 = 2
    U32 = 4
    U64 = 8
    U128 = 16
    F32 = 4
    F64 = 8
    Ptr = 8
}
impl Primitive {
    pub fn is_int(self) -> bool {
        self.is_signed_int() || self.is_unsigned_int()
    }

    pub fn is_signed_int(self) -> bool {
        matches!(
            self,
            Self::I1 | Self::I8 | Self::I16 | Self::I32 | Self::I64
        )
    }

    pub fn is_unsigned_int(self) -> bool {
        matches!(self, Self::U8 | Self::U16 | Self::U32 | Self::U64)
    }

    pub fn is_float(self) -> bool {
        matches!(self, Self::F32 | Self::F64)
    }
}

pub fn register_all(env: &mut crate::Environment) {
    env.get_dialect_module::<Arith>();
    env.get_dialect_module::<Tuple>();
    env.get_dialect_module::<Mem>();
    env.get_dialect_module::<Cf>();
}

instructions! {
    Arith "arith" ArithInsts

    Int value: Int !pure;
    Float value: Float !pure;

    Neg value: Ref !pure;
    Not value: Ref !pure;

    Add l: Ref r: Ref !pure;
    Sub l: Ref r: Ref !pure;
    Mul l: Ref r: Ref !pure;
    Div l: Ref r: Ref !pure;
    Rem l: Ref r: Ref !pure;

    Or  l: Ref r: Ref !pure;
    And l: Ref r: Ref !pure;
    Eq  l: Ref r: Ref !pure;
    NE  l: Ref r: Ref !pure;
    LT  l: Ref r: Ref !pure;
    GT  l: Ref r: Ref !pure;
    LE  l: Ref r: Ref !pure;
    GE  l: Ref r: Ref !pure;

    Xor l: Ref r: Ref !pure;
    Rol l: Ref r: Ref !pure;
    Ror l: Ref r: Ref !pure;

    CastInt value: Ref !pure;
    CastFloat value: Ref !pure;
    CastIntToFloat value: Ref !pure;
    CastFloatToInt value: Ref !pure;
}

instructions! {
    Tuple "tuple" TupleInsts

    MemberValue tuple: Ref element: Int !pure;
    InsertMember tuple: Ref element: Int value: Ref !pure;
}

instructions! {
    Mem "mem" MemInsts

    Decl ty: TypeId !pure;
    Load ptr: Ref !pure;
    Store ptr: Ref value: Ref;
    MemberPtr ptr: Ref ty: TypeId idx: Int32 !pure;
    IntToPtr value: Ref !pure;
    PtrToInt value: Ref !pure;
    FunctionPtr function: FunctionId !pure;
    Global global: GlobalId !pure;
    // CallPtr  (TODO: dynamic argument list)
    ArrayIndex array_ptr: Ref elem_ty: TypeId a: Ref !pure;
}

instructions! {
    Cf "cf" CfInsts

    Goto<'a> target: BlockTarget<'a> !terminator;
    Branch cond: Ref on_true: BlockTarget<'static> on_false: BlockTarget<'static> !terminator;
    Ret value: Ref !terminator;
}
