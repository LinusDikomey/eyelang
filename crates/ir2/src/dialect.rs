use crate::{instructions, primitives};

primitives! {
    Unit = 0
    I1 = 1
    I8 = 1
    I16 = 2
    I32 = 4
    I64 = 8
    U8 = 1
    U16 = 2
    U32 = 4
    U64 = 8
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

instructions! {
    Arith "arith" ArithInsts

    Int value: Int;

    Neg value: Ref;

    Add l: Ref r: Ref;
    Sub l: Ref r: Ref;
    Mul l: Ref r: Ref;
    Div l: Ref r: Ref;
    Rem l: Ref r: Ref;

    Or  l: Ref r: Ref;
    And l: Ref r: Ref;
    Eq  l: Ref r: Ref;
    NE  l: Ref r: Ref;
    LT  l: Ref r: Ref;
    GT  l: Ref r: Ref;
    LE  l: Ref r: Ref;
    GE  l: Ref r: Ref;

    Xor l: Ref r: Ref;
    Rol l: Ref r: Ref;
    Ror l: Ref r: Ref;

    CastInt value: Ref;
    CastFloat value: Ref;
    CastIntToFloat value: Ref;
    CastFloatToInt value: Ref;
}

instructions! {
    Tuple "tuple" TupleInsts

    MemberValue tuple: Ref element: Int;
    InsertMember tuple: Ref element: Int value: Ref;
}

instructions! {
    Mem "mem" MemInsts

    Decl ty: TypeId;
    Load ptr: Ref;
    Store ptr: Ref value: Ref;
    MemberPtr ptr: Ref ty: TypeId idx: Int32;
    IntToPtr value: Ref;
    PtrToInt value: Ref;
    FunctionPtr function: FunctionId;
    Global global: GlobalId;
    // CallPtr  (TODO: dynamic argument list)
    ArrayIndex array_ptr: Ref a: Ref;
}

instructions! {
    Cf "cf" CfInsts

    Goto target: BlockTarget<'static> !terminator true;
    Branch cond: Ref on_true: BlockTarget<'static> on_false: BlockTarget<'static> !terminator true;
    Ret value: Ref !terminator true;
}
