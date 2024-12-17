use crate::{instructions, primitives};

primitives! {
    Unit = 0
    I1 = 1
    I8 = 1
    I16 = 2
    I32 = 4
    I64 = 8
    F32 = 4
    Ptr = 8
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
    IntToPtr value: Ref;
    PtrToInt value: Ref;
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
    MemberPtr;
    FunctionPtr function: FunctionId;
    Global global: GlobalId;
    // CallPtr  (TODO: dynamic argument list)
    ArrayIndex array_ptr: Ref a: Ref;
}

instructions! {
    Cf "cf" CfInsts

    Goto target: BlockId !terminator true;
    Branch cond: Ref on_true: BlockId on_false: BlockId !terminator true;
    Ret value: Ref !terminator true;
}
