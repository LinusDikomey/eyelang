use crate::{
    Ref,
    BlockIndex,
    Primitive,
    ir_types::{IrType, ConstIrType, IrTypes},
    layout::{Layout, type_layout, primitive_layout}, FunctionIr, Function,
};

#[derive(Clone, Copy, Debug)]
pub enum Val {
    Invalid,
    Unit,
    Int(u64),
    F32(f32),
    F64(f64),
    StackPointer(StackAddr),
}
impl Val {
    fn equals(&self, r: Val) -> bool {
        match (*self, r) {
            (Val::Int(a), Val::Int(b)) => a == b,
            (Val::Unit, Val::Unit) => true,
            (Val::F32(a), Val::F32(b)) => a == b,
            (Val::F64(a), Val::F64(b)) => a == b,
            (Val::StackPointer(a), Val::StackPointer(b)) => a.0 == b.0,
            _ => panic!("invalid types for equality check"),
        }
    }
}

struct StackMem {
    mem: Vec<u8>,
}
impl StackMem {
    pub fn new() -> StackMem {
        Self {
            mem: Vec::new(),
        }
    }

    pub fn alloc(&mut self, layout: Layout) -> StackAddr {
        let addr = self.mem.len();
        self.mem.resize_with(addr + layout.size as usize, || 0);
        StackAddr(addr as _)
    }

    pub fn load(&mut self, addr: StackAddr, size: u64) -> &[u8] {
        &self.mem[addr.0 as usize .. addr.0 as usize + size as usize]
    }

    pub fn store(&mut self, addr: StackAddr, value: &[u8]) {
        self.mem[addr.0 as usize .. addr.0 as usize + value.len()].copy_from_slice(value);
    }

    pub fn load_array<const N: usize>(&mut self, addr: StackAddr) -> [u8; N] {
        let mut arr = [0; N];
        arr.copy_from_slice(&self.mem[addr.0 as usize .. addr.0 as usize + N]);
        arr
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StackAddr(u32);

pub static mut BACKWARDS_JUMP_LIMIT: usize = 1000;

#[derive(Debug)]
pub enum Error {
    InfiniteLoop,
}

pub fn eval(function: &Function, params: &[Val]) -> Result<Val, Error> {
    // TODO: validate params
    let mut stack = StackMem::new();
    let ir = function.ir.as_ref().expect("can't eval extern function");
    let types = &function.types;
    let val = unsafe { eval_internal(ir, types, params, &mut stack) }?;
    assert!(
        !matches!(val, Val::Invalid),
        "Constant evaluation yielded an invalid value, this is probably an internal error",
    );
    Ok(val)
}

// TODO: give errors a span by giving all IR instructions spans.
unsafe fn eval_internal(ir: &FunctionIr, types: &IrTypes, params: &[Val], stack: &mut StackMem) -> Result<Val, Error> {
    let mut values = vec![Val::Invalid; ir.inst.len()];

    let get_ref_and_ty = |values: &[Val], r: Ref| -> (Val, IrType) {
        if let Some(r) = r.into_ref() {
            (values[r as usize], types[ir.inst[r as usize].ty])
        } else {
            use crate::RefVal;
            match r.into_val().unwrap() {
                RefVal::True => (Val::Int(1), IrType::Primitive(Primitive::U1)),
                RefVal::False => (Val::Int(0), IrType::Primitive(Primitive::U1)),
                RefVal::Unit => (Val::Unit, IrType::Primitive(Primitive::Unit)),
                RefVal::Undef => panic!("reached undefined"),
            }
        }
    };
    let get_ref = |values: &[Val], r: Ref| -> Val { get_ref_and_ty(values, r).0 };
    let mut pos: u32 = 0;
    let mut previous_block = BlockIndex(0);
    let mut current_block = BlockIndex(0);
    let mut backwards_jumps = 0;

    macro_rules! bin_op {
        ($op: tt, $inst: expr) => {{
            let l = get_ref(&values, $inst.data.bin_op.0);
            let r = get_ref(&values, $inst.data.bin_op.1);

            match types[$inst.ty] {
                IrType::Primitive(p) if p.is_int() => {
                    let Val::Int(l_val) = l else { panic!() };
                    let Val::Int(r_val) = r else { panic!() };
                    Val::Int(l_val $op r_val)
                }
                IrType::Const(ConstIrType::Int) => {
                    let Val::Int(l_val) = l else { panic!() };
                    let Val::Int(r_val) = r else { panic!() };
                    Val::Int(l_val $op r_val)
                }
                IrType::Primitive(Primitive::F32) => {
                    let Val::F32(l_val) = l else { panic!() };
                    let Val::F32(r_val) = r else { panic!() };
                    Val::F32(l_val $op r_val)
                }
                IrType::Primitive(Primitive::F64) | IrType::Const(ConstIrType::Float) => {
                    let Val::F64(l_val) = l else { panic!() };
                    let Val::F64(r_val) = r else { panic!() };
                    Val::F64(l_val $op r_val)
                }
                t => panic!("Invalid type for binary operation: {t:?}")
            }
        }};
    }
    macro_rules! cmp_op {
        ($op: tt, $inst: expr) => {{
            let l = get_ref(&values, $inst.data.bin_op.0);
            let r = get_ref(&values, $inst.data.bin_op.1);

            match (l, r) {
                (Val::Int(l_val), Val::Int(r_val)) => Val::Int((l_val $op r_val) as u64),
                (Val::F32(l_val), Val::F32(r_val)) => Val::Int((l_val $op r_val) as u64),
                (Val::F64(l_val), Val::F64(r_val)) => Val::Int((l_val $op r_val) as u64),
                (l, r) => panic!("Invalid values for comparison: {l:?}, {r:?}")
            }
        }};
    }

    let val = loop {
        let inst = ir.inst[pos as usize];
        let value = match inst.tag {
            super::Tag::BlockBegin => {
                previous_block = current_block;
                current_block = inst.data.block;
                Val::Invalid
            }
            super::Tag::Ret => break get_ref(&values, inst.data.un_op),
            super::Tag::Param => params[inst.data.int32 as usize],
            super::Tag::Uninit => Val::Invalid,
            super::Tag::Int => Val::Int(inst.data.int),
            super::Tag::LargeInt => {
                let bytes = &ir.extra[
                    inst.data.extra as usize
                    .. (inst.data.extra + 16) as usize
                ];
                let mut bytes_arr = [0; 16];
                bytes_arr.copy_from_slice(bytes);
                todo!("support large ints")
            }
            super::Tag::Float => match types[inst.ty] {
                IrType::Primitive(Primitive::F32) => Val::F32(inst.data.float as f32),
                IrType::Primitive(Primitive::F64) => Val::F64(inst.data.float),
                _ => panic!("invalid type"),
            },
            super::Tag::Decl => {
                // TODO: go through decls only once, this will overflow the stack in loops right now
                let layout = type_layout(types[inst.ty], &types);
                let pointer = stack.alloc(layout);
                Val::StackPointer(pointer)
            }
            super::Tag::Load => {
                let Val::StackPointer(addr) = values[inst.data.un_op.into_ref().unwrap() as usize]
                    else { panic!() };
                match types[inst.ty] {
                    IrType::Primitive(p) => {
                        let layout = primitive_layout(p);
                        let bytes = stack.load(addr, layout.size);
                        use Primitive as P;
                        match p {
                            P::U1 => {
                                debug_assert!(bytes[0] < 2);
                                Val::Int(bytes[0] as u64)
                            }
                            P::I8 | P::U8 => Val::Int(u8::from_le_bytes(bytes.try_into().unwrap()) as u64),
                            P::I16 | P::U16 => Val::Int(u16::from_le_bytes(bytes.try_into().unwrap()) as u64),
                            P::I32 | P::U32 => Val::Int(u32::from_le_bytes(bytes.try_into().unwrap()) as u64),
                            P::I64 | P::U64 => Val::Int(u64::from_le_bytes(bytes.try_into().unwrap())),
                            P::I128 | P::U128 => todo!(),
                            P::F32 => Val::F32(f32::from_le_bytes(bytes.try_into().unwrap())),
                            P::F64 => Val::F64(f64::from_le_bytes(bytes.try_into().unwrap())),
                            P::Ptr => Val::StackPointer(StackAddr(u32::from_le_bytes(stack.load_array(addr)))),
                            P::Unit => Val::Unit,
                        }
                    }
                    _ => todo!("load complex types"),
                }
            }
            super::Tag::Store => {
                let (var, val) = inst.data.bin_op;
                let Val::StackPointer(addr) = get_ref(&values, var) else { panic!() };
                let (val, ty) = get_ref_and_ty(&values, val);
                match val {
                    Val::Unit | Val::Invalid => {}
                    Val::Int(i) => match ty {
                        IrType::Primitive(Primitive::I8 | Primitive::U8) => stack.store(addr, &(i as u8).to_le_bytes()),
                        IrType::Primitive(Primitive::I16 | Primitive::U16) => stack.store(addr, &(i as u16).to_le_bytes()),
                        IrType::Primitive(Primitive::I32 | Primitive::U32) => stack.store(addr, &(i as u32).to_le_bytes()),
                        IrType::Primitive(Primitive::I64 | Primitive::U64) => stack.store(addr, &(i as u64).to_le_bytes()),
                        _ => panic!(),
                    }
                    Val::F32(v) => stack.store(addr, &v.to_le_bytes()),
                    Val::F64(v) => stack.store(addr, &v.to_le_bytes()),
                    Val::StackPointer(addr) => stack.store(addr, &addr.0.to_le_bytes()),
                }
                Val::Invalid
            }
            super::Tag::String => {
                let _string = ir.extra[
                    inst.data.extra_len.0 as usize
                    .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                ].to_vec();
                todo!()
            }
            super::Tag::Call => {
                todo!();
            }
            super::Tag::Neg => {
                match get_ref(&values, inst.data.un_op) {
                    Val::Invalid => Val::Invalid,
                    Val::Int(val) => Val::Int(-(val as i64) as u64),
                    Val::F32(val) => Val::F32(-val),
                    Val::F64(val) => Val::F64(-val),
                    _ => panic!("Invalid value to negate")
                }
            }
            super::Tag::Not => {
                let val = get_ref(&values, inst.data.un_op);
                match val {
                    Val::Int(0) => Val::Int(1),
                    Val::Int(1) => Val::Int(0),
                    _ => panic!()
                }
            }
            super::Tag::Add => bin_op!(+, inst),
            super::Tag::Sub => bin_op!(-, inst),
            super::Tag::Mul => bin_op!(*, inst),
            super::Tag::Div => bin_op!(/, inst),
            super::Tag::Mod => bin_op!(%, inst),
            super::Tag::Or => {
                let (Val::Int(a), Val::Int(b)) = (
                    get_ref(&values, inst.data.bin_op.0),
                    get_ref(&values, inst.data.bin_op.1)
                ) else { panic!("Invalid values for or") };
                Val::Int((a != 0 || b != 0) as u64)
            }
            super::Tag::And => {
                let (Val::Int(a), Val::Int(b)) = (
                    get_ref(&values, inst.data.bin_op.0),
                    get_ref(&values, inst.data.bin_op.1)
                ) else { panic!("Invalid values for and") };
                Val::Int((a != 0 && b != 0) as u64)
            }
            super::Tag::Eq => {
                let l = get_ref(&values, inst.data.bin_op.0);
                let r = get_ref(&values, inst.data.bin_op.1);
                Val::Int(l.equals(r) as u64)
            }
            super::Tag::NE => {
                let l = get_ref(&values, inst.data.bin_op.0);
                let r = get_ref(&values, inst.data.bin_op.1);
                Val::Int(!l.equals(r) as u64)
            }
            super::Tag::LT => cmp_op!(< , inst),
            super::Tag::GT => cmp_op!(> , inst),
            super::Tag::LE => cmp_op!(<=, inst),
            super::Tag::GE => cmp_op!(>=, inst),
            super::Tag::Member => {
                todo!("should give pointer to member")
                /*
                let ConstVal::Int(_, member) = get_ref(&values, inst.data.bin_op.1)
                    else { panic!("member should be an int") };
                let var_idx = inst.data.bin_op.0.into_ref().expect("Can't get member of value");
                values[pos as usize] = match &values[var_idx as usize] {
                    LocalVal::Val(_) => panic!("Member used on value '{:?}'", values[var_idx as usize]),
                    LocalVal::Var(_) => LocalVal::VarMember(var_idx, vec![member as u32]),
                    LocalVal::VarMember(idx, members) => LocalVal::VarMember(
                        *idx,
                        members.iter().copied().chain([member as _]).collect()
                    ),
                };
                pos += 1;
                continue;
                */
            }
            super::Tag::Value => todo!(),
            super::Tag::Cast => todo!(),
            super::Tag::Goto => {
                let target = ir.blocks[inst.data.int32 as usize];
                if target <= pos {
                    backwards_jumps += 1;
                    if backwards_jumps > BACKWARDS_JUMP_LIMIT {
                        return Err(Error::InfiniteLoop)
                    }
                }
                pos = target;
                continue;
            }
            super::Tag::Branch => {
                let val = get_ref(&values, inst.data.ref_int.0);
                let i = inst.data.ref_int.1 as usize;
                let mut bytes = [0; 4];
                bytes.copy_from_slice(&ir.extra[i..i+4]);
                let a = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&ir.extra[i+4..i+8]);
                let b = u32::from_le_bytes(bytes);
                let val = match val {
                    Val::Int(0) => false,
                    Val::Int(1) => true,
                    _ => panic!("bool value expected"),
                };
                let target = if val { ir.blocks[a as usize] } else { ir.blocks[b as usize] };
                if target <= pos {
                    backwards_jumps += 1;
                    if backwards_jumps > BACKWARDS_JUMP_LIMIT {
                        return Err(Error::InfiniteLoop)
                    }
                }
                pos = target;
                continue;

            }
            super::Tag::Phi => {
                let mut val = None;
                for i in 0..inst.data.extra_len.1 {
                    let mut current_bytes = [0; 4];
                    let begin = (inst.data.extra_len.0 + i * 8) as usize;
                    current_bytes.copy_from_slice(&ir.extra[begin..begin + 4]);
                    let block = BlockIndex(u32::from_le_bytes(current_bytes));
                    current_bytes.copy_from_slice(&ir.extra[begin + 4 .. begin + 8]);
                    current_bytes.copy_from_slice(&ir.extra[begin + 4 .. begin + 8]);
                    let r = Ref::from_bytes(current_bytes);
                    if block == previous_block {
                        val = Some(get_ref(&values, r));
                        break;
                    }
                }
                val.expect("Invalid phi node: didn't go through any of the blocks")
            }
            super::Tag::Asm => todo!(),
            super::Tag::EnumTag | super::Tag::EnumValueTag
            | super::Tag::EnumVariantMember | super::Tag::EnumValueVariantMember 
            => todo!("eval enums"),
        };
        values[pos as usize] = value;
        pos += 1;
    };
    Ok(val)
}
