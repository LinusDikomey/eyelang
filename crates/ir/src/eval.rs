use std::any::Any;

use crate::{
    ir_types::{ConstIrType, IrType, IrTypes},
    layout::{type_layout, Layout},
    BlockIndex, Function, FunctionId, FunctionIr, Ref,
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

pub struct StackMem {
    mem: Vec<u8>,
}
impl StackMem {
    pub fn new() -> StackMem {
        Self { mem: Vec::new() }
    }

    pub fn alloc(&mut self, layout: Layout) -> StackAddr {
        let addr = self.mem.len();
        self.mem.resize_with(addr + layout.size as usize, || 0);
        StackAddr(addr as _)
    }

    pub fn store(&mut self, addr: StackAddr, value: &[u8]) {
        self.mem[addr.0 as usize..addr.0 as usize + value.len()].copy_from_slice(value);
    }

    pub fn load_n<const N: usize>(&mut self, addr: StackAddr) -> [u8; N] {
        let mut arr = [0; N];
        arr.copy_from_slice(&self.mem[addr.0 as usize..addr.0 as usize + N]);
        arr
    }

    pub fn sp(&self) -> usize {
        self.mem.len()
    }

    pub fn restore_sp(&mut self, sp: usize) {
        debug_assert!(sp <= self.mem.len());
        self.mem.truncate(sp);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct StackAddr(u32);

pub const BACKWARDS_JUMP_LIMIT: usize = 1000;

#[derive(Debug, Clone)]
pub enum Error {
    InfiniteLoop,
    ExternCallFailed(Box<str>),
}

pub trait Environment {
    fn get_function(&mut self, id: FunctionId) -> &Function;

    fn call_extern(
        &mut self,
        _id: FunctionId,
        _args: &[Val],
        _stack: &mut StackMem,
    ) -> Result<Val, Box<str>> {
        Err("Can't evaluate extern functions".into())
    }
}
impl Environment for crate::Module {
    fn get_function(&mut self, id: FunctionId) -> &Function {
        &self.funcs[id.0 as usize]
    }
}

pub struct EmptyEnv;
impl Environment for EmptyEnv {
    fn get_function(&mut self, id: FunctionId) -> &Function {
        panic!("EmptyEnv doesn't provide any functions but tried to retrieve {id:?}")
    }
}

// TODO: validate params
// TODO: give errors a span by giving all IR instructions spans.
pub fn eval<E: Environment>(
    top_level_ir: &FunctionIr,
    top_level_types: &IrTypes,
    params: &[Val],
    env: &mut E,
) -> Result<Val, Error> {
    let top_level_function = (top_level_ir, top_level_types);
    let mut stack = StackMem::new();
    let mut values = vec![Val::Invalid; top_level_ir.inst.len()];
    let mut current_function = None;
    values[..params.len()].copy_from_slice(params);
    let entry_args = top_level_ir.get_block_args(BlockIndex::ENTRY);
    values[entry_args.range()].copy_from_slice(params);

    let mut pc: u32 = top_level_ir
        .get_block_range(top_level_ir.blocks().next().unwrap())
        .start;
    let mut call_stack: Vec<StackFrame> = vec![];
    let mut backwards_jumps = 0;

    let val = 'outer: loop {
        let (ir, types) = current_function.map_or(top_level_function, |id| {
            let function = env.get_function(id);
            (function.ir.as_ref().unwrap(), &function.types)
        });

        let get_ref_and_ty = |values: &[Val], r: Ref| -> (Val, IrType) {
            if let Some(r) = r.into_ref() {
                (values[r as usize], types[ir.inst[r as usize].ty])
            } else {
                use crate::RefVal;
                match r.into_val().unwrap() {
                    RefVal::True => (Val::Int(1), IrType::U1),
                    RefVal::False => (Val::Int(0), IrType::U1),
                    RefVal::Unit => (Val::Unit, IrType::U1),
                    RefVal::Undef => panic!("reached undefined"),
                }
            }
        };
        let get_ref = |values: &[Val], r: Ref| -> Val { get_ref_and_ty(values, r).0 };
        macro_rules! bin_op {
            ($op: tt, $inst: expr) => {{
                let l = get_ref(&values, $inst.data.bin_op().0);
                let r = get_ref(&values, $inst.data.bin_op().1);

                match types[$inst.ty] {
                    t if t.is_int() => {
                        let Val::Int(l_val) = l else { panic!() };
                        let Val::Int(r_val) = r else { panic!() };
                        Val::Int(l_val $op r_val)
                    }
                    IrType::Const(ConstIrType::Int) => {
                        let Val::Int(l_val) = l else { panic!() };
                        let Val::Int(r_val) = r else { panic!() };
                        Val::Int(l_val $op r_val)
                    }
                    IrType::F32 => {
                        let Val::F32(l_val) = l else { panic!() };
                        let Val::F32(r_val) = r else { panic!() };
                        Val::F32(l_val $op r_val)
                    }
                    IrType::F64 | IrType::Const(ConstIrType::Float) => {
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
                let l = get_ref(&values, $inst.data.bin_op().0);
                let r = get_ref(&values, $inst.data.bin_op().1);

                match (l, r) {
                    (Val::Int(l_val), Val::Int(r_val)) => Val::Int((l_val $op r_val) as u64),
                    (Val::F32(l_val), Val::F32(r_val)) => Val::Int((l_val $op r_val) as u64),
                    (Val::F64(l_val), Val::F64(r_val)) => Val::Int((l_val $op r_val) as u64),
                    (l, r) => panic!("Invalid values for comparison: {l:?}, {r:?}")
                }
            }};
        }
        // the inner loop should never break
        let _: std::convert::Infallible = loop {
            let inst = ir.inst[pc as usize];
            let value = match inst.tag {
                super::Tag::Nothing => Val::Invalid,
                super::Tag::Ret => {
                    let return_val = get_ref(&values, inst.data.un_op());
                    let Some(frame) = call_stack.pop() else {
                        // the function that was originally evaluated returned, break to return the
                        // value from eval
                        break 'outer return_val;
                    };
                    current_function = frame.function;
                    pc = frame.pc;
                    stack.restore_sp(frame.sp);
                    values = frame.values;
                    values[pc as usize] = return_val;
                    pc += 1;
                    continue 'outer;
                }
                super::Tag::BlockArg => unreachable!("BlockArg should never exist inside a block"),
                super::Tag::Global => todo!("handle globals in const eval"),
                super::Tag::Int => Val::Int(inst.data.int()),
                super::Tag::LargeInt => {
                    let bytes =
                        &ir.extra[inst.data.extra() as usize..(inst.data.extra() + 16) as usize];
                    let mut bytes_arr = [0; 16];
                    bytes_arr.copy_from_slice(bytes);
                    todo!("support large ints")
                }
                super::Tag::Float => match types[inst.ty] {
                    IrType::F32 => Val::F32(inst.data.float() as f32),
                    IrType::F64 => Val::F64(inst.data.float()),
                    _ => panic!("invalid type"),
                },
                super::Tag::Decl => {
                    let layout = type_layout(types[inst.ty], &types);
                    let pointer = stack.alloc(layout);
                    Val::StackPointer(pointer)
                }
                super::Tag::Load => {
                    let Val::StackPointer(addr) =
                        values[inst.data.un_op().into_ref().unwrap() as usize]
                    else {
                        panic!()
                    };

                    use IrType as P;
                    match types[inst.ty] {
                        P::U1 => {
                            let [v] = stack.load_n(addr);
                            debug_assert!(v < 2);
                            Val::Int(v as u64)
                        }
                        P::I8 | P::U8 => Val::Int(u8::from_le_bytes(stack.load_n(addr)) as u64),
                        P::I16 | P::U16 => Val::Int(u16::from_le_bytes(stack.load_n(addr)) as u64),
                        P::I32 | P::U32 => Val::Int(u32::from_le_bytes(stack.load_n(addr)) as u64),
                        P::I64 | P::U64 => Val::Int(u64::from_le_bytes(stack.load_n(addr))),
                        P::I128 | P::U128 => todo!(),
                        P::F32 => Val::F32(f32::from_le_bytes(stack.load_n(addr))),
                        P::F64 => Val::F64(f64::from_le_bytes(stack.load_n(addr))),
                        P::Ptr => {
                            Val::StackPointer(StackAddr(u32::from_le_bytes(stack.load_n(addr))))
                        }
                        P::Unit => Val::Unit,
                        _ => todo!("load complex types"),
                    }
                }
                super::Tag::Store => {
                    let (var, val) = inst.data.bin_op();
                    let Val::StackPointer(addr) = get_ref(&values, var) else {
                        panic!()
                    };
                    let (val, ty) = get_ref_and_ty(&values, val);
                    match val {
                        Val::Unit | Val::Invalid => {}
                        Val::Int(i) => match ty {
                            IrType::I8 | IrType::U8 => stack.store(addr, &(i as u8).to_le_bytes()),
                            IrType::I16 | IrType::U16 => {
                                stack.store(addr, &(i as u16).to_le_bytes())
                            }
                            IrType::I32 | IrType::U32 => {
                                stack.store(addr, &(i as u32).to_le_bytes())
                            }
                            IrType::I64 | IrType::U64 => {
                                stack.store(addr, &(i as u64).to_le_bytes())
                            }
                            _ => panic!(),
                        },
                        Val::F32(v) => stack.store(addr, &v.to_le_bytes()),
                        Val::F64(v) => stack.store(addr, &v.to_le_bytes()),
                        Val::StackPointer(addr) => stack.store(addr, &addr.0.to_le_bytes()),
                    }
                    Val::Invalid
                }
                super::Tag::String => {
                    let _string = ir.extra[inst.data.extra_len().0 as usize
                        ..(inst.data.extra_len().0 + inst.data.extra_len().1) as usize]
                        .to_vec();
                    todo!("evaluate strings")
                }
                super::Tag::Call => {
                    let (func_id, args) = inst.data.call(&ir.extra);
                    let args: Vec<_> = args.map(|r| get_ref(&values, r)).collect();
                    let func = env.get_function(func_id);
                    if let Some(func_ir) = &func.ir {
                        let mut new_values = vec![Val::Invalid; func_ir.inst.len()];
                        let entry = BlockIndex::ENTRY;
                        let args_range = func_ir.get_block_args(entry).range();
                        new_values[args_range].copy_from_slice(&args);
                        call_stack.push(StackFrame {
                            function: current_function,
                            pc,
                            sp: stack.sp(),
                            values,
                        });
                        pc = func_ir
                            .get_block_range(func_ir.blocks().next().unwrap())
                            .start;
                        values = new_values;
                        current_function = Some(func_id);
                        // this will fetch ir and types again based on current_function
                        continue 'outer;
                    } else {
                        let res = env
                            .call_extern(func_id, &args, &mut stack)
                            .map_err(|s| Error::ExternCallFailed(s))?;
                        values[pc as usize] = res;
                        pc += 1;
                        continue 'outer;
                    }
                }
                super::Tag::Neg => match get_ref(&values, inst.data.un_op()) {
                    Val::Invalid => Val::Invalid,
                    Val::Int(val) => Val::Int(-(val as i64) as u64),
                    Val::F32(val) => Val::F32(-val),
                    Val::F64(val) => Val::F64(-val),
                    _ => panic!("Invalid value to negate"),
                },
                super::Tag::Not => {
                    let val = get_ref(&values, inst.data.un_op());
                    match val {
                        Val::Int(0) => Val::Int(1),
                        Val::Int(1) => Val::Int(0),
                        _ => panic!(),
                    }
                }
                super::Tag::Add => bin_op!(+, inst),
                super::Tag::Sub => bin_op!(-, inst),
                super::Tag::Mul => bin_op!(*, inst),
                super::Tag::Div => bin_op!(/, inst),
                super::Tag::Rem => bin_op!(%, inst),
                super::Tag::Or => {
                    let (Val::Int(a), Val::Int(b)) = (
                        get_ref(&values, inst.data.bin_op().0),
                        get_ref(&values, inst.data.bin_op().1),
                    ) else {
                        panic!("Invalid values for or")
                    };
                    Val::Int((a != 0 || b != 0) as u64)
                }
                super::Tag::And => {
                    let (Val::Int(a), Val::Int(b)) = (
                        get_ref(&values, inst.data.bin_op().0),
                        get_ref(&values, inst.data.bin_op().1),
                    ) else {
                        panic!("Invalid values for and")
                    };
                    Val::Int((a != 0 && b != 0) as u64)
                }
                super::Tag::Eq => {
                    let l = get_ref(&values, inst.data.bin_op().0);
                    let r = get_ref(&values, inst.data.bin_op().1);
                    Val::Int(l.equals(r) as u64)
                }
                super::Tag::NE => {
                    let l = get_ref(&values, inst.data.bin_op().0);
                    let r = get_ref(&values, inst.data.bin_op().1);
                    Val::Int(!l.equals(r) as u64)
                }
                super::Tag::LT => cmp_op!(< , inst),
                super::Tag::GT => cmp_op!(> , inst),
                super::Tag::LE => cmp_op!(<=, inst),
                super::Tag::GE => cmp_op!(>=, inst),
                super::Tag::MemberPtr => {
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
                super::Tag::MemberValue => todo!(),
                super::Tag::InsertMember => todo!(),
                super::Tag::ArrayIndex => todo!(),
                super::Tag::CastInt => {
                    let (v, from_ty) = get_ref_and_ty(&values, inst.data.un_op());
                    debug_assert!(from_ty.is_int());
                    debug_assert!(types[inst.ty].is_int());
                    // integers values are always represented the same right now
                    v
                }
                super::Tag::CastFloat => {
                    let v = get_ref(&values, inst.data.un_op());
                    let to_ty = types[inst.ty];
                    match (v, to_ty) {
                        (Val::F32(v), IrType::F32) => Val::F32(v),
                        (Val::F32(v), IrType::F64) => Val::F64(v as f64),
                        (Val::F64(v), IrType::F32) => Val::F32(v as f32),
                        (Val::F64(v), IrType::F64) => Val::F64(v),
                        _ => panic!("invalid types for float cast"),
                    }
                }
                super::Tag::CastIntToFloat => {
                    let Val::Int(v) = get_ref(&values, inst.data.un_op()) else {
                        panic!("invalid type for CastIntToFloat");
                    };
                    let to_ty = types[inst.ty];
                    match to_ty {
                        IrType::F32 => Val::F32(v as f32),
                        IrType::F64 => Val::F64(v as f64),
                        _ => panic!("invalid target type for CastIntToFloat"),
                    }
                }
                super::Tag::CastFloatToInt => {
                    let v = match get_ref(&values, inst.data.un_op()) {
                        Val::F32(v) => v as f64, // casting f32 to f64 first should never be an issue
                        Val::F64(v) => v,
                        _ => panic!("invalid type for CastFloatToInt"),
                    };
                    let to_ty = types[inst.ty];
                    match to_ty {
                        IrType::U8 => Val::Int(v as u8 as u64),
                        IrType::U16 => Val::Int(v as u16 as u64),
                        IrType::U32 => Val::Int(v as u16 as u64),
                        IrType::U64 => Val::Int(v as u64),
                        IrType::I8 => Val::Int(v as i8 as u64),
                        IrType::I16 => Val::Int(v as i16 as u64),
                        IrType::I32 => Val::Int(v as i16 as u64),
                        IrType::I64 => Val::Int(v as i64 as u64),
                        IrType::U128 | IrType::I128 => {
                            todo!("evaluate 128 bit int values")
                        }
                        _ => panic!("invalid target type for CastIntToFloat"),
                    }
                }
                super::Tag::Goto => {
                    let (target, extra_idx) = inst.data.goto();
                    let args = decode_block_args(ir, target, extra_idx);
                    let target_pos = ir.blocks[target.idx() as usize].start;
                    if target_pos <= pc {
                        backwards_jumps += 1;
                        if backwards_jumps > BACKWARDS_JUMP_LIMIT {
                            return Err(Error::InfiniteLoop);
                        }
                    }
                    let arg_count = args.len() as u32;
                    for (r, i) in args.zip(target_pos - arg_count..target_pos) {
                        values[i as usize] = get_ref(&values, r);
                    }
                    pc = target_pos;
                    continue;
                }
                super::Tag::Branch => {
                    let (cond, a, b, i) = inst.data.branch(&ir.extra);
                    let val = get_ref(&values, cond);
                    let val = match val {
                        Val::Int(0) => false,
                        Val::Int(1) => true,
                        _ => panic!("bool value expected"),
                    };
                    let a_arg_count = ir.blocks[a.idx() as usize].arg_count;
                    let b_arg_count = ir.blocks[b.idx() as usize].arg_count;
                    let (target, args_idx, arg_count) = if val {
                        (a, i, a_arg_count)
                    } else {
                        (b, i + a_arg_count as usize * 4, b_arg_count)
                    };
                    let target_pos = ir.blocks[target.idx() as usize].start;
                    if target_pos <= pc {
                        backwards_jumps += 1;
                        if backwards_jumps > BACKWARDS_JUMP_LIMIT {
                            return Err(Error::InfiniteLoop);
                        }
                    }
                    let args = decode_block_args(ir, target, args_idx);
                    for (r, i) in args.zip(target_pos - arg_count..target_pos) {
                        values[i as usize] = get_ref(&values, r);
                    }
                    pc = target_pos;
                    continue;
                }
                super::Tag::IntToPtr => {
                    todo!("IntToPtr semantics, might have to be disallowed at compile time")
                }
                super::Tag::PtrToInt => {
                    todo!("PtrToInt semantics, might have to be disallowed at compile time")
                }
                super::Tag::Asm => todo!(), // TODO: error handling
            };
            values[pc as usize] = value;
            pc += 1;
        };
    };
    assert!(
        !matches!(val, Val::Invalid),
        "Constant evaluation yielded an invalid value, this is probably an internal error",
    );
    Ok(val)
}

struct StackFrame {
    /// if None, return to the original function that was passed to eval
    function: Option<FunctionId>,
    pc: u32,
    sp: usize,
    values: Vec<Val>,
}

fn decode_block_args<'a>(
    ir: &'a FunctionIr,
    target: BlockIndex,
    extra_idx: usize,
) -> impl 'a + ExactSizeIterator<Item = Ref> {
    let block_arg_count = ir.blocks[target.idx() as usize].arg_count;
    let mut bytes = [0; 4];
    (0..block_arg_count).map(move |i| {
        let i = extra_idx + i as usize * 4;
        bytes.copy_from_slice(&ir.extra[i..i + 4]);
        Ref::from_bytes(bytes)
    })
}
