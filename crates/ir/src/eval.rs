use std::fmt;

use crate::{
    ir_types::{IrType, IrTypes},
    layout::{type_layout, Layout},
    BlockIndex, Function, FunctionId, FunctionIr, Ref, Tag,
};

pub const BACKWARDS_JUMP_LIMIT: usize = 1000;
pub const STACK_SIZE: u32 = 8_000_000;
pub const STACK_FRAME_COUNT: usize = 10000;

#[derive(Clone, Debug)]
pub enum Val {
    Invalid,
    Unit,
    Int(u64),
    F32(f32),
    F64(f64),
    Ptr(Ptr),
    Array(Box<[Val]>),
    Tuple(Box<[Val]>),
}
impl Val {
    fn equals(&self, r: &Val) -> bool {
        match (self, r) {
            (Val::Int(a), Val::Int(b)) => a == b,
            (Val::Unit, Val::Unit) => true,
            (Val::F32(a), Val::F32(b)) => a == b,
            (Val::F64(a), Val::F64(b)) => a == b,
            (Val::Ptr(a), Val::Ptr(b)) => a.addr == b.addr,
            (Val::Array(a), Val::Array(b)) | (Val::Tuple(a), Val::Tuple(b)) => {
                a.iter().zip(b.iter()).all(|(a, b)| Val::equals(a, b))
            }
            _ => panic!("invalid types for equality check"),
        }
    }
}

const STACK_BIT: u32 = 1 << 31;

pub struct Mem {
    stack: Vec<u8>,
    heap: Vec<u8>,
}
impl Default for Mem {
    fn default() -> Self {
        Self::new()
    }
}
impl Mem {
    pub fn new() -> Self {
        Self {
            stack: Vec::new(),
            heap: vec![0], // to cover null pointers
        }
    }

    pub fn stack_alloc(&mut self, layout: Layout) -> Result<Ptr, Error> {
        let addr = self.stack.len();
        if self.stack.len() as u64 + layout.size > STACK_SIZE as u64 {
            return Err(Error::StackOverflow);
        }
        self.stack.resize_with(addr + layout.size as usize, || 0);
        Ok(Ptr {
            addr: addr as u32 | STACK_BIT,
            size: layout.size as u32,
        })
    }

    pub fn sp(&self) -> u32 {
        self.stack.len() as u32
    }

    pub fn restore_sp(&mut self, sp: u32) {
        debug_assert!(sp <= self.stack.len() as u32);
        self.stack.truncate(sp as usize);
    }
    pub fn malloc(&mut self, layout: Layout) -> Result<Ptr, OomError> {
        if self.heap.len() as u64 + layout.size >= STACK_BIT as u64 {
            return Err(OomError);
        }
        let addr = Ptr {
            addr: self.heap.len() as u32,
            size: layout.size as u32,
        };
        self.heap
            .extend(std::iter::repeat(0).take(layout.size as usize));
        Ok(addr)
    }

    pub fn load_n<const N: usize>(&mut self, mut ptr: Ptr) -> [u8; N] {
        let mem = if ptr.addr & STACK_BIT != 0 {
            ptr.addr &= !STACK_BIT;
            &mut self.stack
        } else {
            &mut self.heap
        };
        let mut arr = [0; N];
        arr.copy_from_slice(&mem[ptr.addr as usize..ptr.addr as usize + N]);
        arr
    }

    pub fn store(&mut self, mut ptr: Ptr, value: &[u8]) {
        let mem = if ptr.addr & STACK_BIT != 0 {
            ptr.addr &= !STACK_BIT;
            &mut self.stack
        } else {
            &mut self.heap
        };
        mem[ptr.addr as usize..ptr.addr as usize + value.len()].copy_from_slice(value);
    }

    pub fn free(&mut self, _ptr: Ptr, _layout: Layout) {
        // TODO: proper allocator that can free, also: verify that free call was valid
    }
}

pub struct OomError;

#[derive(Clone, Copy)]
pub struct Ptr {
    pub addr: u32,
    pub size: u32,
}
impl fmt::Debug for Ptr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Ptr")
            .field(
                "addr",
                &if self.addr & STACK_BIT != 0 {
                    self.addr & !STACK_BIT
                } else {
                    self.addr
                },
            )
            .field(
                "location",
                &if self.addr & STACK_BIT != 0 {
                    "stack"
                } else {
                    "heap"
                },
            )
            .field("size", &self.size)
            .finish()
    }
}

impl Ptr {
    pub fn from_u64(x: u64) -> Self {
        Ptr {
            addr: (x >> 32) as u32,
            size: x as u32,
        }
    }

    pub fn into_u64(self) -> u64 {
        (self.addr as u64) << 32 | self.size as u64
    }

    #[must_use = "returns a new pointer"]
    pub fn add_offset(self, offset: u32) -> Result<Self, ProvenanceError> {
        let size = self.size.checked_sub(offset).ok_or(ProvenanceError)?;
        Ok(Self {
            addr: self.addr + offset,
            size,
        })
    }
}

pub struct ProvenanceError;

#[derive(Debug, Clone)]
pub enum Error {
    InfiniteLoop,
    ExternCallFailed(Box<str>),
    StackOverflow,
    ProvenanceViolation,
    OutOfMemory,
}
impl From<ProvenanceError> for Error {
    fn from(_: ProvenanceError) -> Self {
        Self::ProvenanceViolation
    }
}

pub trait Environment {
    fn get_function(&mut self, id: FunctionId) -> &Function;

    fn call_extern(
        &mut self,
        _id: FunctionId,
        _args: &[Val],
        _mem: &mut Mem,
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
    let mut mem = Mem::new();

    let mut values = Values::new(top_level_ir, top_level_types);
    let mut current_function = None;
    for (param, i) in params
        .iter()
        .zip(top_level_ir.get_block_args(BlockIndex::ENTRY).iter())
    {
        // TODO: check that the type fits
        // let ty = top_level_types[top_level_ir.inst[i as usize].ty];
        values.store(i, param);
    }

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

        let get_ref_and_ty = |values: &Values, r: Ref| -> (Val, IrType) {
            if let Some(r) = r.into_ref() {
                let ty = types[ir.inst[r as usize].ty];
                (values.load(r, ty, types), ty)
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
        let get_ref = |values: &Values, r: Ref| -> Val { get_ref_and_ty(values, r).0 };
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
                    IrType::F32 => {
                        let Val::F32(l_val) = l else { panic!() };
                        let Val::F32(r_val) = r else { panic!() };
                        Val::F32(l_val $op r_val)
                    }
                    IrType::F64 => {
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
            //eprintln!("evaluating {} {:?} pc={pc}", inst.tag, inst.data);
            let value = match inst.tag {
                super::Tag::Nothing => Val::Invalid,
                super::Tag::Ret => {
                    let return_val = get_ref(&values, inst.data.un_op());
                    //eprintln!("  -> returning {return_val:?}");
                    let Some(mut frame) = call_stack.pop() else {
                        // the function that was originally evaluated returned, break to return the
                        // value from eval
                        break 'outer return_val;
                    };
                    current_function = frame.function;
                    pc = frame.pc;
                    mem.restore_sp(frame.sp);
                    frame.values.store(pc, &return_val);
                    values = frame.values;
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
                    let layout = type_layout(types[inst.data.ty()], types);
                    Val::Ptr(mem.stack_alloc(layout)?)
                }
                super::Tag::Load => {
                    let ptr = values.load_ptr(inst.data.un_op());
                    values.load_primitives(pc, types[inst.ty], types, |size, offset| {
                        let ptr = ptr.add_offset(offset)?;
                        let val = match size {
                            PrimitiveSize::S8 => u8::from_le_bytes(mem.load_n(ptr)) as u64,
                            PrimitiveSize::S16 => u16::from_le_bytes(mem.load_n(ptr)) as u64,
                            PrimitiveSize::S32 => u32::from_le_bytes(mem.load_n(ptr)) as u64,
                            PrimitiveSize::S64 => u64::from_le_bytes(mem.load_n(ptr)),
                        };
                        //eprintln!("  .. read {} bytes at {ptr:?} -> {val}", size.byte_size());
                        Ok(val)
                    })?;
                    pc += 1;
                    continue;
                }
                super::Tag::Store => {
                    let (var, val) = inst.data.bin_op();
                    let Val::Ptr(mut ptr) = get_ref(&values, var) else {
                        panic!()
                    };
                    //let (val, ty) = get_ref_and_ty(&values, val);
                    //eprintln!("  storing {val:?} into {ptr:?}",);
                    values.visit_primitives(val, ir, types, |p| {
                        //eprintln!("  storing {p:?} {ptr:?}");
                        match p {
                            PrimitiveVal::I8(x) => {
                                let new_ptr = ptr.add_offset(1)?;
                                mem.store(ptr, &[x]);
                                ptr = new_ptr;
                            }
                            PrimitiveVal::I16(x) => {
                                let new_ptr = ptr.add_offset(2)?;
                                mem.store(ptr, &x.to_le_bytes());
                                ptr = new_ptr;
                            }
                            PrimitiveVal::I32(x) => {
                                let new_ptr = ptr.add_offset(4)?;
                                mem.store(ptr, &x.to_le_bytes());
                                ptr = new_ptr;
                            }
                            PrimitiveVal::I64(x) => {
                                let new_ptr = ptr.add_offset(8)?;
                                mem.store(ptr, &x.to_le_bytes());
                                ptr = new_ptr;
                            }
                        }
                        Ok(())
                    })?;
                    Val::Invalid
                }
                super::Tag::String => {
                    let _string = ir.extra[inst.data.extra_len().0 as usize
                        ..(inst.data.extra_len().0 + inst.data.extra_len().1) as usize]
                        .to_vec();
                    eprintln!("TODO: evaluate strings");
                    Val::Tuple(Box::new([Val::Ptr(Ptr { addr: 0, size: 0 }), Val::Int(0)]))
                }
                super::Tag::Call => {
                    let (func_id, args) = inst.data.call(&ir.extra);
                    let args: Vec<_> = args.map(|r| get_ref(&values, r)).collect();
                    let func = env.get_function(func_id);
                    if let Some(func_ir) = &func.ir {
                        // PERF: could copy args directly here without allocating
                        let mut new_values = Values::new(func_ir, &func.types);
                        let entry = BlockIndex::ENTRY;
                        let args_indices = func_ir.get_block_args(entry);
                        for (arg, val) in args_indices.range().zip(args) {
                            new_values.store(arg as _, &val);
                        }
                        if call_stack.len() > STACK_FRAME_COUNT {
                            return Err(Error::StackOverflow);
                        }
                        call_stack.push(StackFrame {
                            function: current_function,
                            pc,
                            sp: mem.sp(),
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
                            .call_extern(func_id, &args, &mut mem)
                            .map_err(Error::ExternCallFailed)?;
                        values.store(pc, &res);
                        pc += 1;
                        continue 'outer;
                    }
                }
                super::Tag::FunctionPtr | super::Tag::CallPtr => todo!("eval function pointers"),
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
                    Val::Int(l.equals(&r) as u64)
                }
                super::Tag::NE => {
                    let l = get_ref(&values, inst.data.bin_op().0);
                    let r = get_ref(&values, inst.data.bin_op().1);
                    Val::Int(!l.equals(&r) as u64)
                }
                super::Tag::LT => cmp_op!(< , inst),
                super::Tag::GT => cmp_op!(> , inst),
                super::Tag::LE => cmp_op!(<=, inst),
                super::Tag::GE => cmp_op!(>=, inst),
                super::Tag::Xor => {
                    let (l, r) = inst.data.bin_op();
                    let (Val::Int(l), Val::Int(r)) = (get_ref(&values, l), get_ref(&values, r))
                    else {
                        panic!("invalid types for xor");
                    };
                    Val::Int(match types[inst.ty] {
                        IrType::I8 | IrType::U8 => ((l as u8) ^ (r as u8)) as u64,
                        IrType::I16 | IrType::U16 => ((l as u16) ^ (r as u16)) as u64,
                        IrType::I32 | IrType::U32 => ((l as u32) ^ (r as u32)) as u64,
                        IrType::I64 | IrType::U64 => l ^ r,
                        _ => panic!("invalid resulting type for xor"),
                    })
                }

                super::Tag::Rol | super::Tag::Ror => {
                    let (Val::Int(l), Val::Int(r)) = (
                        get_ref(&values, inst.data.bin_op().0),
                        get_ref(&values, inst.data.bin_op().1),
                    ) else {
                        panic!("invalid types for rol/ror");
                    };
                    let r = r as u32;
                    let res = if inst.tag == Tag::Rol {
                        match types[inst.ty] {
                            IrType::I8 | IrType::U8 => (l as u8).rotate_left(r) as u64,
                            IrType::I16 | IrType::U16 => (l as u16).rotate_left(r) as u64,
                            IrType::I32 | IrType::U32 => (l as u32).rotate_left(r) as u64,
                            IrType::I64 | IrType::U64 => l.rotate_left(r),
                            _ => panic!("invalid resulting type for rol"),
                        }
                    } else {
                        match types[inst.ty] {
                            IrType::I8 | IrType::U8 => (l as u8).rotate_right(r) as u64,
                            IrType::I16 | IrType::U16 => (l as u16).rotate_right(r) as u64,
                            IrType::I32 | IrType::U32 => (l as u16).rotate_right(r) as u64,
                            IrType::I64 | IrType::U64 => (l as u16).rotate_right(r) as u64,
                            _ => panic!("invalid resulting type for ror"),
                        }
                    };
                    Val::Int(res)
                }
                super::Tag::MemberPtr => {
                    let (ptr, elem_types, i) = inst.data.member_ptr(&ir.extra);
                    let ptr = values.load_ptr(ptr);
                    let offset = crate::offset_in_tuple(elem_types, i, types);
                    Val::Ptr(ptr.add_offset(offset.try_into().unwrap())?)
                }
                super::Tag::MemberValue => {
                    let (tuple, i) = inst.data.ref_int();
                    let Val::Tuple(t) = get_ref(&values, tuple) else {
                        unreachable!()
                    };
                    t[i as usize].clone()
                }
                super::Tag::InsertMember => {
                    let IrType::Tuple(elem_types) = types[inst.ty] else {
                        unreachable!()
                    };
                    let (tuple, i, value) = inst.data.ref_int_ref(&ir.extra);
                    let value = get_ref(&values, value);
                    Val::Tuple(if tuple == Ref::UNDEF {
                        let mut tuple_value: Box<_> =
                            (0..elem_types.count).map(|_| Val::Invalid).collect();
                        tuple_value[i as usize] = value;
                        tuple_value
                    } else {
                        let Val::Tuple(mut t) = get_ref(&values, tuple) else {
                            unreachable!()
                        };
                        t[i as usize] = value;
                        t
                    })
                }
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
                        values.store(i, &get_ref(&values, r));
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
                        values.store(i, &get_ref(&values, r));
                    }
                    pc = target_pos;
                    continue;
                }
                super::Tag::IntToPtr => {
                    let Val::Int(addr) = get_ref(&values, inst.data.un_op()) else {
                        unreachable!()
                    };
                    // TODO: what to do with large addresses?
                    // TODO: what can be done with size
                    Val::Ptr(Ptr {
                        addr: addr.try_into().unwrap(),
                        size: u32::MAX,
                    })
                }
                super::Tag::PtrToInt => {
                    let ptr = values.load_ptr(inst.data.un_op());
                    Val::Int(ptr.addr as u64)
                }
                super::Tag::Asm => todo!(), // TODO: error handling
            };
            //eprintln!("  -> got {value:?}");
            values.store(pc, &value);
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
    sp: u32,
    values: Values,
}

fn decode_block_args(
    ir: &'_ FunctionIr,
    target: BlockIndex,
    extra_idx: usize,
) -> impl ExactSizeIterator<Item = Ref> + use<'_> {
    let block_arg_count = ir.blocks[target.idx() as usize].arg_count;
    let mut bytes = [0; 4];
    (0..block_arg_count).map(move |i| {
        let i = extra_idx + i as usize * 4;
        bytes.copy_from_slice(&ir.extra[i..i + 4]);
        Ref::from_bytes(bytes)
    })
}

struct Values {
    slots: Vec<u64>,
    slot_map: Vec<u32>,
}
impl Values {
    pub fn new(ir: &FunctionIr, types: &IrTypes) -> Self {
        let mut slots = Vec::new();
        let slot_map = ir
            .inst
            .iter()
            .map(|inst| {
                if !inst.ty.is_present() {
                    return u32::MAX;
                }
                let count = slot_count(types[inst.ty], types);
                if count == 0 {
                    return u32::MAX;
                }
                let idx = slots.len() as u32;
                slots.extend(std::iter::repeat(0).take(count as usize));
                idx
            })
            .collect();
        Self { slots, slot_map }
    }

    pub fn visit_primitives(
        &mut self,
        r: Ref,
        ir: &FunctionIr,
        types: &IrTypes,
        mut visit: impl FnMut(PrimitiveVal) -> Result<(), Error>,
    ) -> Result<(), Error> {
        if let Some(val) = r.into_val() {
            match val {
                crate::RefVal::True => visit(PrimitiveVal::I8(1)),
                crate::RefVal::False => visit(PrimitiveVal::I8(0)),
                crate::RefVal::Unit => Ok(()),
                // TODO: might need to do error handling here
                crate::RefVal::Undef => panic!("tried to visit undefined"),
            }
        } else {
            let i = r.into_ref().unwrap();
            let ty = types[ir.inst[i as usize].ty];
            let slot_index = self.slot_map[i as usize];
            self.visit_primitives_inner(&mut { slot_index }, ty, types, &mut { visit })
        }
    }

    fn visit_primitives_inner<F: FnMut(PrimitiveVal) -> Result<(), Error>>(
        &mut self,
        i: &mut u32,
        ty: IrType,
        types: &IrTypes,
        visit: &mut F,
    ) -> Result<(), Error> {
        match ty {
            IrType::Unit => {}
            IrType::I8 | IrType::U8 | IrType::U1 => {
                visit(PrimitiveVal::I8(self.slots[*i as usize] as u8))?;
                *i += 1;
            }
            IrType::I16 | IrType::U16 => {
                visit(PrimitiveVal::I16(self.slots[*i as usize] as u16))?;
                *i += 1;
            }
            IrType::I32 | IrType::U32 | IrType::F32 => {
                visit(PrimitiveVal::I32(self.slots[*i as usize] as u32))?;
                *i += 1;
            }
            IrType::I64 | IrType::U64 | IrType::F64 | IrType::Ptr => {
                visit(PrimitiveVal::I64(self.slots[*i as usize]))?;
                *i += 1;
            }
            IrType::I128 | IrType::U128 => todo!(),
            IrType::Array(elem, len) => {
                for _ in 0..len {
                    self.visit_primitives_inner(i, types[elem], types, visit)?;
                }
            }
            IrType::Tuple(elems) => {
                for elem in elems.iter() {
                    self.visit_primitives_inner(i, types[elem], types, visit)?;
                }
            }
        }
        Ok(())
    }

    pub fn load_primitives(
        &mut self,
        i: u32,
        ty: IrType,
        types: &IrTypes,
        mut visit: impl FnMut(PrimitiveSize, u32) -> Result<u64, Error>,
    ) -> Result<(), Error> {
        let slot_index = self.slot_map[i as usize];
        self.load_primitives_inner(&mut { slot_index }, 0, ty, types, &mut visit)
    }

    pub fn load_primitives_inner(
        &mut self,
        i: &mut u32,
        offset: u32,
        ty: IrType,
        types: &IrTypes,
        visit: &mut impl FnMut(PrimitiveSize, u32) -> Result<u64, Error>,
    ) -> Result<(), Error> {
        match ty {
            IrType::Unit => {}
            IrType::I8 | IrType::U8 | IrType::U1 => {
                self.slots[*i as usize] = visit(PrimitiveSize::S8, offset)?;
                *i += 1;
            }
            IrType::I16 | IrType::U16 => {
                self.slots[*i as usize] = visit(PrimitiveSize::S16, offset.div_ceil(2) * 2)?;
                *i += 1;
            }
            IrType::I32 | IrType::U32 | IrType::F32 => {
                self.slots[*i as usize] = visit(PrimitiveSize::S32, offset.div_ceil(4) * 4)?;
                *i += 1;
            }
            IrType::I64 | IrType::U64 | IrType::F64 | IrType::Ptr => {
                self.slots[*i as usize] = visit(PrimitiveSize::S64, offset.div_ceil(8) * 8)?;
                *i += 1;
            }
            IrType::I128 | IrType::U128 => todo!(),
            IrType::Array(elem, len) => {
                let elem_layout = types.layout(types[elem]);
                if elem_layout.size == 0 {
                    return Ok(());
                }
                let align: u32 = elem_layout
                    .align
                    .get()
                    .try_into()
                    .map_err(|_| Error::OutOfMemory)?;
                let stride: u32 = elem_layout
                    .stride()
                    .try_into()
                    .map_err(|_| Error::OutOfMemory)?;
                let offset = offset.div_ceil(align) * align;
                for elem_idx in 0..len {
                    self.load_primitives_inner(
                        i,
                        offset + elem_idx * stride,
                        types[elem],
                        types,
                        visit,
                    )?;
                }
            }
            IrType::Tuple(elems) => {
                let layout = types.layout(IrType::Tuple(elems));
                let align: u32 = layout
                    .align
                    .get()
                    .try_into()
                    .map_err(|_| Error::OutOfMemory)?;
                let offset = offset.div_ceil(align) * align;
                let mut layout = Layout::EMPTY;
                for elem in elems.iter() {
                    let elem_layout = types.layout(types[elem]);
                    layout.align_for(elem_layout.align);
                    let tuple_offset: u32 = layout.size.try_into().unwrap();
                    self.load_primitives_inner(
                        i,
                        offset + tuple_offset,
                        types[elem],
                        types,
                        visit,
                    )?;
                    layout.accumulate(types.layout(types[elem]));
                }
            }
        }
        Ok(())
    }

    pub fn store(&mut self, i: u32, val: &Val) {
        let i = self.slot_map[i as usize];
        self.store_inner(&mut { i }, val);
    }

    pub fn load(&self, i: u32, ty: IrType, types: &IrTypes) -> Val {
        let i = self.slot_map[i as usize];
        self.load_inner(&mut { i }, ty, types)
    }

    pub fn load_ptr(&mut self, r: Ref) -> Ptr {
        Ptr::from_u64(self.slots[self.slot_map[r.into_ref().unwrap() as usize] as usize])
    }

    fn store_inner(&mut self, i: &mut u32, val: &Val) {
        match val {
            Val::Invalid | Val::Unit => {}
            &Val::Int(n) => {
                self.slots[*i as usize] = n;
                *i += 1;
            }
            &Val::F32(n) => {
                self.slots[*i as usize] = n.to_bits() as u64;
                *i += 1;
            }
            &Val::F64(n) => {
                self.slots[*i as usize] = n.to_bits();
                *i += 1;
            }
            &Val::Ptr(ptr) => {
                self.slots[*i as usize] = ptr.into_u64();
                *i += 1;
            }
            Val::Array(elems) | Val::Tuple(elems) => {
                for elem in elems {
                    self.store_inner(i, elem);
                }
            }
        }
    }

    fn load_inner(&self, i: &mut u32, ty: IrType, types: &IrTypes) -> Val {
        match ty {
            IrType::Unit => Val::Unit,
            IrType::U1
            | IrType::I8
            | IrType::I16
            | IrType::I32
            | IrType::I64
            | IrType::U8
            | IrType::U16
            | IrType::U32
            | IrType::U64 => {
                let val = Val::Int(self.slots[*i as usize]);
                *i += 1;
                val
            }
            IrType::I128 | IrType::U128 => todo!(),
            IrType::F32 => {
                let val = Val::F32(f32::from_bits(self.slots[*i as usize] as u32));
                *i += 1;
                val
            }
            IrType::F64 => {
                let val = Val::F64(f64::from_bits(self.slots[*i as usize]));
                *i += 1;
                val
            }
            IrType::Ptr => {
                let x = self.slots[*i as usize];
                *i += 1;
                Val::Ptr(Ptr::from_u64(x))
            }
            IrType::Array(elem, len) => Val::Array(
                (0..len)
                    .map(|_| self.load_inner(i, types[elem], types))
                    .collect(),
            ),
            IrType::Tuple(elems) => Val::Tuple(
                elems
                    .iter()
                    .map(|elem| self.load_inner(i, types[elem], types))
                    .collect(),
            ),
        }
    }
}

fn slot_count(ty: IrType, types: &IrTypes) -> u32 {
    match ty {
        IrType::Unit => 0,
        IrType::Array(type_ref, count) => slot_count(types[type_ref], types) * count,
        IrType::Tuple(type_refs) => type_refs
            .iter()
            .map(|ty| slot_count(types[ty], types))
            .sum(),
        _ => 1,
    }
}

#[derive(Debug)]
enum PrimitiveVal {
    I8(u8),
    I16(u16),
    I32(u32),
    I64(u64),
}

#[derive(Debug)]
enum PrimitiveSize {
    S8,
    S16,
    S32,
    S64,
}
