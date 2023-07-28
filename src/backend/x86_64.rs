use std::{alloc::Layout, fmt, mem::MaybeUninit};
use crate::ir;

use super::machine_code::{Arg, ArgType, MachineCode, VirtualRegister};


macro_rules! register {
    ($($reg: ident)*) => {
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, Debug)]
        pub enum Register {
            $( $reg ),*
        }
        impl fmt::Display for Register {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let name = match *self {
                    $( Self::$reg => stringify!($reg)),*
                };
                write!(f, "{name}")
            }
        }
    }
}

register! {
    rax rdi rsi rdx rcx r8 r9
}

macro_rules! inst {
    ($($name: ident $($arg: ident)* ,)*) => {
        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Inst {
            $($name),*
        }
        impl fmt::Display for Inst {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let s = match *self {
                    $( Self::$name => stringify!($name) ),*
                };
                write!(f, "{s}")
            }
        }
        impl super::machine_code::Inst for Inst {
            type Register = Register;

            fn arg_types(&self) -> &'static [ArgType] {
                match *self {
                    $( Self::$name => &[$( ArgType::$arg ),*]),*
                }
            }
        }
    };
}

inst! {
    ret,
    mov Def Use,
    add UseDef Use,
    sub UseDef Use,
    mul UseDef Use,
    jmp Label,
    jz,
    jnz,
    cmp Use,
}

const PARAM_REGISTERS: [Register; 6] = [
    Register::rdi,
    Register::rsi,
    Register::rdx,
    Register::rcx,
    Register::r8,
    Register::r9,
];

pub fn generate(module: &ir::Module) {
    for func in &module.funcs {
        let code = generate_func(func);
        if let Some(code) = code {
            println!("Machine code for function {}:\n{}\n\n", func.name, code);
        }
    }
}

struct RegisterMapper {
    ir_values: Box<[Arg<Register>]>,
    next: VirtualRegister,
}
impl RegisterMapper {
    pub fn new(size: usize) -> Self {
        Self {
            ir_values: if size == 0 {
                Box::new([])
            } else {
                unsafe {
                    let ptr = std::alloc::alloc(Layout::array::<VirtualRegister>(size).unwrap())
                        as *mut MaybeUninit<Arg<Register>>;
                    let mut slice = Box::from_raw(core::ptr::slice_from_raw_parts_mut(ptr, size));
                    slice.fill(MaybeUninit::new(Arg::Virtual(VirtualRegister::UNASSIGNED)));
                    std::mem::transmute(slice)
                }
            },
            next: VirtualRegister::FIRST,
        }
    }

    pub fn get(&mut self, ir_register: u32) -> Arg<Register> {
        if matches!(self.ir_values[ir_register as usize], Arg::Virtual(VirtualRegister::UNASSIGNED)) {
            self.ir_values[ir_register as usize] = Arg::Virtual(self.next);
            self.next = self.next.next();
        }
        self.ir_values[ir_register as usize]
    }

    pub fn mark(&mut self, ir_register: u32, mapped: Arg<Register>) {
        self.ir_values[ir_register as usize] = mapped
    }
}

fn generate_func(func: &ir::Function) -> Option<MachineCode<Inst>> {
    let Some(ir) = &func.ir else { return None };

    let mut code = MachineCode::new();
    let mut mapper = RegisterMapper::new(ir.inst.len());

    for (i, inst) in ir.inst.iter().enumerate() {
        generate_inst(i as u32, &mut code, &mut mapper, inst, &ir.extra);
    }
    Some(code)
}

fn generate_inst(
    res: u32,
    code: &mut MachineCode<Inst>,
    mapper: &mut RegisterMapper,
    inst: &ir::Instruction,
    extra: &[u8],
) {
    use ir::Tag;
    match inst.tag {
        Tag::BlockBegin => {
            let block = unsafe { inst.data.block };
            code.label(block);
        }
        Tag::Param => {
            let i = unsafe { inst.data.int32 };
            assert!(i < 6, "more than 6 parameters aren't supported right now");
            mapper.mark(res, Arg::Physical(PARAM_REGISTERS[i as usize]));
        }
        Tag::Int => {
            let int = unsafe { inst.data.int };
            mapper.mark(res, Arg::Imm(int));
        }
        Tag::Add | Tag::Sub | Tag::Mul => {
            let op = match inst.tag {
                Tag::Add => Inst::add,
                Tag::Sub => Inst::sub,
                Tag::Mul => Inst::mul,
                _ => unreachable!(),
            };
            let (l, r) = unsafe { inst.data.bin_op };
            // no integer ref values for now so unwrapping is fine here
            let (l, r) = (l.into_ref().unwrap(), r.into_ref().unwrap());

            let l = mapper.get(l);
            let r = mapper.get(r);
            if let (Arg::Imm(l), Arg::Imm(r)) = (l, r) {
                // TODO: handle overflow here
                let value = match inst.tag {
                    Tag::Add => l.wrapping_add(r),
                    Tag::Sub => l.wrapping_sub(r),
                    Tag::Mul => l.wrapping_mul(r),
                    _ => unreachable!()
                };
                mapper.mark(res, Arg::Imm(value))
            } else {
                mapper.mark(res, l);
                code.inst(op, [l, r]);
            }
        }
        Tag::Ret => {
            let value = unsafe { inst.data.un_op };
            if let Some(val) = value.into_val() {
                match val {
                    ir::RefVal::True | ir::RefVal::False => {
                        let val = if val == ir::RefVal::True { 1 } else { 0 };
                        code.inst(Inst::mov, [Arg::Physical(Register::rax), Arg::Imm(val)]);
                    }
                    ir::RefVal::Unit | ir::RefVal::Undef => {}
                }
            } else {
                let reg = mapper.get(value.into_ref().unwrap());
                code.inst(Inst::mov, [Arg::Physical(Register::rax), reg]);
            }
            code.inst(Inst::ret, []);
        }
        Tag::Goto => {
            code.inst(Inst::jmp, [Arg::Label(unsafe { inst.data.block })]);
        }
        Tag::Branch => {
            let (val, i) = unsafe { inst.data.ref_int };
            let i = i as usize;
            let mut bytes = [0; 4];
            bytes.copy_from_slice(&extra[i..i+4]);
            let on_true = ir::BlockIndex::from_bytes(bytes);
            bytes.copy_from_slice(&extra[i+4..i+8]);
            let on_false = ir::BlockIndex::from_bytes(bytes);

            if let Some(val) = val.into_val() {
                match val {
                    ir::RefVal::True => code.inst(Inst::jmp, [Arg::Label(on_true)]),
                    ir::RefVal::False => code.inst(Inst::jmp, [Arg::Label(on_false)]),
                    _ => panic!("invalid ir"),
                }
            } else {
                let r = mapper.get(val.into_ref().unwrap());
                code.inst(Inst::cmp, [r]);
                code.inst(Inst::jz, [Arg::Label(on_false)]);
                code.inst(Inst::jnz, [Arg::Label(on_true)]);
            };
        }
        Tag::Call => {} // TODO
        other => todo!("unimplemented instruction in x86_64 backend: {other:?}"),
    }
}
