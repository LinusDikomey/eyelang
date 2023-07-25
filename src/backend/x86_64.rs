use std::{alloc::Layout, fmt};

use crate::{backend::{ArgType, Arg}, ir};

use super::{MachineCode, VirtualRegister};



#[allow(non_camel_case_types)]
pub enum Register {
    eax,
}
impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Register::*;
        let s = match self {
            eax => "eax",
        };
        write!(f, "{s}")
    }
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
        impl super::Inst for Inst {
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

pub fn generate(module: &ir::Module) {
    for func in &module.funcs {
        let code = generate_func(func);
        if let Some(code) = code {
            println!("Machine code for function {}:\n{}\n\n", func.name, code);
        }
    }
}

struct RegisterMapper {
    instructions: Box<[VirtualRegister]>,
    next: VirtualRegister,
}
impl RegisterMapper {
    pub fn new(size: usize) -> Self {
        Self {
            instructions: unsafe {
                let ptr = std::alloc::alloc_zeroed(Layout::array::<VirtualRegister>(size).unwrap())
                    as *mut VirtualRegister;
                Box::from_raw(core::ptr::slice_from_raw_parts_mut(ptr, size))
            },
            next: VirtualRegister(1),
        }
    }

    pub fn get(&mut self, ir_register: u32) -> VirtualRegister {
        if self.instructions[ir_register as usize].0 == 0 {
            self.instructions[ir_register as usize] = self.next;
            self.next.0 += 1;
        }
        self.instructions[ir_register as usize]
    }

    pub fn mark(&mut self, ir_register: u32, mapped: VirtualRegister) {
        self.instructions[ir_register as usize] = mapped
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

fn generate_inst(res: u32, code: &mut MachineCode<Inst>, mapper: &mut RegisterMapper, inst: &ir::Instruction, extra: &[u8]) {
    use ir::Tag;
    match inst.tag {
        Tag::BlockBegin => {
            let block = unsafe { inst.data.block };
            code.label(block);
        }
        Tag::Int => {
            let res = mapper.get(res);
            let int = unsafe { inst.data.int };
            code.inst(Inst::mov, [Arg::Virtual(res), Arg::Imm(int)])
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
            mapper.mark(res, l);

            code.inst(op, [Arg::Virtual(l), Arg::Virtual(r)]);
        }
        Tag::Ret => {
            let value = unsafe { inst.data.un_op };
            if let Some(val) = value.into_val() {
                match val {
                    ir::RefVal::True | ir::RefVal::False => {
                        let val = if val == ir::RefVal::True { 1 } else { 0 };
                        code.inst(Inst::mov, [Arg::Physical(Register::eax), Arg::Imm(val)]);
                    }
                    ir::RefVal::Unit | ir::RefVal::Undef => {}
                }
            } else {
                let reg = mapper.get(value.into_ref().unwrap());
                code.inst(Inst::mov, [Arg::Physical(Register::eax), Arg::Virtual(reg)]);
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
                code.inst(Inst::cmp, [Arg::Virtual(r)]);
                code.inst(Inst::jz, [Arg::Label(on_false)]);
                code.inst(Inst::jnz, [Arg::Label(on_true)]);
            };
        }
        Tag::Call => {} // TODO
        other => todo!("unimplemented instruction in x86_64 backend: {other:?}"),
    }
}
