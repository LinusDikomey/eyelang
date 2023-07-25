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

#[allow(non_camel_case_types)]
pub enum Inst {
    ret,
    mov,
    add,
    sub,
    mul,
}
impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Inst::*;
        let s = match self {
            ret => "ret",
            mov => "mov",
            add => "add",
            sub => "sub",
            mul => "mul",
        };

        write!(f, "{s}")
    }
}


impl super::Inst for Inst {
    type Register = Register;

    fn arg_types(&self) -> &'static [ArgType] {
        use Inst::*;
        use ArgType::*;

        match self {
            ret => &[],
            mov => &[Def, Use],
            add | sub | mul => &[UseDef, Use],
        }
    }
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
        generate_inst(i as u32, &mut code, &mut mapper, inst);
    }
    Some(code)
}

fn generate_inst(res: u32, code: &mut MachineCode<Inst>, mapper: &mut RegisterMapper, inst: &ir::Instruction) {
    use ir::Tag;
    match inst.tag {
        Tag::BlockBegin => {}
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
        Tag::Ret => code.inst(Inst::ret, []),
        other => todo!("unimplemented instruction in x86_64 backend: {other:?}"),
    }
}
