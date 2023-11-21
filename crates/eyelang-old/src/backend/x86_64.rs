use std::{fmt, path::Path, process::Command, fs::File};
use crate::{ir, RunResult};

use super::machine_code::{Arg, ArgType, MachineCode, VirtualRegister, Instruction, Inst as _};


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
    call Label,
}

const PARAM_REGISTERS: [Register; 6] = [
    Register::rdi,
    Register::rsi,
    Register::rdx,
    Register::rcx,
    Register::r8,
    Register::r9,
];

struct MachineIR<'a> {
    extern_functions: Vec<&'a str>,
    functions: Vec<(&'a str, MachineCode<Inst>)>,
}
impl<'a> MachineIR<'a> {
    fn emit_assembly<W: std::io::Write>(&self, w: &mut W, module: &ir::Module) -> std::io::Result<()> {
        writeln!(w, "global main\n")?;
        writeln!(w, "section .data\n")?;
        for name in &self.extern_functions {
            writeln!(w, "extern {}", name)?;
        }
        for (function_index, (name, code)) in self.functions.iter().enumerate() {
            writeln!(w, "{}:", name)?;

            for inst in &code.instructions {
                match *inst {
                    Instruction::Label(idx) => writeln!(w, "_f{function_index}_b{}:", idx.idx())?,
                    Instruction::Specific { instruction, arguments_index } => {
                        let arg_count = instruction.arg_types().len();
                        let args = &code.arguments[arguments_index as usize .. arguments_index as usize + arg_count];
                        emit_instruction(w, instruction, args, function_index, module)?;
                    }
                }
            }
        }

        Ok(())
    }
}

fn emit_instruction<W: std::io::Write>(
    w: &mut W,
    inst: Inst,
    args: &[Arg<Register>],
    function_index: usize,
    module: &ir::Module,
) -> std::io::Result<()> {
    write!(w, "    {}", inst)?;
    let mut first = true;
    for arg in args {
        if first {
            write!(w, " ")?;
            first = false;
        } else {
            write!(w, ", ")?;
        }
        match arg {
            Arg::Label(idx) => write!(w, "_f{function_index}_b{}", idx.idx())?,
            Arg::FunctionLabel(id) => write!(w, "{}", module.funcs[id.idx()].name)?,
            Arg::Virtual(_virt) => {
                eprintln!("virtual register encountered during machine code emit");
                write!(w, "{}", 0)?;
            }
            Arg::Physical(phys) => write!(w, "{phys}")?,
            Arg::Imm(value) => write!(w, "{value}")?,
        }
    }
    writeln!(w)
}

pub fn generate(module: &ir::Module, asm_file_path: impl AsRef<Path>, obj_file: impl AsRef<Path>) -> RunResult {
    let mut machine_ir = MachineIR {
        extern_functions: vec![],
        functions: vec![],
    };

    for func in &module.funcs {
        let name = &func.name;
        if let Some(ir) = &func.ir {
            let code = generate_func(ir);
            machine_ir.functions.push((name, code));
        } else {
            machine_ir.extern_functions.push(name);
        };
    }

    let asm_file_path = asm_file_path.as_ref();
    let mut asm_file = File::create(asm_file_path).map_err(|_| "Failed to create assembly file")?;
    machine_ir.emit_assembly(&mut asm_file, module).map_err(|_| "Failed to write to assembly file")?;
    assemble(asm_file_path, obj_file.as_ref())
}

fn assemble(asm: &Path, output: &Path) -> RunResult {
    let status = Command::new("nasm")
        .arg("-f")
        .arg("elf64")
        .arg(asm)
        .arg("-o")
        .arg(output)
        .status()
        .map_err(|_| "Failed to invoke assembler")?;

    status.success().then_some(()).ok_or("Assembler failed")
}


struct RegisterMapper {
    ir_values: Box<[Arg<Register>]>,
    next: VirtualRegister,
}
impl RegisterMapper {
    pub fn new(size: usize) -> Self {
        Self {
            // PERF: can this cause 2 allocs if the vec overallocates?
            // Can be allocated manually but 
            ir_values: vec![Arg::Virtual(VirtualRegister::UNASSIGNED); size].into_boxed_slice(),
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

fn generate_func(ir: &ir::FunctionIr) -> MachineCode<Inst> {
    let mut code = MachineCode::new();
    let mut mapper = RegisterMapper::new(ir.inst.len());

    for (i, inst) in ir.inst.iter().enumerate() {
        generate_inst(i as u32, &mut code, &mut mapper, inst, &ir.extra);
    }
    code
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
        Tag::Call => {
            // TODO: call arguments
            let start = unsafe { inst.data.extra_len.0 as usize };
            let mut bytes = [0; 8];
            bytes.copy_from_slice(&extra[start..start+8]);
            let func = ir::FunctionId::from_bytes(bytes);
            /*
            let refs = (0..inst.data.extra_len.1).map(|i| {
                let mut ref_bytes = [0; 4];
                let begin = 8 + start + (4 * i) as usize;
                ref_bytes.copy_from_slice(&extra[begin..begin+4]);
                ir::Ref::from_bytes(ref_bytes)
            });
            */
            code.inst(Inst::call, [Arg::FunctionLabel(func)])
        }
        other => todo!("unimplemented instruction in x86_64 backend: {other:?}"),
    }
}
