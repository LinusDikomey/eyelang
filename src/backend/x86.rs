use std::{fs::File, io::{BufWriter, Write}, fmt, process::Command, path::Path};
use std::fmt::Write as _;

use crate::{ir::{self, Instruction, Tag, SymbolKey, Ref, BaseType}, types::Primitive};

#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
enum Inst<'a> {
    mov(Val, Val),
    push(Val),
    pop(Val),
    call(&'a str),
    ret,
    not(Val),
    add(Val, Val),
    sub(Val, Val),
    imul(Val, Val),
    idiv(Val),
    xor(Val, Val),
    and(Val, Val)
}
use Inst::*;

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Val {
    NoVal,
    Int(Type, u64),
    NegInt(Type, u64),
    Stack { offset: u32, size: u32 },
    Data(u32),

    // parameter registers
    rdi, // edi, di, dil,
    rsi, // esi, si, sil,
    rdx, // edx, dx, dl,
    rcx, // ecx, cx, cl,
    r8,  //r8d, r8w, r8b,
    r9,  //r9d, r9w, r9b,

    rsp,
    rbp,
    rax,
    al,
}
impl Val {
    /*
    #[must_use = "returns the new Val"]
    fn ty(self, ty: Type) -> Self {
        match self {
            Stack { offset, size } => TStack(ty, v),
            Int(i) => TInt(ty, i),
            NegInt(i) => TNegInt(ty, i),
            other => other
        }
    }*/

    fn size(self) -> u32 {
        match self {
            NoVal => 0,
            Int(ty, _) | NegInt(ty, _) => ty.size(),
            Stack { offset: _, size } => size,
            Data(_) => 8,
            rsp | rbp | rax | rdi | rsi | rdx | rcx | r8 | r9 => 8,
            //edi | esi | edx | ecx | r8d | r9d => 4,
            //di | si | dx | cx | r8w | r9w => 2,
            //dil | sil | dl | cl | r8b | r9b => 1,
            al => 1,
        }
    }
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Type {
    byte,
    word,
    dword,
    qword,
    oword,
}
impl Type {
    fn from_size(size: u32) -> Option<Self> {
        Some(match size {
            1 => Self::byte,
            2 => Self::word,
            4 => Self::dword,
            8 => Self::qword,
            16 => Self::oword,
            _ => return None
        })
    }
    fn size(self) -> u32 {
        match self {
            Self::byte => 1,
            Self::word => 2,
            Self::dword => 4,
            Self::qword => 8,
            Self::oword => 16,
        }
    }
}
impl TryFrom<Primitive> for Type {
    type Error = ();

    fn try_from(p: Primitive) -> Result<Self, ()> {
        use Primitive::*;
        Ok(match p {
            Unit | Never => return Err(()),
            I8 | U8 | Bool => Self::byte,
            I16 | U16 => Self::word,
            I32 | U32 | F32 => Self::dword,
            I64 | U64 | F64 => Self::qword,
            I128 | U128 => Self::oword,
        })
    }
}
impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", match self {
            Type::byte => "byte",
            Type::word => "word",
            Type::dword => "dword",
            Type::qword => "qword",
            Type::oword => "oword",
        })
    }
}

use Val::*;

impl Val {
    fn is_reg(&self) -> bool {
        !matches!(self, NoVal | Int(_, _) | NegInt(_, _) | Stack { .. } | Data(_))
    }
    /// moves this value into the specified register if it isn't already in any register
    #[must_use = "Returns the existing or new register"]
    fn ensure_reg(self, w: &mut AsmWriter, reg: Val) -> Self {
        if self.is_reg() { self } else {
            w.inst(mov(reg, self));
            reg
        }
    }
    #[must_use = "Returns the existing register or rax"]
    fn ensure_rax(self, w: &mut AsmWriter) -> Self { self.ensure_reg(w, rax) }

    fn move_into(self, w: &mut AsmWriter, reg: Val) {
        if self != reg {
            w.inst(mov(reg, self));
        }
    }
}
impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            NoVal => panic!("Tried to write NoVal. Did the x86 backend try to use the result of a label/return?"),
            //Int(i) => return write!(f, "{i}"),
            Int(ty, i) => return write!(f, "{ty} {i}"),
            //NegInt(i) => return write!(f, "-{i}"),
            NegInt(ty, i) => return write!(f, "{ty} -{i}"),
            Stack { offset, size } => {
                return if let Some(ty) = Type::from_size(*size) {
                    write!(f, "{ty} [rbp - {offset}]")
                } else {
                    write!(f, "[rbp - {offset}]")
                }
            }
            //TStack(ty, offset) => return write!(f, "{ty} [rbp - {offset}]"),
            Data(index) => return write!(f, "QWORD data{index}"),
            rdi => "rdi", // edi => "edi", di => "di", dil => "dil",
            rsi => "rsi", // esi => "esi", si => "si", sil => "sil",
            rdx => "rdx", // edx => "ex", dx => "dx", dl => "dl",
            rcx => "rcx", // ecx => "ecx", cx => "cy", cl => "cl",
            r8 => "r8",   // r8d => "r8d", r8w => "r8w", r8b => "r8b",
            r9 => "r9",   // r9d => "r9d", r9w => "r9w", r9b => "r9b",

            rsp => "rsp",
            rbp => "rbp",
            rax => "rax",
            al => "al",
        };

        write!(f, "{s}")
    }
}

const FILE_START: &[u8] = 
b"\
; --------------------------------------------------------------
; This file was automatically generated by the Eyelang Compiler.
; --------------------------------------------------------------

";

fn name_modifier(name: &str) -> std::borrow::Cow<'_, str> {
    name.into()
}

struct AsmWriter {
    w: BufWriter<File>,
    content: String,
    data: Vec<u8>,
    data_index: u32
}

impl AsmWriter {
    fn new(file: File) -> Self {
        let mut w = BufWriter::new(file);
        w.write_all(FILE_START).unwrap();
        Self {
            w,
            content: String::new(),
            data: Vec::new(),
            data_index: 0,
        }
    }

    fn add_extern(&mut self, name: &str) {
        writeln!(self.w, "extern {}", name_modifier(name)).unwrap();
    }

    fn begin_func(&mut self, name: &str) {
        writeln!(self.content, "{}:", name_modifier(name)).unwrap();
    }

    fn label(&mut self, func: u32, block: u32) {
        writeln!(self.content, "label{func}_{block}:").unwrap();
    }

    fn inst(&mut self, inst: Inst) {
        use Inst::*;
        write!(self.content, "\t").unwrap();
        let mut w = |inst: &str, args: &[Val]| {
            write!(self.content, "{inst}").unwrap();
            if !args.is_empty() { write!(self.content, " ").unwrap(); }
            for (i, arg) in args.iter().enumerate() {
                if i != 0 {
                    write!(self.content, ", ").unwrap();
                }
                write!(self.content, "{arg}").unwrap();
            }
        };
        match inst {
            mov(a, b) => w("mov", &[a, b]),
            push(r) => w("push", &[r]),
            pop(r) => w("pop", &[r]),
            ret => w("ret", &[]),
            call(name) => write!(self.content, "call {name}").unwrap(),
            not(v) => w("not", &[v]),
            add(r, v) => w("add", &[r, v]),
            sub(r, v) => w("sub", &[r, v]),
            imul(r, v) => w("imul", &[r, v]),
            idiv(r) => w("idiv", &[r]),
            xor(r, v) => w("xor", &[r, v]),
            and(r, v) => w("and", &[r, v]),
        }
        writeln!(self.content).unwrap();
    }

    fn data(&mut self, data: &[u8]) -> u32 {
        self.data.extend(format!("data{}: db ", self.data_index).as_bytes());
        for b in data {
            write!(self.data, "{}", b).unwrap();
            write!(self.data, ", ").unwrap();
        }
        writeln!(self.data, "0").unwrap();
        self.data_index += 1;
        self.data_index - 1
    }
}

impl Drop for AsmWriter {
    fn drop(&mut self) {
        writeln!(self.w, "global {}", name_modifier("main")).unwrap();
        writeln!(self.w, "section   .text").unwrap();
        write!(self.w, "{}", self.content).unwrap();
        writeln!(self.w, "\nsection .data").unwrap();
        self.w.write_all(&self.data).unwrap();
    }
}

pub unsafe fn emit(module: &ir::Module, file: File) {
    let mut w = AsmWriter::new(file);

    for (index, func) in module.funcs.iter().enumerate() {
        gen_func(index as u32, func, &module.funcs, &mut w);
    }
}

pub fn assemble(asm: &Path, output: &Path) -> bool {
    let status = Command::new("nasm")
        .arg("-f")
        .arg("elf64")
        .arg(asm)
        .arg("-o")
        .arg(output)
        .status()
        .expect("Failed to invoke assembler");
    status.success()
}

const CALL_REGS: [Val; 6] = [rdi, rsi, rdx, rcx, r8, r9];

const CALL_STACK_ALIGNMENT: u32 = 16;

unsafe fn gen_func(index: u32, func: &ir::FinalFunction, funcs: &[ir::FinalFunction], w: &mut AsmWriter) {
    if let Some(ir) = &func.ir {
        w.begin_func(&func.name);
        w.inst(push(rbp));
        w.inst(mov(rbp, rsp));
        let mut r = Vec::with_capacity(ir.inst.len());
        
        let mut stack_pos: u32 = 0;
        
        let get_ref = |r: Ref, refs: &[Val]| {
            if let Some(v) = r.into_val() {
                match v {
                    ir::RefVal::True => Int(Type::byte, 1),
                    ir::RefVal::False => Int(Type::byte, 0),
                    ir::RefVal::Unit | ir::RefVal::Undef => NoVal,
                }
            } else {
                let r = r.into_ref().unwrap();
                refs[r as usize]
            }
        };

        for inst in &ir.inst {
            let Instruction { data, tag, ty: _, used: _ } = inst;
            let val = match *tag {
                Tag::BlockBegin => {
                    w.label(index, data.int32);
                    NoVal
                }
                Tag::Ret => {
                    let val = get_ref(data.un_op, &r);
                    if val != rax && val != NoVal {
                        w.inst(mov(rax, val));
                    }
                    w.inst(mov(rsp, rbp));
                    w.inst(pop(rbp));
                    w.inst(ret);
                    NoVal
                }
                Tag::Param => {
                    let idx = data.int32;
                    assert!(idx < 6, "More than 6 parameters not supported");
                    CALL_REGS[idx as usize]
                }
                Tag::Int => {
                    match ir.types[inst.ty] {
                        ir::Type::Base(BaseType::Prim(p)) => {
                            let ty = Type::try_from(p)
                                .expect("Unsupported int size");
                            Int(ty, data.int)
                        }
                        other => panic!("Invalid type for const int: {other}"),
                    }

                }
                Tag::LargeInt => todo!(),
                Tag::Float => todo!(),
                Tag::Decl => {
                    let size = match ir.types[inst.ty] {
                        ir::Type::Base(BaseType::Prim(p)) => p.size(),
                        ir::Type::Base(BaseType::Id(_)) => panic!("Non-primitives not supported in x86 backend"),
                        ir::Type::Pointer {.. } => 8,
                    };
                    stack_pos += size;
                    w.inst(sub(rsp, Int(Type::qword, size as u64)));
                    r.push(Stack { offset: stack_pos, size });
                    continue // value is already on the stack
                }
                Tag::Load => get_ref(data.un_op, &r),
                Tag::Store => {
                    let into = get_ref(data.bin_op.0, &r);
                    let val = get_ref(data.bin_op.1, &r);
                    let from = if matches!(into, Stack {..}) && matches!(val, Stack {..}) {
                        w.inst(mov(rax, val));
                        rax
                    } else {
                        val
                    };
                    w.inst(mov(into, from));
                    NoVal
                }
                Tag::String => {
                    let bytes = &ir.extra[
                        inst.data.extra_len.0 as usize
                        .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                    ];
                    Data(w.data(bytes))
                }
                Tag::Call => {
                    let start = data.extra_len.0 as usize;
                    let mut bytes = [0; 8];
                    bytes.copy_from_slice(&ir.extra[start..start+8]);
                    let func = SymbolKey::from_bytes(bytes);
                    let refs = (0..data.extra_len.1).map(|i| {
                        let mut ref_bytes = [0; 4];
                        let begin = 8 + start + (4 * i) as usize;
                        ref_bytes.copy_from_slice(&ir.extra[begin..begin+4]);
                        Ref::from_bytes(ref_bytes)
                    });
                    let func = &funcs[func.idx()];
                    let call_name = &func.name;
                    let arg_count = refs.len();
                    assert!(arg_count <= 6, "More than 6 arguments not supported right now");
                    for (ref_val, reg) in refs.take(6).zip(CALL_REGS) {
                        let val = get_ref(ref_val, &r);
                        val.move_into(w, reg);
                    }
                    if func.varargs {
                        let vararg_count = arg_count - func.params.len();
                        w.inst(mov(al, Int(Type::byte, vararg_count as u64)));
                    }
                    // align the stack to the required alignment before calling
                    let missing_alignment = (
                        (CALL_STACK_ALIGNMENT - (stack_pos % CALL_STACK_ALIGNMENT)) % CALL_STACK_ALIGNMENT
                    ) as u64;
                    dbg!(stack_pos, missing_alignment);
                    w.inst(sub(rsp, Int(Type::qword, missing_alignment)));
                    w.inst(call(&name_modifier(call_name)));
                    // move back the stack pointer
                    w.inst(add(rsp, Int(Type::qword, missing_alignment)));
                    rax
                }
                Tag::Neg => {
                    let r = get_ref(data.un_op, &r).ensure_rax(w);
                    w.inst(not(r));
                    w.inst(add(r, Int(Type::qword, 1)));
                    r
                }
                Tag::Not => {
                    let r = get_ref(data.un_op, &r).ensure_reg(w, al);
                    w.inst(xor(al, NegInt(Type::byte, 1)));
                    w.inst(and(al, Int(Type::byte, 1)));
                    r
                }
                Tag::Add | Tag::Sub | Tag::Mul | Tag::Div => {
                    let left = get_ref(data.bin_op.0, &r).ensure_rax(w);
                    stack_pos += 8;
                    w.inst(push(left));
                    let mut right = get_ref(data.bin_op.1, &r);
                    if right == rax {
                        // move into rdx because rax will be occupied by the left side
                        w.inst(mov(rdx, right));
                        right = rdx;
                    }
                    w.inst(pop(left));
                    match inst.tag {
                        Tag::Add => { w.inst(add(left, right)); left },
                        Tag::Sub => { w.inst(sub(left, right)); left },
                        Tag::Mul => { w.inst(imul(left, right)); left },
                        Tag::Div => {
                            left.move_into(w, rax);
                            w.inst(idiv(right/*.ty(Type::qword)*/));
                            rax
                        }
                        _ => unreachable!()
                    }
                }
                Tag::Mod => todo!(),
                Tag::Or => todo!(),
                Tag::And => todo!(),
                Tag::Eq => todo!(),
                Tag::Ne => todo!(),
                Tag::LT => todo!(),
                Tag::GT => todo!(),
                Tag::LE => todo!(),
                Tag::GE => todo!(),
                Tag::Member => todo!(),
                Tag::Cast => todo!(),
                Tag::AsPointer => todo!(),
                Tag::Goto => todo!(),
                Tag::Branch => todo!(),
                Tag::Phi => todo!(),
                
            };
            if inst.used && val != NoVal {
                if val.is_reg() {
                    stack_pos += 8;
                    w.inst(push(val));
                    r.push(Stack { offset: stack_pos, size: val.size() });
                } else {
                    r.push(val);
                }
                
            } else {
                r.push(NoVal)
            }
        }
    } else {
        w.add_extern(&func.name);
    }
}