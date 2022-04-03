use std::{fs::File, io::{BufWriter, Write}, fmt};

use crate::ir::{self, Instruction, Tag};

#[allow(non_camel_case_types)]
enum Inst {
    mov(Val, Val),
    push(Val),
    pop(Val),
    ret,
}

#[allow(non_camel_case_types)]
#[derive(Clone, Copy, Debug)]
enum Val {
    NoVal,
    Int(u64),
    Stack(u32),
    Data(u32),
    eax,
    rbp,
}
use Inst::*;
use Val::*;

impl fmt::Display for Val {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let s = match self {
            NoVal => panic!("Tried to write NoVal. Did the x86 backend try to use the result of a label/return?"),
            Int(i) => return write!(f, "{i}"),
            Stack(offset) => return write!(f, "dword ptr [rbp - {offset}]"),
            Data(index) => return write!(f, "data{index}"),
            eax => "eax",
            rbp => "rbp",
        };

        write!(f, "{s}")
    }
}

const FILE_START: &[u8] = 
b"; ----------------------------------------------------------------------------------------
; This file was automatically generated by the Eyelang Compiler.
; ----------------------------------------------------------------------------------------

global    _start

section   .text
";

struct AsmWriter {
    w: BufWriter<File>,
    data: Vec<u8>,
    data_index: u32
}

impl AsmWriter {
    fn new(file: File) -> Self {
        let mut w = BufWriter::new(file);
        w.write_all(FILE_START).unwrap();
        Self {
            w,
            data: Vec::new(),
            data_index: 0,
        }
    }

    fn begin_func(&mut self, name: &str) {
        write!(self.w, "{name}:\n").unwrap();
    }

    fn label(&mut self, func: u32, block: u32) {
        write!(self.w, "label{func}_{block}:\n").unwrap();
    }

    fn inst(&mut self, inst: Inst) {
        use Inst::*;
        write!(self.w, "\t").unwrap();
        let mut w = |inst: &str, args: &[Val]| {
            write!(self.w, "{inst} ").unwrap();
            for (i, arg) in args.into_iter().enumerate() {
                if i != 0 {
                    write!(self.w, ", ").unwrap();
                }
                write!(self.w, "{arg}").unwrap();
            }
        };
        match inst {
            mov(a, b) => w("mov", &[a, b]),
            push(r) => w("push", &[r]),
            pop(r) => w("pop", &[r]),
            ret => w("ret", &[])
        }
        write!(self.w, "\n").unwrap();
    }

    fn data(&mut self, data: &[u8]) -> u32 {
        self.data.extend(format!("data{}: ", self.data_index).as_bytes());
        self.data.extend(data);
        self.data.push(b'\n');
        self.data_index += 1;
        self.data_index - 1
    }
}

impl Drop for AsmWriter {
    fn drop(&mut self) {
        self.w.write_all(b"\nsection .data\n").unwrap();
        self.w.write_all(&self.data).unwrap();
        //message:  db        \"Hello, World\", 10      ; note the newline at the end
    }
}

pub unsafe fn emit(module: &ir::Module, file: File) {
    let mut w = AsmWriter::new(file);

    for (index, func) in module.funcs.iter().enumerate() {
        gen_func(index as u32, func, &mut w);
    }
}

unsafe fn gen_func(index: u32, func: &ir::FinalFunction, w: &mut AsmWriter) {
    if let Some(ir) = &func.ir {
        w.begin_func(if func.name == "main" { "_start" } else { &func.name });
        w.inst(push(rbp));

        let mut r = Vec::with_capacity(ir.inst.len());

        let mut offset: u32 = 0;

        let get_ref = |r: ir::Ref, refs: &[Val]| {
            if let Some(v) = r.into_val() {
                match v {
                    ir::RefVal::True => Int(1),
                    ir::RefVal::False => Int(0),
                    ir::RefVal::Unit => Int(0),
                    ir::RefVal::Undef => Int(0),
                }
            } else {
                let r = r.into_ref().unwrap();
                refs[r as usize]
            }
        };

        for inst in &ir.inst {
            let Instruction { data, tag, ty: _, span: _, used: _ } = inst;
            let val = match *tag {
                Tag::BlockBegin => {
                    w.label(index, data.int32);
                    NoVal
                }
                Tag::Ret => {
                    w.inst(mov(eax, get_ref(data.un_op, &r)));
                    w.inst(pop(rbp));
                    w.inst(ret);
                    NoVal
                }
                Tag::Param => todo!(),
                Tag::Int => Int(data.int),
                Tag::LargeInt => todo!(),
                Tag::Float => todo!(),
                Tag::Decl => {
                    let current_offset = offset;
                    offset += 8;
                    Stack(current_offset)
                }
                Tag::Load => get_ref(data.un_op, &r),
                Tag::Store => {
                    let into = get_ref(data.bin_op.0, &r);
                    let val = get_ref(data.bin_op.1, &r);
                    
                    w.inst(mov(into, val));
                    NoVal
                }
                Tag::String => {
                    let bytes = &ir.extra[
                        inst.data.extra_len.0 as usize
                        .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                    ];
                    Data(w.data(bytes))
                }
                Tag::Call => todo!(),
                Tag::Neg => todo!(),
                Tag::Not => todo!(),
                Tag::Add => todo!(),
                Tag::Sub => todo!(),
                Tag::Mul => todo!(),
                Tag::Div => todo!(),
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
                Tag::Goto => todo!(),
                Tag::Branch => todo!(),
                Tag::Phi => todo!(),
                
            };
            r.push(val);
        }
    }
}