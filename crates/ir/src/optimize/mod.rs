use std::fmt::Debug;

use color_format::ceprintln;

use crate::{instruction::DataVariant, Function, FunctionIr, Instruction, Ref};

mod dce;
mod inst_combine;
mod mem2reg;

pub use dce::Dce;
pub use inst_combine::InstCombine;
pub use mem2reg::Mem2Reg;

pub trait FunctionPass: Debug {
    fn run(&self, function: &mut Function, instrument: bool);
}

pub struct Pipeline {
    function_passes: Vec<Box<dyn FunctionPass>>,
    print_passes: bool,
}
impl Default for Pipeline {
    fn default() -> Self {
        Self {
            function_passes: vec![Box::new(Mem2Reg), Box::new(InstCombine), Box::new(Dce)],
            print_passes: false,
        }
    }
}
impl Pipeline {
    pub fn new() -> Self {
        Self {
            function_passes: Vec::new(),
            print_passes: false,
        }
    }

    pub fn add_function_pass(&mut self, pass: Box<dyn FunctionPass>) {
        self.function_passes.push(pass);
    }

    pub fn enable_print_passes(&mut self) {
        self.print_passes = true;
    }

    pub fn run(&self, module: &mut crate::Module) {
        for i in 0..module.funcs.len() {
            if module.funcs[i].ir.is_none() {
                continue;
            }
            if self.print_passes {
                for _ in 0..module.funcs[i].name.len() {
                    eprint!("-");
                }
                ceprintln!(
                    "-----------------------------\n\
                    IR for #r<{}> before optimizations:\n{}",
                    module.funcs[i].name,
                    module.funcs[i].display(crate::display::Info {
                        funcs: &module.funcs
                    })
                );
            }
            for pass in &self.function_passes {
                pass.run(&mut module.funcs[i], self.print_passes);
                if self.print_passes {
                    eprintln!(
                        "after {pass:?}:\n{}",
                        module.funcs[i].display(crate::display::Info {
                            funcs: &module.funcs,
                        })
                    );
                }
            }
        }
    }
}

/// Tracks renames of values to replace all uses of values with other values
pub struct RenameTable {
    renames: Box<[Option<Ref>]>,
}
impl RenameTable {
    pub fn new(ir: &FunctionIr) -> Self {
        Self {
            renames: vec![None; ir.total_inst_count() as usize].into_boxed_slice(),
        }
    }

    pub fn rename(&mut self, idx: u32, rename: Ref) {
        self.renames[idx as usize] = Some(rename);
    }

    pub fn visit_inst(&self, ir: &mut FunctionIr, inst: &mut Instruction) {
        let get_new =
            |r: Ref| -> Option<Ref> { r.into_ref().and_then(|i| self.renames[i as usize]) };
        let get = |r: Ref| get_new(r).unwrap_or(r);
        unsafe {
            match inst.tag.union_data_type() {
                DataVariant::Int
                | DataVariant::LargeInt
                | DataVariant::Float
                | DataVariant::Global
                | DataVariant::TypeTableIdx
                | DataVariant::String
                | DataVariant::Function
                | DataVariant::None => {}
                DataVariant::MemberPtr | DataVariant::RefInt => {
                    inst.data.ref_int.0 = get(inst.data.ref_int.0)
                }
                DataVariant::RefIntRef => {
                    let (r, extra) = inst.data.ref_int;
                    if let Some(new) = get_new(r) {
                        inst.data.ref_int.0 = new;
                    }
                    let ref_bytes = &mut ir.extra[extra as usize + 4..extra as usize + 8];
                    if let Some(new) = get_new(Ref::from_bytes(ref_bytes.try_into().unwrap())) {
                        ref_bytes.copy_from_slice(&new.to_bytes());
                    }
                }
                DataVariant::ArrayIndex => {
                    let (array_ptr, extra_start) = inst.data.ref_int();
                    let extra_start = extra_start as usize;
                    let bytes = &mut ir.extra[extra_start + 4..extra_start + 8];
                    let index_ref = Ref::from_bytes(bytes.try_into().unwrap());
                    inst.data.ref_int.0 = get(array_ptr);
                    if let Some(new) = get_new(index_ref) {
                        bytes.copy_from_slice(&new.to_bytes());
                    }
                }
                DataVariant::Call => {
                    let (idx, arg_count) = inst.data.extra_len();
                    for i in (idx as usize + 8..).step_by(4).take(arg_count as usize) {
                        let bytes = &mut ir.extra[i..i + 4];
                        let r = Ref::from_bytes(bytes.try_into().unwrap());
                        if let Some(new) = get_new(r) {
                            bytes.copy_from_slice(&new.to_bytes());
                        }
                    }
                }
                DataVariant::CallPtr => {
                    let (i, arg_count) = inst.data.extra_len();
                    let i = i as usize;
                    let bytes = &mut ir.extra[i..i + 4];
                    let func = Ref::from_bytes(bytes.try_into().unwrap());
                    if let Some(new) = get_new(func) {
                        bytes.copy_from_slice(&new.to_bytes());
                    }
                    for i in (i + 12..).step_by(4).take(arg_count as usize) {
                        let bytes = &mut ir.extra[i..i + 4];
                        let func = Ref::from_bytes(bytes.try_into().unwrap());
                        if let Some(new) = get_new(func) {
                            bytes.copy_from_slice(&new.to_bytes());
                        }
                    }
                }
                DataVariant::Goto => {
                    let (block, extra_idx) = inst.data.goto();
                    for i in (extra_idx..)
                        .step_by(4)
                        .take(ir.get_block_args(block).count())
                    {
                        let r = Ref::from_bytes(ir.extra[i..i + 4].try_into().unwrap());
                        if let Some(new) = get_new(r) {
                            ir.extra[i..i + 4].copy_from_slice(&new.to_bytes());
                        }
                    }
                }
                DataVariant::Branch => {
                    let (cond, a, b, extra_idx) = inst.data.branch(&ir.extra);
                    inst.data.ref_int.0 = get(cond);
                    let total_args = ir.get_block_args(a).count() + ir.get_block_args(b).count();
                    for i in (extra_idx..).step_by(4).take(total_args) {
                        let r = Ref::from_bytes(ir.extra[i..i + 4].try_into().unwrap());
                        if let Some(new) = get_new(r) {
                            ir.extra[i..i + 4].copy_from_slice(&new.to_bytes());
                        }
                    }
                }
                DataVariant::UnOp => inst.data.un_op = get(inst.data.un_op),
                DataVariant::BinOp => {
                    inst.data.bin_op.0 = get(inst.data.bin_op.0);
                    inst.data.bin_op.1 = get(inst.data.bin_op.1);
                }
                DataVariant::Asm => todo!("handle asm inst in InstCombine"),
            };
        }
    }
}
