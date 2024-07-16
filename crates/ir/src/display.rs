use std::fmt;

use color_format::{cwrite, cwriteln};

use crate::{ir_types::ConstIrType, BlockInfo};

use super::{
    instruction::DataVariant, ir_types::IrTypes, Data, Function, FunctionIr, Instruction, Module,
    Ref,
};

#[derive(Clone, Copy)]
pub struct Info<'a> {
    pub funcs: &'a [Function],
}

impl FunctionIr {
    pub fn display<'a>(&'a self, info: Info<'a>, types: &'a IrTypes) -> FunctionIrDisplay<'a> {
        FunctionIrDisplay {
            ir: self,
            info,
            types,
        }
    }
}
pub struct FunctionIrDisplay<'a> {
    ir: &'a FunctionIr,
    info: Info<'a>,
    types: &'a IrTypes,
}
impl fmt::Display for FunctionIrDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for block in self.ir.blocks() {
            cwrite!(f, "  #m<block> #b!<b{}>", block.idx())?;
            let args = self.ir.get_block_args(block);
            if !args.is_empty() {
                write!(f, "(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write_ref(f, Ref::index(arg))?;
                }
                write!(f, ")")?;
            }
            writeln!(f, ":")?;
            for (i, inst) in self.ir.get_block(block) {
                if inst.tag == crate::Tag::Nothing {
                    continue;
                }
                if inst.tag.is_usable() {
                    cwrite!(f, "    #c<{:>4}> = ", format!("%{i}"))?;
                } else {
                    write!(f, "           ")?;
                }
                cwriteln!(
                    f,
                    "{}",
                    inst.display(&self.ir.extra, self.types, self.info, &self.ir.blocks)
                )?;
            }
        }
        Ok(())
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let info = Info { funcs: &self.funcs };
        // TODO: show globals
        /*
        for (name, ty, val) in &self.globals {
            cwriteln!(f, "#b<global> #r<{}> : #m<{}>\n", name, ty.display(info))?;
            if let Some(val) = val {
                cwriteln!(f, " = {}", val)?;
            }
        }
        */
        for func in &self.funcs {
            if func.ir.is_none() {
                cwriteln!(f, "#m<extern> #r<{}>{}", func.name, func.display(info))?;
            } else {
                cwriteln!(
                    f,
                    "#b<begin> #r<{name}>{}#b<end> #r<{name}>\n",
                    func.display(info),
                    name = func.name
                )?;
            }
        }
        Ok(())
    }
}

impl Function {
    pub fn display<'a>(&'a self, info: Info<'a>) -> FunctionDisplay<'a> {
        FunctionDisplay { func: self, info }
    }
}

pub struct FunctionDisplay<'a> {
    func: &'a Function,
    info: Info<'a>,
}
impl<'a> fmt::Display for FunctionDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { func, info } = self;
        write!(f, "(")?;
        write_delimited_with(
            f,
            func.params.iter(),
            |f, param| display_type(f, func.types[param], &func.types, *info),
            ", ",
        )?;
        if func.varargs {
            if !func.params.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "...")?;
        }
        cwrite!(f, ") -#> ")?;
        display_type(f, func.return_type, &func.types, *info)?;

        if let Some(ir) = &func.ir {
            write!(f, "\n{}", ir.display(*info, &func.types))?;
        }
        Ok(())
    }
}

impl Instruction {
    pub fn display<'a>(
        &'a self,
        extra: &'a [u8],
        types: &'a IrTypes,
        info: Info<'a>,
        blocks: &'a [BlockInfo],
    ) -> InstructionDisplay<'a> {
        InstructionDisplay {
            inst: self,
            extra,
            types,
            info,
            blocks,
        }
    }
}
pub struct InstructionDisplay<'a> {
    inst: &'a Instruction,
    extra: &'a [u8],
    types: &'a IrTypes,
    info: Info<'a>,
    blocks: &'a [BlockInfo],
}

impl<'a> fmt::Display for InstructionDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let InstructionDisplay {
            inst,
            extra,
            types,
            info,
            blocks,
        } = self;
        write!(f, "{} ", inst.tag)?;
        display_data(inst, f, extra, self.types, *info, blocks)?;
        if inst.ty.is_present() {
            match inst.tag {
                _ => cwrite!(f, " :: ")?,
            };
            display_type(f, types[inst.ty], types, self.info)?;
        }
        Ok(())
    }
}
fn display_type(
    f: &mut fmt::Formatter<'_>,
    ty: super::ir_types::IrType,
    types: &IrTypes,
    info: Info,
) -> fmt::Result {
    use super::ir_types::IrType;

    let name = match ty {
        IrType::I8 => "i8",
        IrType::I16 => "i16",
        IrType::I32 => "i32",
        IrType::I64 => "i64",
        IrType::I128 => "i128",
        IrType::U8 => "u8",
        IrType::U16 => "u16",
        IrType::U32 => "u32",
        IrType::U64 => "u64",
        IrType::U128 => "u128",
        IrType::F32 => "f32",
        IrType::F64 => "f64",
        IrType::U1 => "u1",
        IrType::Unit => "unit",
        IrType::Ptr => "ptr",
        IrType::Array(inner, count) => {
            cwrite!(f, "#m<[>")?;
            display_type(f, types[inner], types, info)?;
            cwrite!(f, "#m<; {count}]>")?;
            return Ok(());
        }
        IrType::Tuple(elems) => {
            cwrite!(f, "#m<(>")?;
            write_delimited_with(
                f,
                elems.iter(),
                |f, ty| display_type(f, types[ty], types, info),
                ", ",
            )?;
            cwrite!(f, "#m<)>")?;
            return Ok(());
        }
        IrType::Const(ConstIrType::Int) => "{const: int}",
        IrType::Const(ConstIrType::Float) => "{const: float}",
        IrType::Const(ConstIrType::Enum) => "{const: enum}",
    };
    cwrite!(f, "#m<{name}>")
}

fn write_ref(f: &mut fmt::Formatter<'_>, r: Ref) -> fmt::Result {
    if let Some(val) = r.into_val() {
        cwrite!(f, "#y<{}>", val)
    } else {
        cwrite!(f, "#c<%{}>", r.into_ref().unwrap())
    }
}

fn write_block_args(
    f: &mut fmt::Formatter,
    arg_count: u32,
    extra: &[u8],
    idx: usize,
) -> fmt::Result {
    let mut bytes = [0; 4];
    if arg_count != 0 {
        cwrite!(f, "(")?;
        for i in 0..arg_count {
            if i != 0 {
                cwrite!(f, ", ")?;
            }
            let i = idx + i as usize * 4;
            bytes.copy_from_slice(&extra[i..i + 4]);
            write_ref(f, Ref::from_bytes(bytes))?;
        }
        cwrite!(f, ")")?;
    }
    Ok(())
}

fn display_data(
    inst: &Instruction,
    f: &mut fmt::Formatter<'_>,
    extra: &[u8],
    types: &IrTypes,
    info: Info,
    blocks: &[BlockInfo],
) -> fmt::Result {
    match inst.tag.union_data_type() {
        DataVariant::Int => {
            let x = inst.data.int();
            if types[inst.ty].is_signed_int() {
                cwrite!(f, "#y<{}>", x as i64)
            } else {
                cwrite!(f, "#y<{}>", x)
            }
        }
        DataVariant::Global => cwrite!(f, "#m<{}>", inst.data.global()),
        DataVariant::MemberPtr => {
            let (ptr, elem_refs, elem_idx) = inst.data.member_ptr(extra);
            write_ref(f, ptr)?;
            cwrite!(f, " #g<as> #m<*(>")?;
            write_delimited_with(
                f,
                elem_refs.iter(),
                |f, elem| display_type(f, types[elem], types, info),
                ", ",
            )?;
            cwrite!(f, "#m<)>, #y<{elem_idx}>")
        }
        DataVariant::ArrayIndex => {
            let (array_ptr, elem_ty, index_ref) = inst.data.array_index(extra);
            write_ref(f, array_ptr)?;
            cwrite!(f, " #g<as> #m<*[>")?;
            display_type(f, types[elem_ty], types, info)?;
            cwrite!(f, "#m<]>, ")?;
            write_ref(f, index_ref)
        }
        DataVariant::LargeInt => {
            let i = inst.data.extra() as usize;
            cwrite!(
                f,
                "#y<{}>",
                u128::from_le_bytes(extra[i..i + 16].try_into().unwrap())
            )
        }
        DataVariant::String => {
            let (i, len) = inst.data.extra_len();
            let string = String::from_utf8_lossy(&extra[i as usize..i as usize + len as usize]);
            cwrite!(f, "#y<{:?}>", string)
        }
        DataVariant::Call => {
            let (func, args) = inst.data.call(extra);
            cwrite!(f, "#r<{}>(", info.funcs[func.0 as usize].name)?;
            write_delimited_with(f, args, write_ref, ", ")?;
            cwrite!(f, ")")
        }
        DataVariant::Float => cwrite!(f, "#y<{}>", inst.data.float()),
        DataVariant::TypeTableIdx => display_type(f, types[inst.data.ty()], types, info),
        DataVariant::UnOp => write_ref(f, inst.data.un_op()),
        DataVariant::BinOp => {
            write_ref(f, inst.data.bin_op().0)?;
            write!(f, ", ")?;
            write_ref(f, inst.data.bin_op().1)
        }
        DataVariant::Goto => {
            let (block, extra_idx) = inst.data.goto();
            let arg_count = blocks[block.idx() as usize].arg_count;
            cwrite!(f, "{}", block)?;
            write_block_args(f, arg_count, &extra, extra_idx)
        }
        DataVariant::Branch => {
            let (r, a, b, i) = inst.data.branch(extra);
            write_ref(f, r)?;
            let a_count = blocks[a.idx() as usize].arg_count;
            let b_count = blocks[b.idx() as usize].arg_count;
            cwrite!(f, " #b!<{a}>")?;
            write_block_args(f, a_count, extra, i)?;
            cwrite!(f, " #g<or> ")?;
            write_block_args(f, a_count, extra, i)?;
            cwrite!(f, "#b!<{}>", b)?;
            write_block_args(f, b_count, extra, i + a_count as usize * 4)
        }
        DataVariant::RefInt => {
            write_ref(f, inst.data.ref_int().0)?;
            cwrite!(f, ", #y<{}>", inst.data.ref_int().1)
        }
        DataVariant::Asm => {
            unsafe {
                let Data {
                    asm: (extra_idx, str_len, arg_count),
                } = inst.data;
                let str_bytes = &extra[extra_idx as usize..extra_idx as usize + str_len as usize];
                cwrite!(f, "#y<\"{}\">", std::str::from_utf8(str_bytes).unwrap())?;
                let expr_base = extra_idx as usize + str_len as usize;
                for i in 0..arg_count as usize {
                    write!(f, ", ")?;
                    let mut arg_bytes = [0; 4];
                    arg_bytes.copy_from_slice(&extra[expr_base + 4 * i..expr_base + 4 * (i + 1)]);
                    write_ref(f, Ref::from_bytes(arg_bytes))?;
                }
            }
            Ok(())
        }
        DataVariant::None => Ok(()),
    }
}

fn write_delimited_with<W: std::fmt::Write, I, T, F, D>(
    f: &mut W,
    i: I,
    write_func: F,
    delim: D,
) -> fmt::Result
where
    I: IntoIterator<Item = T>,
    F: Fn(&mut W, T) -> fmt::Result,
    D: fmt::Display,
{
    let mut i = i.into_iter();
    i.next().map(|t| write_func(f, t)).transpose()?;
    for elem in i {
        write!(f, "{delim}")?;
        write_func(f, elem)?;
    }
    Ok(())
}
