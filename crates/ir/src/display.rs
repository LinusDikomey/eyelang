use std::fmt;

use color_format::{cwrite, cwriteln};

use crate::{ir_types::ConstIrType, FunctionId, TypeRef, TypeRefs};

use super::{
    instruction::DataVariant, ir_types::IrTypes, Data, Function, FunctionIr, Instruction, Module,
    Ref, Tag,
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
        for (i, inst) in self.ir.inst.iter().enumerate() {
            if inst.tag == Tag::BlockBegin {
                //TODO: make this purple
                cwriteln!(f, "  #m<block> #b!<b{}>:", unsafe { inst.data.int32 })?;
                continue;
            }
            if inst.used {
                cwrite!(f, "    #c<{:>4}> = ", format!("%{i}"))?;
            } else {
                write!(f, "           ")?;
            }
            cwriteln!(f, "{}", inst.display(&self.ir.extra, self.types, self.info))?;
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
    ) -> InstructionDisplay<'a> {
        InstructionDisplay {
            inst: self,
            extra,
            types,
            info,
        }
    }
}
pub struct InstructionDisplay<'a> {
    inst: &'a Instruction,
    extra: &'a [u8],
    types: &'a IrTypes,
    info: Info<'a>,
}

impl<'a> fmt::Display for InstructionDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let InstructionDisplay {
            inst,
            extra,
            types,
            info,
        } = self;
        write!(f, "{} ", inst.tag)?;
        display_data(inst, f, extra, self.types, *info)?;
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

fn display_data(
    inst: &Instruction,
    f: &mut fmt::Formatter<'_>,
    extra: &[u8],
    types: &IrTypes,
    info: Info,
) -> fmt::Result {
    let write_ref = |f: &mut fmt::Formatter<'_>, r: Ref| {
        if let Some(val) = r.into_val() {
            cwrite!(f, "#y<{}>", val)
        } else {
            cwrite!(f, "#c<%{}>", r.into_ref().unwrap())
        }
    };
    unsafe {
        match inst.tag.union_data_type() {
            DataVariant::Int => cwrite!(f, "#y<{}>", inst.data.int),
            DataVariant::Int32 => cwrite!(f, "#y<{}>", inst.data.int32),
            DataVariant::Block => cwrite!(f, "{}", inst.data.block),
            DataVariant::MemberPtr => {
                let (ptr, extra_start) = inst.data.ref_int;
                let i = extra_start as usize;
                let elem_refs = TypeRefs::from_bytes(extra[i..i + 8].try_into().unwrap());
                let elem_idx = u32::from_le_bytes(extra[i + 8..i + 12].try_into().unwrap());
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
                let (array_ptr, extra_start) = inst.data.ref_int;
                let i = extra_start as usize;
                let elem_ty = TypeRef::from_bytes(extra[i..i + 4].try_into().unwrap());
                let index_ref = Ref::from_bytes(extra[i + 4..i + 8].try_into().unwrap());
                write_ref(f, array_ptr)?;
                cwrite!(f, " #g<as> #m<*[>")?;
                display_type(f, types[elem_ty], types, info)?;
                cwrite!(f, "#m<]>, ")?;
                write_ref(f, index_ref)
            }
            DataVariant::LargeInt => {
                let bytes = &extra[inst.data.extra as usize..(inst.data.extra + 16) as usize];
                let mut bytes_arr = [0; 16];
                bytes_arr.copy_from_slice(bytes);
                cwrite!(f, "#y<{}>", u128::from_le_bytes(bytes_arr))
            }
            DataVariant::String => {
                let string = String::from_utf8_lossy(
                    &extra[inst.data.extra_len.0 as usize
                        ..(inst.data.extra_len.0 + inst.data.extra_len.1) as usize],
                );
                cwrite!(f, "#y<{:?}>", string)
            }
            DataVariant::Call => {
                let start = inst.data.extra_len.0 as usize;
                let mut bytes = [0; 8];
                bytes.copy_from_slice(&extra[start..start + 8]);
                let func = FunctionId::from_bytes(bytes);
                let refs = (0..inst.data.extra_len.1).map(|i| {
                    let mut ref_bytes = [0; 4];
                    let begin = 8 + start + (4 * i) as usize;
                    ref_bytes.copy_from_slice(&extra[begin..begin + 4]);
                    Ref::from_bytes(ref_bytes)
                });
                cwrite!(f, "#r<{}>(", info.funcs[func.0 as usize].name)?;
                write_delimited_with(f, refs, write_ref, ", ")?;
                cwrite!(f, ")")
            }
            DataVariant::ExtraBranchRefs => {
                for i in 0..inst.data.extra_len.1 {
                    if i != 0 {
                        cwrite!(f, ", ")?;
                    }
                    let mut current_bytes = [0; 4];
                    let begin = (inst.data.extra_len.0 + i * 8) as usize;
                    current_bytes.copy_from_slice(&extra[begin..begin + 4]);
                    let block = u32::from_le_bytes(current_bytes);
                    current_bytes.copy_from_slice(&extra[begin + 4..begin + 8]);
                    current_bytes.copy_from_slice(&extra[begin + 4..begin + 8]);
                    let r = Ref::from_bytes(current_bytes);
                    cwrite!(f, "[")?;
                    cwrite!(f, "#b!<b{}>, ", block)?;
                    write_ref(f, r)?;
                    cwrite!(f, "]")?;
                }
                Ok(())
            }
            DataVariant::Float => cwrite!(f, "#y<{}>", inst.data.float),
            DataVariant::TypeTableIdx => display_type(f, types[inst.data.ty], types, info),
            DataVariant::UnOp => write_ref(f, inst.data.un_op),
            DataVariant::BinOp => {
                write_ref(f, inst.data.bin_op.0)?;
                write!(f, ", ")?;
                write_ref(f, inst.data.bin_op.1)
            }
            DataVariant::Branch => {
                let i = inst.data.ref_int.1 as usize;
                let mut bytes = [0; 4];
                bytes.copy_from_slice(&extra[i..i + 4]);
                let a = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&extra[i + 4..i + 8]);
                let b = u32::from_le_bytes(bytes);
                write_ref(f, inst.data.ref_int.0)?;
                cwrite!(f, ", #b!<b{}> #g<or> #b!<b{}>", a, b)
            }
            DataVariant::RefInt => {
                write_ref(f, inst.data.ref_int.0)?;
                cwrite!(f, ", #y<{}>", inst.data.ref_int.1)
            }
            DataVariant::Asm => {
                let Data {
                    asm: (extra_idx, str_len, arg_count),
                } = inst.data;
                let str_bytes = &extra[extra_idx as usize..extra_idx as usize + str_len as usize];
                cwrite!(f, "#y<\"{}\">", std::str::from_utf8_unchecked(str_bytes))?;
                let expr_base = extra_idx as usize + str_len as usize;
                for i in 0..arg_count as usize {
                    write!(f, ", ")?;
                    let mut arg_bytes = [0; 4];
                    arg_bytes.copy_from_slice(&extra[expr_base + 4 * i..expr_base + 4 * (i + 1)]);
                    write_ref(f, Ref::from_bytes(arg_bytes))?;
                }
                Ok(())
            }
            DataVariant::None => Ok(()),
        }
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
