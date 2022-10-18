use std::fmt;

use color_format::{cwrite, cwriteln};

use crate::help::{write_delimited, write_delimited_with};

use super::{
    Type,
    TypeDef,
    Function,
    Module,
    Instruction,
    FinalTypeTable,
    instruction::DataVariant,
    Ref,
    SymbolKey,
    Data,
    Tag,
    FunctionIr,
    Struct
};

#[derive(Clone, Copy)]
pub struct Info<'a> {
    pub types: &'a [(String, TypeDef)],
    pub funcs: &'a [Function],
}

impl FunctionIr {
    pub fn display<'a>(&'a self, info: Info<'a>) -> FunctionIrDisplay<'a> {
        FunctionIrDisplay { ir: self, info }
    }
}
pub struct FunctionIrDisplay<'a> {
    ir: &'a FunctionIr,
    info: Info<'a>,
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
            cwriteln!(f, "{}", inst.display(&self.ir.extra, &self.ir.types, self.info))?;
        }
        Ok(())
    }
}

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let info = Info { types: &self.types, funcs: &self.funcs };
        for (name, ty) in &self.types {
            cwriteln!(f, "#b<begin> #r<{name}>\n{}#b<end> #r<{name}>\n",
                ty.display(info),
                name = name,
            )?;
        }
        for (name, ty, val) in &self.globals {
            cwriteln!(f, "#b<global> #r<{}> : #m<{}>\n", name, ty.display(info))?;
            if let Some(val) = val {
                cwriteln!(f, " = {}", val)?;
            }
        }
        for func in &self.funcs {
            if func.ir.is_none() {
                cwriteln!(f, "#m<extern> #r<{}>{}", func.header.name, func.display(info))?;
            } else {
                cwriteln!(f, "#b<begin> #r<{name}>{}#b<end> #r<{name}>\n",
                    func.display(info),
                    name = func.header.name
                )?;
            }
        }
        Ok(())
    }
}

impl Type {
    pub fn display<'a>(&'a self, info: Info<'a>) -> impl fmt::Display + 'a {
        self.display_fn(|key| &info.types[key.idx()].0)
    }
    pub fn display_fn<'a, F: Fn(SymbolKey) -> &'a str>(&'a self, type_name: F) -> TypeDisplay<'a, F> {
        TypeDisplay { ty: self, type_name }
    }
}
pub struct TypeDisplay<'a, F: Fn(SymbolKey) -> &'a str> {
    ty: &'a Type,
    type_name: F,
}

impl<'a, F: Fn(SymbolKey) -> &'a str + Copy> fmt::Display for TypeDisplay<'a, F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { ty, type_name } = self;
        match ty {
            Type::Prim(p) => write!(f, "{p}"),
            Type::Id(id, generics) => {
                let ty = type_name(*id);
                write!(f, "{}", ty)?;
                if !generics.is_empty() {
                    write!(f, "[")?;
                    write_delimited(f, generics.iter().map(|ty| ty.display_fn(*type_name)), ", ")?;
                    write!(f, "]")?;
                }
                Ok(())
            }
            Type::Pointer(inner) => write!(f, "*{}", inner.display_fn(*type_name)),
            Type::Array(array) => {
                let (ty, count) = &**array;
                write!(f, "[{}; {}]", ty.display_fn(*type_name), count)
            }
            Type::Enum(variants) => {
                write_delimited(f, variants, " | ")?;
                Ok(())
            }
            Type::Tuple(elems) => {
                write!(f, "(")?;
                write_delimited(f, elems.iter().map(|ty| ty.display_fn(*type_name)), ", ")?;
                write!(f, ")")
            }
            Type::Generic(idx) => write!(f, "Generic #{idx}"),
            Type::Symbol => write!(f, "[symbol]"),
            Type::Invalid => write!(f, "[invalid]"),
        }
    }
}

impl Function {
    fn display<'a>(&'a self, info: Info<'a>) -> FunctionDisplay<'a> {
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
        write_delimited_with(f, &func.header.params,
            |f, (name, param)| cwrite!(f, "#g<{}> #m<{}>", name, param.display(*info)), ", ")?;
        cwriteln!(f, ") -#> #m<{}>", func.header.return_type.display(*info))?;

        if let Some(ir) = &func.ir {
            write!(f, "{}", ir.display(*info))?;
        }
        Ok(())
    }
}

impl Struct {
    pub fn display<'a>(&'a self, info: Info<'a>) -> StructDisplay<'a> {
        StructDisplay { s: self, info }
    }
}

pub struct StructDisplay<'a> {
    s: &'a Struct,
    info: Info<'a>,
}
impl fmt::Display for StructDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        cwrite!(f, "{{")?;
        let Self { s, info } = self;
        write_delimited_with(f, &s.members, |f, (name, m)| cwrite!(f, "#g<{}> #m<{}>", name, m.display(*info)), ", ")?;
        cwrite!(f, "}}")?;
        Ok(())
    }
}


impl TypeDef {
    pub fn display<'a>(&'a self, info: Info<'a>) -> TypeDefDisplay<'a> {
        TypeDefDisplay { def: self, info }
    }
}
pub struct TypeDefDisplay<'a> {
    def: &'a TypeDef,
    info: Info<'a>,
}
impl fmt::Display for TypeDefDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { def, info } = self;
        match def {
            TypeDef::Struct(s) => write!(f, "{}", s.display(*info)),
            TypeDef::Enum(e) => write!(f, "{e}"),
            TypeDef::NotGenerated { .. } => write!(f, "not generated")
        }
    }
}

impl Instruction {
    fn display<'a>(&'a self, extra: &'a [u8], types: &'a FinalTypeTable, info: Info<'a>)
    -> InstructionDisplay<'a> {
        InstructionDisplay { inst: self, extra, types, info }
    }
}
pub struct InstructionDisplay<'a> {
    inst: &'a Instruction,
    extra: &'a [u8],
    types: &'a FinalTypeTable,
    info: Info<'a>,
}

impl<'a> fmt::Display for InstructionDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let InstructionDisplay { inst, extra, types, info } = self;
        write!(f, "{} ", inst.tag)?;
        display_data(inst, f, extra, self.types, *info)?;
        if inst.ty.is_present() {
            match inst.tag {
                Tag::Cast => cwrite!(f, "#m!< as >")?,
                _ => cwrite!(f, " :: ")?
            };
            cwrite!(f, "#m!<{}>", types.get(inst.ty).display(*info))?;
        }
        Ok(())
    }
}
fn display_data(inst: &Instruction, f: &mut fmt::Formatter<'_>, extra: &[u8], types: &FinalTypeTable, info: Info)
-> fmt::Result {
    let write_ref = |f: &mut fmt::Formatter<'_>, r: Ref| {
        if let Some(val) = r.into_val() {
            cwrite!(f, "#y<{}>", val)
        } else {
            cwrite!(f, "#c<%{}>", r.into_ref().unwrap())
        }
    };
    unsafe { match inst.tag.union_data_type() {
        DataVariant::Int => cwrite!(f, "#y<{}>", inst.data.int),
        DataVariant::Int32 => cwrite!(f, "#y<{}>", inst.data.int32),
        DataVariant::Block => cwrite!(f, "{}", inst.data.block),
        DataVariant::LargeInt => {
            let bytes = &extra[
                inst.data.extra as usize
                .. (inst.data.extra + 16) as usize
            ];
            let mut bytes_arr = [0; 16];
            bytes_arr.copy_from_slice(bytes);
            cwrite!(f, "#y<{}>", u128::from_le_bytes(bytes_arr))
        }
        DataVariant::String => {
            let string = String::from_utf8_lossy(&extra[
                inst.data.extra_len.0 as usize
                .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
            ]);
            cwrite!(f, "#y<{:?}>", string)
        }
        DataVariant::Call => {
            let start = inst.data.extra_len.0 as usize;
            let mut bytes = [0; 8];
            bytes.copy_from_slice(&extra[start..start+8]);
            let func = SymbolKey(u64::from_le_bytes(bytes));
            let refs = (0..inst.data.extra_len.1).map(|i| {
                let mut ref_bytes = [0; 4];
                let begin = 8 + start + (4 * i) as usize;
                ref_bytes.copy_from_slice(&extra[begin..begin+4]);
                Ref::from_bytes(ref_bytes)
            });
            cwrite!(f, "#r<{}>(", info.funcs[func.idx()].header.name)?;
            write_delimited_with(f, refs, |f, r| write_ref(f, r), ", ")?;
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
                current_bytes.copy_from_slice(&extra[begin + 4 .. begin + 8]);
                current_bytes.copy_from_slice(&extra[begin + 4 .. begin + 8]);
                let r = Ref::from_bytes(current_bytes);
                cwrite!(f, "[")?;
                cwrite!(f, "#b!<b{}>, ", block)?;
                write_ref(f, r)?;
                cwrite!(f, "]")?;
            }
            Ok(())
        }
        DataVariant::Float => cwrite!(f, "#y<{}>", inst.data.float),
        DataVariant::Symbol => cwrite!(f, "f#m<{}>", inst.data.symbol.0),
        DataVariant::TraitFunc => {
            let mut buf = [0; 8];
            buf.copy_from_slice(&extra[inst.data.trait_func.0 as usize ..inst.data.trait_func.0 as usize + 8]);
            
            cwrite!(f, "#m<t{}>.#m<f{}>", SymbolKey::from_bytes(buf).0, inst.data.trait_func.1)
        }
        DataVariant::TypeTableIdx => {
            cwrite!(f, "#m<{}>", types[inst.data.ty].display(info))
        }
        DataVariant::UnOp => write_ref(f, inst.data.un_op),
        DataVariant::BinOp => {
            write_ref(f, inst.data.bin_op.0)?;
            write!(f, ", ")?;
            write_ref(f, inst.data.bin_op.1)
        }
        DataVariant::Branch => {
            let i = inst.data.branch.1 as usize;
            let mut bytes = [0; 4];
            bytes.copy_from_slice(&extra[i..i+4]);
            let a = u32::from_le_bytes(bytes);
            bytes.copy_from_slice(&extra[i+4..i+8]);
            let b = u32::from_le_bytes(bytes);
            write_ref(f, inst.data.branch.0)?;
            cwrite!(f, ", #b!<b{}> #m<or> #b!<b{}>", a, b)
        }
        DataVariant::Asm => {
            let Data { asm: (extra_idx, str_len, arg_count) } = inst.data;
            let str_bytes = &extra[extra_idx as usize .. extra_idx as usize + str_len as usize];
            cwrite!(f, "#y<\"{}\">", std::str::from_utf8_unchecked(str_bytes))?;
            let expr_base = extra_idx as usize + str_len as usize;
            for i in 0..arg_count as usize {
                write!(f, ", ")?;
                let mut arg_bytes = [0; 4];
                arg_bytes.copy_from_slice(&extra[expr_base + 4*i .. expr_base + 4*(i+1) ]);
                write_ref(f, Ref::from_bytes(arg_bytes))?;
            }
            Ok(())
        }
        DataVariant::Global => cwrite!(f, "#c<##{}>", inst.data.symbol.0),
        DataVariant::None => Ok(())
    }}
}