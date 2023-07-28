use std::fmt;

use color_format::{cwrite, cwriteln};

use crate::{
    help::{write_delimited, write_delimited_with},
    ast::{TypeId, FunctionId, TraitId},
    resolve::types::{Struct, ResolvedTypeDef, Type, Enum, ResolvedTypeBody},
    ir::types::ConstIrType,
};

use super::{
    Function,
    Module,
    Instruction,
    instruction::DataVariant,
    Ref,
    Data,
    Tag,
    FunctionIr, types::IrTypes,
};

#[derive(Clone, Copy)]
pub struct Info<'a> {
    pub types: &'a [(String, ResolvedTypeDef)],
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
                cwriteln!(f, "#m<extern> #r<{}>{}", func.name, func.display(info))?;
            } else {
                cwriteln!(f, "#b<begin> #r<{name}>{}#b<end> #r<{name}>\n",
                    func.display(info),
                    name = func.name
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
    #[must_use]
    pub fn display_fn<'a, F: Fn(TypeId) -> &'a str>(&'a self, type_name: F) -> TypeDisplay<'a, F> {
        TypeDisplay { ty: self, type_name }
    }
}
pub struct TypeDisplay<'a, F: Fn(TypeId) -> &'a str> {
    ty: &'a Type,
    type_name: F,
}

impl<'a, F: Fn(TypeId) -> &'a str + Copy> fmt::Display for TypeDisplay<'a, F> {
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
            Type::Tuple(elems) => {
                write!(f, "(")?;
                write_delimited(f, elems.iter().map(|ty| ty.display_fn(*type_name)), ", ")?;
                write!(f, ")")
            }
            Type::Generic(idx) => write!(f, "Generic #{idx}"),
            Type::LocalEnum(variants) => {
                write!(f, "enum {{")?;
                write_delimited_with(f, variants, |f, variant| {
                    write!(f, "(")?;
                    for arg in variant {
                        write!(f, "{}", arg.display_fn(self.type_name))?;
                    }
                    write!(f, ")")
                }, ", ")?;
                write!(f, "}}")
            }
            Type::TraitSelf => write!(f, "Self"),
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
        write_delimited_with(f, &func.params,
            |f, (name, param)| cwrite!(f, "#g<{}> #m<{}>", name, param.display(*info)), ", ")?;
        if func.varargs {
            if !func.params.is_empty() {
                write!(f, ", ")?;
            }
            write!(f, "...")?;
        }
        cwriteln!(f, ") -#> #m<{}>", func.return_type.display(*info))?;

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
        let Self { s, info } = self;
        for (name, m) in &s.members {
            cwrite!(f, "  #g<{}> #m<{}>\n", name, m.display(*info))?;
        }
        Ok(())
    }
}

impl fmt::Display for Enum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (variant, (_, variant_val, variant_types)) in &self.variants {
            if variant_types.is_empty() {
                cwriteln!(f, "  #m<{}> = #c<{}>", variant, variant_val)?;
            } else {
                cwrite!(f, "  #m<{}>", variant)?;

                for _ty in variant_types {
                    write!(f, "TODO: render types here")?;
                }

                cwriteln!(f, " = #c<{}>", variant_val)?;
            }
        }
        Ok(())
    }
}


impl ResolvedTypeDef {
    pub fn display<'a>(&'a self, info: Info<'a>) -> TypeDefDisplay<'a> {
        TypeDefDisplay { def: self, info }
    }
}
pub struct TypeDefDisplay<'a> {
    def: &'a ResolvedTypeDef,
    info: Info<'a>,
}
impl fmt::Display for TypeDefDisplay<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self { def, info } = self;
        match &def.body {
            ResolvedTypeBody::Struct(s) => write!(f, "{}", s.display(*info)),
            ResolvedTypeBody::Enum(e) => write!(f, "{e}"),
        }
    }
}

impl Instruction {
    pub fn display<'a>(&'a self, extra: &'a [u8], types: &'a IrTypes, info: Info<'a>)
    -> InstructionDisplay<'a> {
        InstructionDisplay { inst: self, extra, types, info }
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
        let InstructionDisplay { inst, extra, types, info } = self;
        write!(f, "{} ", inst.tag)?;
        display_data(inst, f, extra, self.types, *info)?;
        if inst.ty.is_present() {
            match inst.tag {
                Tag::Cast => cwrite!(f, "#m!< as >")?,
                _ => cwrite!(f, " :: ")?
            };
            display_type(f, types[inst.ty], types, self.info)?;
        }
        Ok(())
    }
}
fn display_type(f: &mut fmt::Formatter<'_>, ty: super::types::IrType, types: &IrTypes, info: Info) -> fmt::Result {
    use super::types::IrType;

    match ty {
        IrType::Primitive(p) => write!(f, "{p}"),
        IrType::Id(id, generics) => {
            write!(f, "{}", info.types[id.idx()].0)?;
            if generics.len() > 0 {
                write!(f, "[")?;
                for (i, generic) in generics.iter().enumerate() {
                    if i != 0 {
                        write!(f, ",")?;
                    }
                    display_type(f, types[generic], types, info)?;
                }
                write!(f, "]")?;
            }
            Ok(())
        }
        IrType::Ptr(inner) => {
            write!(f, "*")?;
            display_type(f, types[inner], types, info)
        }
        IrType::Array(inner, count) => {
            write!(f, "[")?;
            display_type(f, types[inner], types, info)?;
            write!(f, "; {count}]")
        }
        IrType::Tuple(elems) => {
            write!(f, "(")?;
            write_delimited_with(f, elems.iter(), |f, ty| display_type(f, types[ty], types, info), ", ")?;
            write!(f, ")")
        }
        IrType::Enum(variants) => {
            write!(f, "enum {{")?;
            write_delimited_with(f, variants.iter().enumerate(), |f, (i, variant)| {
                write!(f, "{i}")?;
                let IrType::Tuple(args) = types[variant] else { panic!("invalid IrTypes") };
                if args.len() > 0 {
                    write!(f, "(")?;
                    write_delimited_with(f, args.iter(), |f, arg| display_type(f, types[arg], types, info), ", ")?;
                    write!(f, ")")?;
                }
                Ok(())
            }, ", ")?;
            write!(f, "}}")
        }
        IrType::Const(ConstIrType::Int) => write!(f, "int"),
        IrType::Const(ConstIrType::Float) => write!(f, "enum"),
        IrType::Const(ConstIrType::Enum) => write!(f, "float"),
        IrType::Ref(r) => display_type(f, types[r], types, info)
    }
}

fn display_data(inst: &Instruction, f: &mut fmt::Formatter<'_>, extra: &[u8], types: &IrTypes, info: Info)
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
            let func = FunctionId::from_bytes(bytes);
            let refs = (0..inst.data.extra_len.1).map(|i| {
                let mut ref_bytes = [0; 4];
                let begin = 8 + start + (4 * i) as usize;
                ref_bytes.copy_from_slice(&extra[begin..begin+4]);
                Ref::from_bytes(ref_bytes)
            });
            cwrite!(f, "#r<{}>(", info.funcs[func.idx()].name)?;
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
        DataVariant::TraitFunc => {
            let mut buf = [0; 8];
            buf.copy_from_slice(&extra[inst.data.trait_func.0 as usize ..inst.data.trait_func.0 as usize + 8]);
            
            cwrite!(f, "#m<t{}>.#m<f{}>", TraitId::from_bytes(buf).idx(), inst.data.trait_func.1)
        }
        DataVariant::TypeTableIdx => {
            display_type(f, types[inst.data.ty], types, info)
        }
        DataVariant::UnOp => write_ref(f, inst.data.un_op),
        DataVariant::BinOp => {
            write_ref(f, inst.data.bin_op.0)?;
            write!(f, ", ")?;
            write_ref(f, inst.data.bin_op.1)
        }
        DataVariant::Branch => {
            let i = inst.data.ref_int.1 as usize;
            let mut bytes = [0; 4];
            bytes.copy_from_slice(&extra[i..i+4]);
            let a = u32::from_le_bytes(bytes);
            bytes.copy_from_slice(&extra[i+4..i+8]);
            let b = u32::from_le_bytes(bytes);
            write_ref(f, inst.data.ref_int.0)?;
            cwrite!(f, ", #b!<b{}> #m<or> #b!<b{}>", a, b)
        }
        DataVariant::RefInt => {
            write_ref(f, inst.data.ref_int.0)?;
            cwrite!(f, ", #y<{}>", inst.data.ref_int.1)
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
        DataVariant::Func => cwrite!(f, "func #c<##{}>", inst.data.func_symbol.idx()),
        DataVariant::Type => cwrite!(f, "type #c<##{}>", inst.data.type_symbol.idx()),
        DataVariant::Trait => cwrite!(f, "trait #c<##{}>", inst.data.trait_symbol.idx()),
        DataVariant::Global => cwrite!(f, "global #c<##{}>", inst.data.global_symbol.idx()),
        DataVariant::VariantMember => {
            write_ref(f, inst.data.variant_member.0)?;
            write!(f, " {:?} arg {}", inst.data.variant_member.1, inst.data.variant_member.2)
        }
        DataVariant::None => Ok(())
    }}
}
