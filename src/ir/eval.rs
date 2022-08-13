use crate::{ir::{Ref, gen::ConstSymbol, SymbolKey, TypeTableIndex, BlockIndex}, error::Error, ast::ModuleId};

use super::{ConstVal, TypeInfo};

#[derive(Clone, Debug)]
enum LocalVal {
    Val(ConstVal),
    Var(ConstVal),
}

pub static mut BACKWARDS_JUMP_LIMIT: usize = 1000;

// TODO: give errors a span by giving all IR instructions spans.
pub unsafe fn eval(ir: &super::IrBuilder, params: &[ConstVal]) -> Result<ConstVal, Error> {
    let mut values = vec![LocalVal::Val(ConstVal::Invalid); ir.inst.len()];

    fn get_ref(values: &[LocalVal], r: Ref) -> ConstVal {
        if let Some(r) = r.into_ref() {
            match &values[r as usize] {
                LocalVal::Val(v) => v.clone(),
                LocalVal::Var(_) => panic!("Unexpected variable reference"),
            }
        } else {
            match r.into_val().unwrap() {
                crate::ir::RefVal::True => ConstVal::Bool(true),
                crate::ir::RefVal::False => ConstVal::Bool(false),
                crate::ir::RefVal::Unit => ConstVal::Unit,
                crate::ir::RefVal::Undef => ConstVal::Invalid,
            }
        }
    }
    let mut pos: u32 = 0;
    let mut previous_block = BlockIndex(0);
    let mut current_block = BlockIndex(0);
    let mut backwards_jumps = 0;

    macro_rules! bin_op {
        ($op: tt, $inst: expr) => {{
            let l = get_ref(&values, $inst.data.bin_op.0);
            let r = get_ref(&values, $inst.data.bin_op.1);

            match &ir.types[$inst.ty] {
                TypeInfo::Primitive(p) if p.is_int() => {
                    let ConstVal::Int(l_ty, l_val) = l else { panic!() };
                    let ConstVal::Int(r_ty, r_val) = r else { panic!() };
                    let ty = p.as_int().unwrap();
                    assert!(match l_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    assert!(match r_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    ConstVal::Int(Some(ty), l_val $op r_val)
                }
                TypeInfo::Int => {
                    let ConstVal::Int(l_ty, l_val) = l else { panic!() };
                    let ConstVal::Int(r_ty, r_val) = r else { panic!() };
                    assert!(l_ty.is_none());
                    assert!(r_ty.is_none());
                    ConstVal::Int(None, l_val $op r_val)
                }
                TypeInfo::Primitive(p) if p.is_float() => {
                    let ConstVal::Float(l_ty, l_val) = l else { panic!() };
                    let ConstVal::Float(r_ty, r_val) = r else { panic!() };
                    let ty = p.as_float().unwrap();
                    debug_assert!(match l_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    debug_assert!(match r_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    ConstVal::Float(Some(ty), l_val $op r_val)                        
                }
                TypeInfo::Float => {
                    let ConstVal::Float(l_ty, l_val) = l else { panic!() };
                    let ConstVal::Float(r_ty, r_val) = r else { panic!() };
                    assert!(l_ty.is_none());
                    assert!(r_ty.is_none());
                    ConstVal::Float(None, l_val $op r_val)
                }
                t => panic!("Invalid type for binary operation: {t:?}")
            }
        }};
    }
    macro_rules! cmp_op {
        ($op: tt, $inst: expr) => {{
            let l = get_ref(&values, $inst.data.bin_op.0);
            let r = get_ref(&values, $inst.data.bin_op.1);

            match (l, r) {
                (ConstVal::Int(l_ty, l_val), ConstVal::Int(r_ty, r_val)) => {
                    debug_assert!(match (l_ty, r_ty) {
                        (Some(l), Some(r)) => l == r,
                        _ => true
                    });
                    ConstVal::Bool(l_val $op r_val)
                }
                (ConstVal::Float(l_ty, l_val), ConstVal::Float(r_ty, r_val)) => {
                    debug_assert!(match (l_ty, r_ty) {
                        (Some(l), Some(r)) => l == r,
                        _ => true
                    });
                    ConstVal::Bool(l_val $op r_val)
                }
                (l, r) => panic!("Invalid values for comparison: {l}, {r}")
            }
        }};
    }

    let val = loop {
        let inst = ir.inst[pos as usize];
        values[pos as usize] = LocalVal::Val(match inst.tag {
            super::Tag::BlockBegin => {
                previous_block = current_block;
                current_block = inst.data.block;
                ConstVal::Invalid
            }
            super::Tag::Ret => break get_ref(&values, inst.data.un_op),
            super::Tag::RetUndef => break ConstVal::Invalid, // could this also be unit?
            super::Tag::Param => params[inst.data.int32 as usize].clone(),
            super::Tag::Int => {
                let int_ty = match ir.types[inst.ty] {
                    TypeInfo::Primitive(p) if p.is_int() => Some(p.as_int().unwrap()),
                    TypeInfo::Int => None,
                    _ => panic!("invalid type in const eval")
                };
                ConstVal::Int(int_ty, inst.data.int as _)
            }
            super::Tag::LargeInt => {
                let int_ty = match ir.types[inst.ty] {
                    TypeInfo::Primitive(p) if p.is_int() => Some(p.as_int().unwrap()),
                    TypeInfo::Int => None,
                    _ => panic!("invalid type in const eval of float")
                };
                let bytes = &ir.extra[
                    inst.data.extra as usize
                    .. (inst.data.extra + 16) as usize
                ];
                let mut bytes_arr = [0; 16];
                bytes_arr.copy_from_slice(bytes);
                let int = u128::from_le_bytes(bytes_arr)
                    .try_into()
                    .expect("integer value too large for const evaluator");
                ConstVal::Int(int_ty, int)
            }
            super::Tag::Float => {
                let float_ty = match &ir.types[inst.ty] {
                    TypeInfo::Primitive(p) if p.is_float() => Some(p.as_float().unwrap()),
                    TypeInfo::Float => None,
                    ty => panic!("invalid type in const eval of float: {ty:?}")
                };
                ConstVal::Float(float_ty, inst.data.float)
            }
            super::Tag::EnumLit => {
                let variant = String::from_utf8(ir.extra[
                    inst.data.extra_len.0 as usize
                    .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                ].to_vec()).expect("Enum variant was invalid utf8");
                ConstVal::EnumVariant(variant)
            }
            super::Tag::Func => {
                ConstVal::Symbol(ConstSymbol::Func(inst.data.symbol))
            }
            super::Tag::_TraitFunc => {
                let mut buf = [0; 8];
                buf.copy_from_slice(&ir.extra[inst.data.trait_func.0 as usize .. inst.data.trait_func.0 as usize + 8]);

                ConstVal::Symbol(ConstSymbol::TraitFunc(SymbolKey::from_bytes(buf), inst.data.trait_func.1))
            }
            super::Tag::Type => ConstVal::Symbol(ConstSymbol::Type(inst.data.symbol)),
            super::Tag::Trait => ConstVal::Symbol(ConstSymbol::Trait(inst.data.symbol)),
            super::Tag::LocalType => ConstVal::Symbol(ConstSymbol::LocalType(TypeTableIndex(inst.data.int32))),
            super::Tag::Module => ConstVal::Symbol(ConstSymbol::Module(ModuleId::new(inst.data.int32))),

            super::Tag::Decl => {
                let val = inst.data.un_op;
                values[pos as usize] = LocalVal::Var(get_ref(&values, val));
                pos += 1;
                continue;
            }
            super::Tag::Load => {
                let LocalVal::Var(val) = &values[inst.data.un_op.into_ref().unwrap() as usize]
                    else { panic!("not a variable") };
                val.clone()
            }
            super::Tag::Store => {
                let (var, val) = inst.data.bin_op;
                let val = get_ref(&values, val);
                let LocalVal::Var(current_val) = &mut values[var.into_ref().unwrap() as usize]
                    else { panic!("Var expected") };
                *current_val = val;
                ConstVal::Invalid
            }
            super::Tag::String => {
                let string = String::from_utf8_lossy(&ir.extra[
                    inst.data.extra_len.0 as usize
                    .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                ]);
                ConstVal::String(string.into_owned())
            }
            super::Tag::Call => {
                todo!();
            }
            super::Tag::Neg => {
                match get_ref(&values, inst.data.un_op) {
                    ConstVal::Invalid => ConstVal::Invalid,
                    ConstVal::Int(ty, val) => ConstVal::Int(ty, -val),
                    ConstVal::Float(ty, val) => ConstVal::Float(ty, -val),
                    _ => panic!("Invalid value to negate")
                }
            }
            super::Tag::Not => {
                let val = get_ref(&values, inst.data.un_op);
                let ConstVal::Bool(b) = val else { panic!("Invalid value for not") };
                ConstVal::Bool(!b)
            }
            super::Tag::Global => todo!(),
            super::Tag::Add => bin_op!(+, inst),
            super::Tag::Sub => bin_op!(-, inst),
            super::Tag::Mul => bin_op!(*, inst),
            super::Tag::Div => bin_op!(/, inst),
            super::Tag::Mod => bin_op!(%, inst),
            super::Tag::Or => {
                let (ConstVal::Bool(l), ConstVal::Bool(r)) = (
                    get_ref(&values, inst.data.bin_op.0),
                    get_ref(&values, inst.data.bin_op.1)
                ) else { panic!("Invalid values for or") };
                ConstVal::Bool(l || r)
            }
            super::Tag::And => {
                let (ConstVal::Bool(l), ConstVal::Bool(r)) = (
                    get_ref(&values, inst.data.bin_op.0),
                    get_ref(&values, inst.data.bin_op.1)
                ) else { panic!("Invalid values for and") };
                ConstVal::Bool(l && r)
            }
            //TODO: eq/ne should probably be implemented for more types
            super::Tag::Eq => {
                let l = get_ref(&values, inst.data.bin_op.0);
                let r = get_ref(&values, inst.data.bin_op.1);
                ConstVal::Bool(l.equal_to(&r, &ir.types))
            }
            super::Tag::Ne => {
                let l = get_ref(&values, inst.data.bin_op.0);
                let r = get_ref(&values, inst.data.bin_op.1);
                ConstVal::Bool(!l.equal_to(&r, &ir.types))
            }
            super::Tag::LT => cmp_op!(< , inst),
            super::Tag::GT => cmp_op!(> , inst),
            super::Tag::LE => cmp_op!(<=, inst),
            super::Tag::GE => cmp_op!(>=, inst),
            super::Tag::Member => {
                let ConstVal::Int(_, _member) = get_ref(&values, inst.data.bin_op.1)
                    else { panic!("member should be an int") };
                let LocalVal::Var(val) = &values[inst.data.bin_op.0.0 as usize]
                    else { panic!("Member used on non-variable" ) };

                match val {
                    ConstVal::Invalid => ConstVal::Invalid,
                    ConstVal::Symbol(_symbol) => todo!("does this make sense?"),
                    ConstVal::NotGenerated => panic!(),
                    _ => panic!("tried to take member of {val}")
                }
            }
            super::Tag::Cast => todo!(),
            super::Tag::AsPointer => todo!(),
            super::Tag::Goto => {
                let target = ir.blocks[inst.data.int32 as usize];
                eprintln!("{pos} -> {target}");
                if target <= pos {
                    backwards_jumps += 1;
                    if backwards_jumps > BACKWARDS_JUMP_LIMIT {
                        return Err(Error::InfiniteLoop)
                    }
                }
                pos = target;
                continue;
            }
            super::Tag::Branch => {
                let ConstVal::Bool(val) = get_ref(&values, inst.data.branch.0)
                    else { panic!("bool expected") };
                let i = inst.data.branch.1 as usize;
                let mut bytes = [0; 4];
                bytes.copy_from_slice(&ir.extra[i..i+4]);
                let a = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&ir.extra[i+4..i+8]);
                let b = u32::from_le_bytes(bytes);
                let target = if val { ir.blocks[a as usize] } else { ir.blocks[b as usize] };
                eprintln!("{pos} -> {target} (branch: {val})");
                if target <= pos {
                    backwards_jumps += 1;
                    if backwards_jumps > BACKWARDS_JUMP_LIMIT {
                        return Err(Error::InfiniteLoop)
                    }
                }
                pos = target;
                continue;

            }
            super::Tag::Phi => {
                let mut val = None;
                for i in 0..inst.data.extra_len.1 {
                    let mut current_bytes = [0; 4];
                    let begin = (inst.data.extra_len.0 + i * 8) as usize;
                    current_bytes.copy_from_slice(&ir.extra[begin..begin + 4]);
                    let block = BlockIndex(u32::from_le_bytes(current_bytes));
                    current_bytes.copy_from_slice(&ir.extra[begin + 4 .. begin + 8]);
                    current_bytes.copy_from_slice(&ir.extra[begin + 4 .. begin + 8]);
                    let r = Ref::from_bytes(current_bytes);
                    if block == previous_block {
                        val = Some(get_ref(&values, r));
                        break;
                    }
                }
                val.expect("Invalid phi node: didn't go through any of the blocks")
            }
            super::Tag::Asm => todo!(),
        });
        pos += 1;
    };
    Ok(val)
}