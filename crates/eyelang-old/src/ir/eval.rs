use crate::{
    ir::{Ref, BlockIndex},
    error::Error,
    ast::{ModuleId, TraitId},
    resolve::const_val::{ConstSymbol, ConstItem},
    ir::types::ConstIrType,
};

use super::{ConstVal, builder::IrBuilder, types::IrType};

#[derive(Clone, Debug)]
enum LocalVal {
    Val(ConstItem),
    Var(ConstItem),
}

struct StackMem {
    mem: Vec<u8>,
}
impl StackMem {
    pub fn new() -> StackMem {
        Self {
            mem: vec![],
        }
    }
    pub fn new_frame(&mut self) -> StackFrame {
        let base_pointer = self.mem.len();
        StackFrame { mem: self, base_pointer, alloc_count: 0 }
    }
}

// TODO: integrate this to have proper memory when evaluating at comptime
struct StackFrame<'a> {
    mem: &'a mut StackMem,
    base_pointer: usize,
    alloc_count: usize, // just for debugging
}
impl<'a> StackFrame<'a> {
    fn _new_frame<'b: 'a>(&'b mut self) -> StackFrame<'b> {
        self.mem.new_frame()
    }
    fn _alloc(&mut self, count: usize) -> usize {
        self.alloc_count += count;
        let idx = self.mem.mem.len();
        self.mem.mem.extend((0..count).map(|_| 0));
        idx
    }
}
impl<'a> Drop for StackFrame<'a> {
    fn drop(&mut self) {
        debug_assert_eq!(self.mem.mem.len() - self.alloc_count, self.base_pointer);
        self.mem.mem.truncate(self.base_pointer);
    }
}

pub static mut BACKWARDS_JUMP_LIMIT: usize = 1000;

pub fn eval(ir: &IrBuilder, params: &[ConstVal]) -> Result<ConstItem, Error> {
    let mut stack = StackMem::new();
    let val = unsafe { eval_internal(ir, params, stack.new_frame()) }?;
    assert!(
        !matches!(val, ConstItem::Val(ConstVal::Invalid)),
        "Constant evaluation yielded an invalid value, this is probably an internal error",
    );
    Ok(val)
}

// TODO: give errors a span by giving all IR instructions spans.
unsafe fn eval_internal(ir: &IrBuilder, _params: &[ConstVal], _frame: StackFrame) -> Result<ConstItem, Error> {
    let mut values = vec![LocalVal::Val(ConstItem::Val(ConstVal::Invalid)); ir.inst.len()];

    fn get_ref(values: &[LocalVal], r: Ref) -> ConstItem {
        if let Some(r) = r.into_ref() {
            match &values[r as usize] {
                LocalVal::Val(v) => v.clone(),
                LocalVal::Var(_) => panic!("Unexpected variable reference"),
            }
        } else {
            ConstItem::Val(match r.into_val().unwrap() {
                crate::ir::RefVal::True => ConstVal::Bool(true),
                crate::ir::RefVal::False => ConstVal::Bool(false),
                crate::ir::RefVal::Unit => ConstVal::Unit,
                crate::ir::RefVal::Undef => ConstVal::Invalid,
            })
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

            match ir.types[$inst.ty] {
                IrType::Primitive(p) if p.is_int() => {
                    let ConstItem::Val(ConstVal::Int(l_ty, l_val)) = l else { panic!() };
                    let ConstItem::Val(ConstVal::Int(r_ty, r_val)) = r else { panic!() };
                    let ty = p.as_int().unwrap();
                    assert!(match l_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    assert!(match r_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    ConstItem::Val(ConstVal::Int(Some(ty), l_val $op r_val))
                }
                IrType::Const(ConstIrType::Int) => {
                    let ConstItem::Val(ConstVal::Int(l_ty, l_val)) = l else { panic!() };
                    let ConstItem::Val(ConstVal::Int(r_ty, r_val)) = r else { panic!() };
                    assert!(l_ty.is_none());
                    assert!(r_ty.is_none());
                    ConstItem::Val(ConstVal::Int(None, l_val $op r_val))
                }
                IrType::Primitive(p) if p.is_float() => {
                    let ConstItem::Val(ConstVal::Float(l_ty, l_val)) = l else { panic!() };
                    let ConstItem::Val(ConstVal::Float(r_ty, r_val)) = r else { panic!() };
                    let ty = p.as_float().unwrap();
                    debug_assert!(match l_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    debug_assert!(match r_ty {
                        Some(t) => t == ty,
                        None => true
                    });
                    ConstItem::Val(ConstVal::Float(Some(ty), l_val $op r_val))                        
                }
                IrType::Const(ConstIrType::Float) => {
                    let ConstItem::Val(ConstVal::Float(l_ty, l_val)) = l else { panic!() };
                    let ConstItem::Val(ConstVal::Float(r_ty, r_val)) = r else { panic!() };
                    assert!(l_ty.is_none());
                    assert!(r_ty.is_none());
                    ConstItem::Val(ConstVal::Float(None, l_val $op r_val))
                }
                t => panic!("Invalid type for binary operation: {t:?}")
            }
        }};
    }
    macro_rules! cmp_op {
        ($op: tt, $inst: expr) => {{
            let ConstItem::Val(l) = get_ref(&values, $inst.data.bin_op.0) else { unreachable!() };
            let ConstItem::Val(r) = get_ref(&values, $inst.data.bin_op.1) else { unreachable!() };

            ConstItem::Val(match (l, r) {
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
            })
        }};
    }

    let val = loop {
        let inst = ir.inst[pos as usize];
        values[pos as usize] = LocalVal::Val(match inst.tag {
            super::Tag::BlockBegin => {
                previous_block = current_block;
                current_block = inst.data.block;
                ConstItem::Val(ConstVal::Invalid)
            }
            super::Tag::Ret => break get_ref(&values, inst.data.un_op),
            super::Tag::Param => todo!("should give pointer to param"),
            super::Tag::Uninit => ConstItem::Val(ConstVal::Invalid),
            super::Tag::Int => {
                let int_ty = match ir.types[inst.ty] {
                    IrType::Primitive(p) if p.is_int() => Some(p.as_int().unwrap()),
                    IrType::Const(ConstIrType::Int) => None,
                    _ => panic!("invalid type in const eval")
                };
                ConstItem::Val(ConstVal::Int(int_ty, inst.data.int as _))
            }
            super::Tag::LargeInt => {
                let int_ty = match ir.types[inst.ty] {
                    IrType::Primitive(p) if p.is_int() => Some(p.as_int().unwrap()),
                    IrType::Const(ConstIrType::Int) => None,
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
                    ConstItem::Val(ConstVal::Int(int_ty, int))
            }
            super::Tag::Float => {
                let float_ty = match &ir.types[inst.ty] {
                    IrType::Primitive(p) if p.is_float() => Some(p.as_float().unwrap()),
                    IrType::Const(ConstIrType::Float) => None,
                    ty => panic!("invalid type in const eval of float: {ty:?}")
                };
                ConstItem::Val(ConstVal::Float(float_ty, inst.data.float))
            }
            super::Tag::Func => {
                ConstItem::Symbol(ConstSymbol::Func(inst.data.func_symbol))
            }
            super::Tag::TraitFunc => {
                let mut buf = [0; 8];
                buf.copy_from_slice(&ir.extra[inst.data.trait_func.0 as usize .. inst.data.trait_func.0 as usize + 8]);

                ConstItem::Symbol(ConstSymbol::TraitFunc(TraitId::from_bytes(buf), inst.data.trait_func.1))
            }
            super::Tag::Type => ConstItem::Val(ConstVal::Type(ir.types[inst.data.ty].as_resolved_type(&ir.types))),
            super::Tag::Trait => ConstItem::Symbol(ConstSymbol::Trait(inst.data.trait_symbol)),
            super::Tag::Module => ConstItem::Symbol(ConstSymbol::Module(ModuleId::new(inst.data.int32))),

            super::Tag::Decl => {
                values[pos as usize] = LocalVal::Var(ConstItem::Val(ConstVal::Invalid));
                pos += 1;
                continue;
            }
            super::Tag::Load => {
                match &values[inst.data.un_op.into_ref().unwrap() as usize] {
                    LocalVal::Var(val) => {
                        val.clone()
                    }
                    _ => panic!("not a variable")
                }
            }
            super::Tag::Store => {
                let (var, val) = inst.data.bin_op;
                let val = get_ref(&values, val);
                match &mut values[var.into_ref().unwrap() as usize] {
                    LocalVal::Var(current_val) => *current_val = val,
                    LocalVal::Val(_) => panic!("can't store in val")
                }
                ConstItem::Val(ConstVal::Invalid)
            }
            super::Tag::String => {
                let string = ir.extra[
                    inst.data.extra_len.0 as usize
                    .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                ].to_vec();
                ConstItem::Val(ConstVal::String(string))
            }
            super::Tag::Call => {
                todo!();
            }
            super::Tag::Neg => {
                ConstItem::Val(match get_ref(&values, inst.data.un_op) {
                    ConstItem::Val(ConstVal::Invalid) => ConstVal::Invalid,
                    ConstItem::Val(ConstVal::Int(ty, val)) => ConstVal::Int(ty, -val),
                    ConstItem::Val(ConstVal::Float(ty, val)) => ConstVal::Float(ty, -val),
                    _ => panic!("Invalid value to negate")
                })
            }
            super::Tag::Not => {
                let val = get_ref(&values, inst.data.un_op);
                let ConstItem::Val(ConstVal::Bool(b)) = val else { panic!("Invalid value for not") };
                ConstItem::Val(ConstVal::Bool(!b))
            }
            super::Tag::Global => todo!(),
            super::Tag::Add => bin_op!(+, inst),
            super::Tag::Sub => bin_op!(-, inst),
            super::Tag::Mul => bin_op!(*, inst),
            super::Tag::Div => bin_op!(/, inst),
            super::Tag::Mod => bin_op!(%, inst),
            super::Tag::Or => {
                let (ConstItem::Val(ConstVal::Bool(l)), ConstItem::Val(ConstVal::Bool(r))) = (
                    get_ref(&values, inst.data.bin_op.0),
                    get_ref(&values, inst.data.bin_op.1)
                ) else { panic!("Invalid values for or") };
                ConstItem::Val(ConstVal::Bool(l || r))
            }
            super::Tag::And => {
                let (ConstItem::Val(ConstVal::Bool(l)), ConstItem::Val(ConstVal::Bool(r))) = (
                    get_ref(&values, inst.data.bin_op.0),
                    get_ref(&values, inst.data.bin_op.1)
                ) else { panic!("Invalid values for and") };
                ConstItem::Val(ConstVal::Bool(l && r))
            }
            //TODO: eq/ne should probably be implemented for more types
            super::Tag::Eq => {
                let l = get_ref(&values, inst.data.bin_op.0);
                let r = get_ref(&values, inst.data.bin_op.1);
                ConstItem::Val(ConstVal::Bool(l.equal_to(&r, &ir.types)))
            }
            super::Tag::NE => {
                let l = get_ref(&values, inst.data.bin_op.0);
                let r = get_ref(&values, inst.data.bin_op.1);
                ConstItem::Val(ConstVal::Bool(!l.equal_to(&r, &ir.types)))
            }
            super::Tag::LT => cmp_op!(< , inst),
            super::Tag::GT => cmp_op!(> , inst),
            super::Tag::LE => cmp_op!(<=, inst),
            super::Tag::GE => cmp_op!(>=, inst),
            super::Tag::Member => {
                todo!("should give pointer to member")
                /*
                let ConstVal::Int(_, member) = get_ref(&values, inst.data.bin_op.1)
                    else { panic!("member should be an int") };
                let var_idx = inst.data.bin_op.0.into_ref().expect("Can't get member of value");
                values[pos as usize] = match &values[var_idx as usize] {
                    LocalVal::Val(_) => panic!("Member used on value '{:?}'", values[var_idx as usize]),
                    LocalVal::Var(_) => LocalVal::VarMember(var_idx, vec![member as u32]),
                    LocalVal::VarMember(idx, members) => LocalVal::VarMember(
                        *idx,
                        members.iter().copied().chain([member as _]).collect()
                    ),
                };
                pos += 1;
                continue;
                */
            }
            super::Tag::Value => todo!(),
            super::Tag::Cast => todo!(),
            super::Tag::Goto => {
                let target = ir.blocks[inst.data.int32 as usize];
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
                let ConstItem::Val(ConstVal::Bool(val)) = get_ref(&values, inst.data.ref_int.0)
                    else { panic!("bool expected") };
                let i = inst.data.ref_int.1 as usize;
                let mut bytes = [0; 4];
                bytes.copy_from_slice(&ir.extra[i..i+4]);
                let a = u32::from_le_bytes(bytes);
                bytes.copy_from_slice(&ir.extra[i+4..i+8]);
                let b = u32::from_le_bytes(bytes);
                let target = if val { ir.blocks[a as usize] } else { ir.blocks[b as usize] };
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
            super::Tag::EnumTag | super::Tag::EnumValueTag
            | super::Tag::EnumVariantMember | super::Tag::EnumValueVariantMember 
            => todo!("eval enums"),
        });
        pos += 1;
    };
    Ok(val)
}
