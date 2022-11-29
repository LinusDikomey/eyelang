use crate::{ir::{Ref, BlockIndex}, error::Error, ast::{ModuleId, TraitId}, resolve::{consts::ConstSymbol, type_info::TypeTableIndex}};

use super::ConstVal;
use crate::resolve::type_info::TypeInfo;

#[derive(Clone, Debug)]
enum LocalVal {
    Val(ConstVal),
    Var(ConstVal),
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

/*
pub fn eval(ir: &super::IrBuilder, params: &[ConstVal]) -> Result<ConstVal, Error> {
    let mut stack = StackMem::new();
    unsafe {
        eval_internal(ir, params, stack.new_frame())
    }
}

// TODO: give errors a span by giving all IR instructions spans.
unsafe fn eval_internal(ir: &super::IrBuilder, _params: &[ConstVal], _frame: StackFrame) -> Result<ConstVal, Error> {
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

            match &ir.ir_types[$inst.ty] {
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
            super::Tag::Param => todo!("should give pointer to param"), //params[inst.data.int32 as usize].clone(),
            super::Tag::Uninit => ConstVal::Invalid,
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
            super::Tag::Func => {
                ConstVal::Symbol(ConstSymbol::Func(inst.data.func_symbol))
            }
            super::Tag::TraitFunc => {
                let mut buf = [0; 8];
                buf.copy_from_slice(&ir.extra[inst.data.trait_func.0 as usize .. inst.data.trait_func.0 as usize + 8]);

                ConstVal::Symbol(ConstSymbol::TraitFunc(TraitId::from_bytes(buf), inst.data.trait_func.1))
            }
            super::Tag::Type => ConstVal::Symbol(ConstSymbol::Type(inst.data.type_symbol)),
            super::Tag::Trait => ConstVal::Symbol(ConstSymbol::Trait(inst.data.trait_symbol)),
            super::Tag::LocalType => ConstVal::Symbol(ConstSymbol::LocalType(TypeTableIndex(inst.data.int32))),
            super::Tag::Module => ConstVal::Symbol(ConstSymbol::Module(ModuleId::new(inst.data.int32))),

            super::Tag::Decl => {
                values[pos as usize] = LocalVal::Var(ConstVal::Invalid);
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
                ConstVal::Invalid
            }
            super::Tag::String => {
                let string = ir.extra[
                    inst.data.extra_len.0 as usize
                    .. (inst.data.extra_len.0 + inst.data.extra_len.1) as usize
                ].to_vec();
                ConstVal::String(string)
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
            super::Tag::NE => {
                let l = get_ref(&values, inst.data.bin_op.0);
                let r = get_ref(&values, inst.data.bin_op.1);
                ConstVal::Bool(!l.equal_to(&r, &ir.types))
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
                let ConstVal::Bool(val) = get_ref(&values, inst.data.ref_int.0)
                    else { panic!("bool expected") };
                let i = inst.data.ref_int.1 as usize;
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

*/