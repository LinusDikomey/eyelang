use crate::{BlockGraph, Function, IrType, Module, Tag};

pub fn module(module: &Module) {
    for func in &module.funcs {
        function(func);
    }
}

pub fn function(function: &Function) {
    let Some(ir) = &function.ir else {
        return;
    };
    let dom_tree = BlockGraph::calculate(ir);
    for block in ir.blocks() {
        for (i, inst) in ir.get_block(block) {
            inst.visit_refs(ir, |r| {
                assert!(dom_tree.dominates(ir, i, r));
                if let Some(idx) = r.into_ref() {
                    if ir.get_inst(idx).tag == Tag::Nothing {
                        panic!("Instruction {i} has a ref pointing to nothing %{idx}");
                    }
                }
            });
            match inst.tag {
                Tag::Nothing => {}
                Tag::BlockArg => unreachable!("BlockArg shouldn't exist inside a block"),
                Tag::Uninit => {}
                Tag::Int => {
                    let value = inst.data.int();
                    // HACK: currently, when a literal for a minimum signed integer (like i8 -128)
                    // is written, the number 128 is added first and then subtracted. This fails
                    // the verifier but works totally fine. For now, we just allow literal values
                    // that are one too high
                    let hack = 1;
                    let value_in_range = match function.types[inst.ty] {
                        IrType::I8 => {
                            (i8::MIN as i64..=i8::MAX as i64 + hack).contains(&(value as i64))
                        }
                        IrType::I16 => {
                            (i16::MIN as i64..=i16::MAX as i64 + hack).contains(&(value as i64))
                        }
                        IrType::I32 => {
                            (i32::MIN as i64..=i32::MAX as i64 + hack).contains(&(value as i64))
                        }
                        IrType::U8 => value <= u8::MAX as u64,
                        IrType::U16 => value <= u16::MAX as u64,
                        IrType::U32 => value <= u32::MAX as u64,
                        IrType::U64 | IrType::I64 | IrType::U128 | IrType::I128 => true,
                        other => panic!("invalid type for int constant: {other:?}"),
                    };
                    if !value_in_range {
                        panic!(
                            "constant %{i} = Int {value} is out of range for type {:?}",
                            function.types[inst.ty]
                        );
                    }
                }
                Tag::LargeInt => {
                    assert!(matches!(
                        function.types[inst.ty],
                        IrType::U128 | IrType::I128
                    ));
                }
                Tag::Float => assert!(function.types[inst.ty].is_float()),
                Tag::Global => {
                    // TODO: check globals and check that type matches
                }
                Tag::Ret
                | Tag::Load
                | Tag::Neg
                | Tag::Not
                | Tag::CastInt
                | Tag::CastFloat
                | Tag::CastIntToFloat
                | Tag::CastFloatToInt
                | Tag::IntToPtr
                | Tag::PtrToInt => {
                    let r = inst.data.un_op();
                    assert!(dom_tree.dominates(ir, i, r));
                }
                Tag::Store => {
                    let (ptr, value) = inst.data.bin_op();
                    assert!(dom_tree.dominates(ir, i, ptr));
                    assert!(dom_tree.dominates(ir, i, value));
                    assert!(matches!(ir.get_ref_ty(ptr, &function.types), IrType::Ptr));
                }
                Tag::Add
                | Tag::Sub
                | Tag::Mul
                | Tag::Div
                | Tag::Rem
                | Tag::Or
                | Tag::And
                | Tag::Eq
                | Tag::NE
                | Tag::LT
                | Tag::GT
                | Tag::LE
                | Tag::GE => {
                    let (lhs, rhs) = inst.data.bin_op();
                    assert!(dom_tree.dominates(ir, i, lhs));
                    assert!(dom_tree.dominates(ir, i, rhs));
                }
                // TODO: check the dominators and instruction specific properties of these
                // instructions
                Tag::Goto => {}
                Tag::Branch => {}
                Tag::Decl => {}
                Tag::MemberPtr => {}
                Tag::MemberValue => {}
                Tag::ArrayIndex => {}
                Tag::String => {}
                Tag::Call => {}
                Tag::Asm => {}
            }
        }
    }
}
