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
        let mut block_insts = ir.get_block(block).peekable();
        while let Some((_, inst)) =
            block_insts.next_if(|(_, inst)| matches!(inst.tag, Tag::Param | Tag::Phi))
        {
            match inst.tag {
                Tag::Param => {
                    let param_index = unsafe { inst.data.int32 };
                    if param_index >= function.params.count {
                        panic!("Param index {param_index} is out of bounds, the function only has {} params", function.params.len());
                    }
                    let signature_type = function.params.nth(param_index);
                    assert!(
                        function
                            .types
                            .are_equal(function.types[signature_type], function.types[inst.ty]),
                        "Mismatch between function type and Param type"
                    );
                }
                Tag::Phi => {
                    let args = inst.data.phi(&ir.extra);
                    let arg_count = args.len();
                    for (phi_block, r) in args {
                        assert!(dom_tree.preceeds(block, phi_block));
                        if let Some(r_index) = r.into_ref() {
                            assert!(dom_tree
                                .block_dominates(phi_block, ir.get_block_from_index(r_index)));
                        }
                    }
                    assert_eq!(
                        arg_count,
                        dom_tree.pred_count(block),
                        "Phi doesn't contain all pred blocks"
                    );
                }
                _ => unreachable!(),
            }
        }
        for (i, inst) in block_insts {
            match inst.tag {
                Tag::Param => panic!("Param should only be at the start of the block"),
                Tag::Phi => panic!("Phi should only be at the start of the block"),
                Tag::Uninit => {}
                Tag::Int => {
                    let value = inst.data.int();
                    let value_in_range = match function.types[inst.ty] {
                        IrType::I8 => (i8::MIN as i64..=i8::MAX as i64).contains(&(value as i64)),
                        IrType::I16 => {
                            (i16::MIN as i64..=i16::MAX as i64).contains(&(value as i64))
                        }
                        IrType::I32 => {
                            (i32::MIN as i64..=i32::MAX as i64).contains(&(value as i64))
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
                | Tag::Mod
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
