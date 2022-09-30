use crate::ir::{Ref, RefVal, ConstVal};
use super::{IrBuilder, expr::ExprInfo, ConstSymbol, ExprResult};


pub(super) fn to_expr_result(val: &ConstVal, ir: &mut IrBuilder, info: ExprInfo) -> ExprResult {
    // TODO: specify types here
    ExprResult::Val(match val {
        &ConstVal::Symbol(symbol) => {
            return match symbol {
                ConstSymbol::Func(key) => ExprResult::Symbol(ConstSymbol::Func(key)),
                ConstSymbol::Type(key) => ExprResult::Symbol(ConstSymbol::Type(key)),
                ConstSymbol::Trait(key) => ExprResult::Symbol(ConstSymbol::Trait(key)),
                ConstSymbol::LocalType(..) => unreachable!(),
                ConstSymbol::Module(key) => ExprResult::Symbol(ConstSymbol::Module(key)),
                ConstSymbol::TraitFunc(trait_symbol, func_idx) => {
                    ExprResult::Symbol(ConstSymbol::TraitFunc(trait_symbol, func_idx))
                }
            }
        }
        ConstVal::Invalid => Ref::UNDEF,
        ConstVal::Unit => Ref::UNIT,
        ConstVal::Int(_, val) => {
            if *val > u64::MAX as i128 || *val < -(u64::MAX as i128) {
                todo!("Large ints aren't implemented");
            }
            if *val < 0 {
                let positive_val = ir.build_int(-*val as u64, info.expected);
                ir.build_neg(positive_val, info.expected)
            } else {
                ir.build_int(*val as u64, info.expected)
            }
        }
        ConstVal::Float(_, val) => ir.build_float(*val, info.expected),
        ConstVal::String(val) => {
            ir.build_string(val, false, info.expected)
        }
        ConstVal::EnumVariant(variant) => {
            ir.build_enum_lit(variant, info.expected)
        }
        ConstVal::Bool(false) => Ref::val(RefVal::False),
        ConstVal::Bool(true) => Ref::val(RefVal::True),
        ConstVal::NotGenerated { .. } => todo!("Handle recursive const evaluation"),
    })
}