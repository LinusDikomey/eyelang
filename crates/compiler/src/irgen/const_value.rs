use crate::eval;

pub fn translate(value: &eval::ConstValue) -> ir::ConstValue {
    match value {
        eval::ConstValue::Undefined => ir::ConstValue::Undefined,
        eval::ConstValue::Unit => ir::ConstValue::Unit,
        &eval::ConstValue::Bool(b) => ir::ConstValue::Int(b as i64),
        &eval::ConstValue::Int(val, _) => ir::ConstValue::Int(val as i64),
        &eval::ConstValue::Float(val, _) => ir::ConstValue::Float(val),
    }
}
