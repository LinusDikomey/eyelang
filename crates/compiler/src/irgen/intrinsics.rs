use ir::{builder::BinOp, IrType, Ref};

use super::{Ctx, ValueOrPlace};

pub fn call_intrinsic(
    ctx: &mut Ctx,
    intrinsic: &str,
    args: &[Ref],
    return_ty: IrType,
) -> super::Result<ValueOrPlace> {
    Ok(ValueOrPlace::Value(match intrinsic {
        "xor" => ctx
            .builder
            .build_bin_op(BinOp::Xor, args[0], args[1], return_ty),
        "rotate_left" => ctx
            .builder
            .build_bin_op(BinOp::Rol, args[0], args[1], return_ty),
        "rotate_right" => ctx
            .builder
            .build_bin_op(BinOp::Ror, args[0], args[1], return_ty),
        _ => panic!("called unknown intrinsic: {intrinsic}"),
    }))
}
