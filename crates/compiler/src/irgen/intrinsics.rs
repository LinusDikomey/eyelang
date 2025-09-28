use ir::{Ref, TypeId};

use super::{Ctx, ValueOrPlace};

pub fn call_intrinsic(
    ctx: &mut Ctx,
    intrinsic: &str,
    args: &[Ref],
    return_ty: TypeId,
) -> super::Result<ValueOrPlace> {
    let crate::compiler::Dialects { arith, .. } = ctx.dialects;
    Ok(ValueOrPlace::Value(match intrinsic {
        "xor" => ctx.builder.append(arith.Xor(args[0], args[1], return_ty)),
        "rotate_left" => ctx.builder.append(arith.Rol(args[0], args[1], return_ty)),
        "rotate_right" => ctx.builder.append(arith.Ror(args[0], args[1], return_ty)),
        _ => panic!("called unknown intrinsic: {intrinsic}"),
    }))
}
