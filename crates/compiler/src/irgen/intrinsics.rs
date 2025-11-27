use ir::Ref;

use super::{Ctx, ValueOrPlace};

pub fn call_intrinsic(ctx: &mut Ctx, intrinsic: &str, args: &[Ref]) -> super::Result<ValueOrPlace> {
    let crate::compiler::Dialects { arith, .. } = ctx.dialects;
    Ok(ValueOrPlace::Value(match intrinsic {
        "eq" => {
            let bool = ctx.builder.types.add(ir::Type::from(ir::Primitive::I1));
            ctx.builder.append(arith.Eq(args[0], args[1], bool))
        }
        "xor" => ctx
            .builder
            .append(arith.Xor(args[0], args[1], ctx.builder.get_ref_ty(args[0]))),
        "rotate_left" => {
            ctx.builder
                .append(arith.Rol(args[0], args[1], ctx.builder.get_ref_ty(args[0])))
        }
        "rotate_right" => {
            ctx.builder
                .append(arith.Ror(args[0], args[1], ctx.builder.get_ref_ty(args[0])))
        }
        _ => panic!("called unknown intrinsic: {intrinsic}"),
    }))
}
