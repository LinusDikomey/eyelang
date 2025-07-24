use std::convert::Infallible;

use ir::{BlockId, Environment, MCReg, ModuleOf, Primitive, Ref, Type, TypeId, Types, mc::Mc};

use crate::arch::x86::{X86, isa::Reg};

use super::Abi;

const ABI_PARAM_REGISTERS: [[Reg; 4]; 6] = [
    [Reg::rdi, Reg::edi, Reg::di, Reg::dl],
    [Reg::rsi, Reg::esi, Reg::si, Reg::sil],
    [Reg::rdx, Reg::edx, Reg::dx, Reg::dl],
    [Reg::rcx, Reg::ecx, Reg::cx, Reg::cl],
    [Reg::r8, Reg::r8d, Reg::r8w, Reg::r8b],
    [Reg::r9, Reg::r9d, Reg::r9w, Reg::r9b],
];
const RETURN_REGS: [[Reg; 4]; 2] = [
    [Reg::rax, Reg::eax, Reg::ax, Reg::al],
    [Reg::rdx, Reg::edx, Reg::dx, Reg::dl],
];

pub struct SystemV;
impl Abi<X86> for SystemV {
    fn implement_params(
        &self,
        args: ir::Refs,
        ir: &mut ir::modify::IrModify,
        env: &Environment,
        mc: ModuleOf<Mc>,
        types: &Types,
        regs: &ir::slots::Slots<MCReg>,
        unit: TypeId,
    ) {
        let info = ir.get_block(BlockId::ENTRY);
        let before = Ref::index(info.idx + info.arg_count);
        let mut abi_regs = ABI_PARAM_REGISTERS.into_iter();
        for arg in args.iter() {
            _ = regs.visit_primitive_slots::<Infallible, _>(
                arg,
                types[ir.get_ref_ty(arg)],
                types,
                |regs, ty| {
                    let mut copy = |args| {
                        ir.add_before(env, before, ir::mc::parallel_copy(mc, args, unit));
                    };
                    match ty {
                        Primitive::Unit => {}
                        Primitive::I1 | Primitive::I8 | Primitive::U8 => {
                            copy(&[regs[0], MCReg::from_phys(abi_regs.next().unwrap()[3])]);
                        }
                        Primitive::I16 | Primitive::U16 => {
                            copy(&[regs[0], MCReg::from_phys(abi_regs.next().unwrap()[2])]);
                        }
                        Primitive::I32 | Primitive::U32 => {
                            copy(&[regs[0], MCReg::from_phys(abi_regs.next().unwrap()[1])]);
                        }
                        Primitive::I64 | Primitive::U64 | Primitive::Ptr => {
                            copy(&[regs[0], MCReg::from_phys(abi_regs.next().unwrap()[0])]);
                        }
                        Primitive::I128 | Primitive::U128 => {
                            copy(&[
                                regs[0],
                                MCReg::from_phys(abi_regs.next().unwrap()[0]),
                                regs[1],
                                MCReg::from_phys(abi_regs.next().unwrap()[1]),
                            ]);
                        }
                        Primitive::F32 | Primitive::F64 => todo!("SystemV float parameter abi"),
                    }
                    Ok(())
                },
            );
        }
    }

    fn implement_return(
        &self,
        value: ir::Ref,
        ir: &mut ir::modify::IrModify,
        env: &Environment,
        mc: ModuleOf<Mc>,
        x86: ModuleOf<X86>,
        types: &Types,
        regs: &ir::slots::Slots<MCReg>,
        r: ir::Ref,
        unit: TypeId,
    ) {
        let ty = types[ir.get_ref_ty(value)];
        let mut copy = |args| ir.add_before(env, r, ir::mc::parallel_copy(mc, args, unit));
        match ty {
            Type::Primitive(p) => match Primitive::try_from(p).unwrap() {
                Primitive::Unit => ir.replace(env, r, x86.ret0(unit)),
                Primitive::I1 | Primitive::I8 | Primitive::U8 => {
                    copy(&[MCReg::from_phys(RETURN_REGS[0][3]), regs.get_one(value)]);
                    ir.replace(env, r, x86.ret64(unit));
                }
                Primitive::I16 | Primitive::U16 => {
                    copy(&[MCReg::from_phys(RETURN_REGS[0][2]), regs.get_one(value)]);
                    ir.replace(env, r, x86.ret64(unit));
                }
                Primitive::I32 | Primitive::U32 => {
                    copy(&[MCReg::from_phys(RETURN_REGS[0][1]), regs.get_one(value)]);
                    ir.replace(env, r, x86.ret64(unit));
                }
                Primitive::I64 | Primitive::U64 | Primitive::Ptr => {
                    copy(&[MCReg::from_phys(RETURN_REGS[0][0]), regs.get_one(value)]);
                    ir.replace(env, r, x86.ret64(unit));
                }
                Primitive::I128 | Primitive::U128 => {
                    let &[a, b] = regs.get(value) else {
                        unreachable!()
                    };
                    copy(&[
                        MCReg::from_phys(RETURN_REGS[0][0]),
                        a,
                        MCReg::from_phys(RETURN_REGS[1][0]),
                        b,
                    ]);
                    ir.replace(env, r, x86.ret128(unit));
                }
                Primitive::F32 | Primitive::F64 => todo!("abi: float return values"),
            },
            Type::Array(_, _) => todo!("abi: array return values"),
            Type::Tuple(_) => todo!("abi: tuple return values"),
        }
    }
}
