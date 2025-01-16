use crate::Layout;

use super::{MirBlock, RegClass, Register, VReg, VRegs};

use super::{Instruction, InstructionStorage, MachineIR, Op};

pub struct BlockBuilder<'a, I: Instruction> {
    pub(super) mir: &'a mut MachineIR<I>,
    pub(super) block: MirBlock,
}
impl<I: Instruction> BlockBuilder<'_, I> {
    pub fn next_inst_index(&self) -> u32 {
        self.mir.insts.len() as u32
    }

    #[cfg_attr(debug_assertions, track_caller)]
    /// appends an instruction to the MachineIR
    pub fn inst<const N: usize>(&mut self, inst: I, operands: [Op<I::Register>; N]) {
        self.mir.blocks[self.block.0 as usize].len += 1;
        #[cfg(debug_assertions)]
        {
            let expected = inst.ops();
            let mut found = [crate::mc::OpType::Non; 4];
            found[..N].copy_from_slice(&operands.map(|op| op.op_type()));
            if expected != found {
                panic!("invalid operands to instruction {}", inst.to_str());
            }
        }
        let mut all_operands = [0; 4];
        all_operands[..operands.len()].copy_from_slice(&operands.map(|op| op.encode()));
        self.mir.insts.push(InstructionStorage {
            inst,
            ops: all_operands,
            implicit_dead: I::Register::NO_BITS,
        });
    }

    /// create a copy instruction
    pub fn copy(&mut self, to: Op<I::Register>, from: Op<I::Register>) {
        self.inst(I::COPY, [to, from]);
    }

    /// create a copy into a newly created virtual register
    pub fn copy_to_fresh(&mut self, from: Op<I::Register>, class: RegClass) -> VReg {
        let vreg = self.reg(class);
        self.copy(vreg.op(), from);
        vreg
    }

    /// create a phi instruction given the phi operands ordered by the predecessor block
    pub fn build_copyargs(
        &mut self,
        copyarg_inst: I,
        to: impl IntoIterator<Item = Op<I::Register>>,
        from: impl IntoIterator<Item = Op<I::Register>>,
    ) {
        let extra_idx = self.mir.extra_ops.len();
        self.mir.extra_ops.extend(to);
        let count = self.mir.extra_ops.len() - extra_idx;
        self.mir.extra_ops.extend(from);
        debug_assert_eq!(count, self.mir.extra_ops.len() - count - extra_idx);
        if count != 0 {
            self.mir.blocks[self.block.0 as usize].len += 1;
            self.mir.insts.push(InstructionStorage {
                inst: copyarg_inst,
                ops: [extra_idx as u64, count as u64, 0, 0],
                implicit_dead: I::Register::NO_BITS,
            });
        }
    }

    pub fn register_successor(&mut self, successor: MirBlock) {
        self.mir.blocks[self.block.0 as usize]
            .successors
            .push(successor);
    }

    /// creates a fresh virtual register
    pub fn reg(&mut self, class: RegClass) -> VReg {
        self.mir.reg(class)
    }

    pub fn create_stack_slot(&mut self, layout: Layout) -> u32 {
        self.mir.create_stack_slot(layout)
    }

    pub fn create_block(
        &mut self,
        block_args: impl IntoIterator<Item = RegClass>,
    ) -> (MirBlock, VRegs) {
        self.mir.create_block(block_args)
    }
}
