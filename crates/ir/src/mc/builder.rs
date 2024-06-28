use crate::Layout;

use super::{MirBlock, OpType, Register, VReg};

use super::{Instruction, InstructionStorage, MachineIR, Op};

pub struct BlockBuilder<'a, I: Instruction> {
    pub(super) mir: &'a mut MachineIR<I>,
    pub(super) block: MirBlock,
}
impl<'a, I: Instruction> BlockBuilder<'a, I> {
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
            let mut found = [OpType::Non; 4];
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

    /// create a phi instruction given the phi operands ordered by the predecessor block
    pub fn build_phi(
        &mut self,
        phi_inst: I,
        args: impl IntoIterator<Item = Op<I::Register>>,
    ) -> VReg {
        let r = self.reg();
        // TODO
        self.mir.insts.push(InstructionStorage {
            inst: phi_inst,
            ops: [Op::<I::Register>::VReg(r).encode(), 0, 0, 0],
            implicit_dead: I::Register::NO_BITS,
        });
        r
    }

    pub fn register_successor(&mut self, successor: MirBlock) {
        self.mir.blocks[self.block.0 as usize]
            .successors
            .push(successor);
    }

    /// creates a fresh virtual register
    pub fn reg(&mut self) -> VReg {
        self.mir.reg()
    }

    pub fn create_stack_slot(&mut self, layout: Layout) -> u64 {
        self.mir.create_stack_slot(layout)
    }

    pub fn create_block(&mut self) -> MirBlock {
        self.mir.create_block()
    }
}
