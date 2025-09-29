use core::fmt;
use std::path::Path;

use ir::{
    MCReg, ModuleId,
    mc::{Abi, BackendState},
    pipeline::FunctionPass,
};

use crate::arch::x86::X86;

mod arch;
mod exe;

#[derive(Debug)]
pub enum Error {
    IO(std::io::Error),
}

#[derive(Default)]
pub struct Backend {}
impl Backend {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn emit_module(
        &self,
        env: &mut ir::Environment,
        module_id: ir::ModuleId,
        target: Option<&str>,
        out_file: &Path,
    ) -> Result<(), Error> {
        assert!(target.is_none(), "todo: check target");

        let mut writer = exe::elf::ElfObjectWriter::new();
        let mut text_section = Vec::new();
        let mut symtab = exe::elf::symtab::SymtabWriter::new();

        // file entry
        let file_name = writer.add_str(env[module_id].name());
        symtab.entry(exe::elf::symtab::Entry {
            name_index: file_name,
            bind: exe::elf::symtab::Bind::Local,
            ty: exe::elf::symtab::Type::File,
            visibility: exe::elf::symtab::Visibility::Default,
            section_index: 0xfff1, // SHN_ABS
            value: 0,
            size: 0,
        });
        // section entry
        symtab.entry(exe::elf::symtab::Entry {
            name_index: 0,
            bind: exe::elf::symtab::Bind::Local,
            ty: exe::elf::symtab::Type::Section,
            visibility: exe::elf::symtab::Visibility::Default,
            section_index: 2,
            value: 0,
            size: 0,
        });

        let isel = arch::x86::InstructionSelector::new(env);
        let mc = env.get_dialect_module::<ir::mc::Mc>();
        let x86 = isel.x86;
        let abi = arch::x86::get_target_abi();
        let mut relocations = Vec::new();

        let mut function_offsets = vec![0u32; env[module_id].function_ids().len()];

        let mut pipeline = ir::pipeline::Pipeline::new("backend");
        pipeline.add_function_pass(Box::new(Isel {
            isel,
            module_id,
            abi,
        }));
        pipeline.add_function_pass(Box::new(ir::mc::Regalloc::<arch::x86::X86> {
            mc: isel.mc,
            preoccupied: arch::x86::PREOCCUPIED_REGISTERS,
        }));
        pipeline.add_function_pass(Box::new(arch::x86::PrologueEpilogueInsertion { x86, abi }));

        for (id, function_offset) in
            (env[module_id].function_ids()).zip(function_offsets.iter_mut())
        {
            let func = &env[module_id][id];
            if let Some(ir) = func.ir() {
                let offset = text_section.len() as u64;
                *function_offset = offset.try_into().unwrap();
                // PERF: cloning ir, types, name
                let ir = ir.clone();
                let mut types = func.types().clone();
                let name = func.name.clone();
                let mir = pipeline
                    .process_function_with_regs::<arch::x86::Reg>(env, ir, &mut types, &name);
                arch::x86::write(env, mc, x86, &mir, &mut text_section, &mut relocations);
                let size = text_section.len() as u64 - offset;
                let name_index = writer.add_str(&env[module_id][id].name);
                symtab.entry(exe::elf::symtab::Entry {
                    name_index,
                    bind: exe::elf::symtab::Bind::Global,
                    ty: exe::elf::symtab::Type::Function,
                    visibility: exe::elf::symtab::Visibility::Default,
                    section_index: 2,
                    value: offset,
                    size,
                });
            }
        }
        for (function_id, i) in relocations {
            debug_assert_eq!(function_id.module, module_id);
            let is_extern = env[module_id][function_id.function].ir().is_none();
            if is_extern {
                // TODO: write relocation
            } else {
                let offset = (function_offsets[function_id.function.idx()] as i32) - (i as i32) - 4;
                text_section[i as usize..i as usize + 4].copy_from_slice(&offset.to_le_bytes());
            }
        }
        writer.section(
            exe::elf::SectionHeader {
                name: ".text".to_owned(),
                ty: exe::elf::SectionHeaderType::Progbits,
                flags: exe::elf::SectionHeaderFlags {
                    alloc: true,
                    execinstr: true,
                    ..Default::default()
                },
                addr: 0,
                link: 0,
                info: 0,
                addralign: 16,
                entsize: 0,
            },
            text_section,
        );
        let (symtab_header, symtab_contents) = symtab.finish();
        writer.section(symtab_header, symtab_contents);
        writer.write(out_file).map_err(Error::IO)?;
        Ok(())
    }
}

#[derive(Debug, Clone, Copy)]
pub enum MCValue {
    /// this value doesn't have any runtime bits
    None,
    /// value is undefined and can be assumed to be any value at runtime
    Undef,
    /// an immediate (pointer-sized) constant value
    Imm(u64),
    /// value is located in a register
    Reg(MCReg),
    /// value is up to 16 bytes large and is spread across two registers (lower bits, upper bits)
    TwoRegs(MCReg, MCReg),
}

pub fn list_targets() -> Vec<String> {
    vec!["x86_64-unknown-linux".to_owned()]
}

struct Isel {
    isel: arch::x86::InstructionSelector,
    module_id: ModuleId,
    abi: &'static dyn Abi<X86>,
}
impl fmt::Debug for Isel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Isel")
    }
}
impl FunctionPass<BackendState> for Isel {
    fn run(
        &self,
        env: &ir::Environment,
        types: &ir::Types,
        ir: ir::FunctionIr,
        _name: &str,
        state: &mut BackendState,
    ) -> (ir::FunctionIr, Option<ir::Types>) {
        let mut isel = self.isel;
        let (mir, types) =
            arch::x86::codegen(env, &ir, types, &mut isel, self.module_id, self.abi, state);
        (mir, Some(types))
    }
}
