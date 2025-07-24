use std::path::Path;

use ir::MCReg;

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

        env.get_dialect_module::<arch::x86::X86>();
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

        let mut isel = arch::x86::InstructionSelector::new(env);
        let mc = env.get_dialect_module::<ir::mc::Mc>();
        let x86 = isel.x86;
        let abi = arch::x86::get_target_abi();

        for func in env[module_id].functions() {
            if let Some(ir) = func.ir() {
                let (mut mir, types) =
                    arch::x86::codegen(env, ir, func.types(), &mut isel, mc, abi);
                let offset = text_section.len() as u64;
                tracing::debug!(
                    target: "backend-ir",
                    function = func.name,
                    "mir:\n{}",
                    mir.display_with_phys_regs::<arch::x86::Reg>(env, &types)
                );
                ir::mc::regalloc::<arch::x86::X86>(
                    env,
                    mc,
                    &mut mir,
                    &types,
                    arch::x86::PREOCCUPIED_REGISTERS,
                    &func.name,
                );
                tracing::debug!(
                    target: "regalloc",
                    function = func.name,
                    "mir (post-regalloc):\n{}",
                    mir.display_with_phys_regs::<arch::x86::Reg>(env, &types),
                );
                arch::x86::write(env, mc, x86, &mir, &mut text_section);
                let size = text_section.len() as u64 - offset;
                let name_index = writer.add_str(&func.name);
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
