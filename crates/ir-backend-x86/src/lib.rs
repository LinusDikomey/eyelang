#![allow(unused)] // TODO: remove when x86 backend is worked on again
use std::path::Path;

use elf::{ElfObjectWriter, SectionHeader};
use ir::mc::Op;

mod abi;
mod elf;
mod emit;
mod isa;
mod isel;

#[derive(Debug)]
pub enum Error {
    IO(std::io::Error),
}

pub struct Backend {
    log: bool,
}
impl Backend {
    pub fn new() -> Self {
        Self { log: false }
    }

    pub fn enable_logging(&mut self) {
        self.log = true;
    }

    pub fn emit_module(
        &self,
        module: &ir::Module,
        print_ir: bool,
        target: Option<&str>,
        out_file: &Path,
    ) -> Result<(), Error> {
        assert!(target.is_none(), "todo: check target");
        let mut writer = ElfObjectWriter::new();
        let mut text_section = Vec::new();
        let mut symtab = elf::symtab::SymtabWriter::new();

        // file entry
        let file_name = writer.add_str(&module.name);
        symtab.entry(elf::symtab::Entry {
            name_index: file_name,
            bind: elf::symtab::Bind::Local,
            ty: elf::symtab::Type::File,
            visibility: elf::symtab::Visibility::Default,
            section_index: 0xfff1, // SHN_ABS
            value: 0,
            size: 0,
        });
        // section entry
        symtab.entry(elf::symtab::Entry {
            name_index: 0,
            bind: elf::symtab::Bind::Local,
            ty: elf::symtab::Type::Section,
            visibility: elf::symtab::Visibility::Default,
            section_index: 2,
            value: 0,
            size: 0,
        });

        for func in &module.funcs {
            if let Some(ir) = &func.ir {
                let mut mir = isel::codegen(ir, func, &func.types);
                let offset = text_section.len() as u64;
                if print_ir {
                    println!("mir for {}:\n{}\n", func.name, mir);
                }
                ir::mc::regalloc(&mut mir, self.log);
                if self.log {
                    println!("mir for {}: (post-regalloc)\n{}\n", func.name, mir);
                }
                emit::write(&mir, &mut text_section);
                let size = text_section.len() as u64 - offset;
                let name_index = writer.add_str(&func.name);
                symtab.entry(elf::symtab::Entry {
                    name_index,
                    bind: elf::symtab::Bind::Global,
                    ty: elf::symtab::Type::Function,
                    visibility: elf::symtab::Visibility::Default,
                    section_index: 2,
                    value: offset,
                    size,
                });
            }
        }
        writer.section(
            SectionHeader {
                name: ".text".to_owned(),
                ty: elf::SectionHeaderType::Progbits,
                flags: elf::SectionHeaderFlags {
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
enum MCValue {
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
    /// represents a constant offset from a register
    PtrOffset(MCReg, i32),
    /// value is located at a constant offset from an address in a register
    Indirect(MCReg, i32),
}
#[derive(Debug, Clone, Copy)]
enum MCReg {
    Register(isa::Reg),
    Virtual(ir::mc::VReg),
}
impl MCReg {
    pub fn op(self) -> Op<isa::Reg> {
        match self {
            MCReg::Register(r) => Op::Reg(r),
            MCReg::Virtual(r) => Op::VReg(r),
        }
    }
}
