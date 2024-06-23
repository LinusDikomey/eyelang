use std::{ffi::CStr, path::Path};

use elf::{ElfObjectWriter, SectionHeader};

mod codegen;
mod elf;
mod emit;
mod machine_ir;

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
                let mut mir = codegen::codegen(ir, func, &func.types);
                let offset = text_section.len() as u64;
                if print_ir {
                    println!("mir for {}:\n{}\n", func.name, mir);
                }
                ir::mc::regalloc(&mut mir);
                if print_ir {
                    println!("post-regalloc mir {}:\n{}\n", func.name, mir);
                }
                emit::write(&mir, &mut text_section);
                let size = text_section.len() as u64 - offset;
                let name_index = writer.add_str(&func.name);
                symtab.entry(elf::symtab::Entry {
                    name_index,
                    bind: elf::symtab::Bind::Global,
                    ty: elf::symtab::Type::None,
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
