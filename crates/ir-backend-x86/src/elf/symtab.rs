use super::SectionHeader;

pub struct SymtabWriter {
    section: Vec<u8>,
    entry_count: u32,
}
impl SymtabWriter {
    pub fn new() -> Self {
        let mut writer = Self {
            section: Vec::new(),
            entry_count: 0,
        };
        writer.entry(Entry {
            name_index: 0,
            bind: Bind::Local,
            ty: Type::None,
            visibility: Visibility::Default,
            section_index: 0,
            value: 0,
            size: 0,
        });
        // the null entry isn't counted
        writer.entry_count = 0;
        writer
    }

    pub fn entry(&mut self, entry: Entry) {
        self.entry_count = self
            .entry_count
            .checked_add(1)
            .expect("too many entries in symtab");
        self.section.extend(entry.name_index.to_le_bytes());
        let info = ((entry.bind as u8) << 4) | (entry.ty as u8);
        self.section.extend([info, entry.visibility as u8]);
        self.section.extend(entry.section_index.to_le_bytes());
        self.section.extend(entry.value.to_le_bytes());
        self.section.extend(entry.size.to_le_bytes());
    }

    pub fn finish(self) -> (SectionHeader, Vec<u8>) {
        (
            SectionHeader {
                name: ".symtab".to_owned(),
                ty: super::SectionHeaderType::SymTab,
                flags: super::SectionHeaderFlags::default(),
                addr: 0,
                link: 1,
                info: self.entry_count,
                addralign: 8,
                entsize: 24,
            },
            self.section,
        )
    }
}

pub struct Entry {
    pub name_index: u32,
    pub bind: Bind,
    pub ty: Type,
    pub visibility: Visibility,
    pub section_index: u16,
    pub value: u64,
    pub size: u64,
}

#[repr(u8)]
#[allow(unused)]
pub enum Bind {
    Local = 0x00,
    Global = 0x01,
    Weak = 0x02,
    Num = 0x03,
}

#[repr(u8)]
#[allow(unused)]
pub enum Type {
    None = 0x00,
    Object = 0x01,
    Function = 0x02,
    Section = 0x03,
    File = 0x04,
    Common = 0x05,
    TLS = 0x06,
    NumTypes = 0x07,
}

#[repr(u8)]
#[allow(unused)]
pub enum Visibility {
    Default = 0x00,
    Internal = 0x01,
    Hiddden = 0x02,
    Protected = 0x03,
}
