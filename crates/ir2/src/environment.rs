use core::{fmt, str};
use std::{marker::PhantomData, ops::Index};

use color_format::{cwrite, cwriteln};

use crate::{
    Argument, Function, FunctionId, Global, GlobalId, Inst, LocalFunctionId, Module, ModuleId,
    ModuleOf, PrimitiveInfo,
};

pub struct Environment {
    modules: Vec<Module>,
    primitives: Vec<PrimitiveInfo>,
}
impl Index<ModuleId> for Environment {
    type Output = Module;

    fn index(&self, index: ModuleId) -> &Self::Output {
        &self.modules[index.0 as usize]
    }
}
impl Index<FunctionId> for Environment {
    type Output = Function;

    fn index(&self, index: FunctionId) -> &Self::Output {
        &self.modules[index.module.0 as usize].functions[index.function.0 as usize]
    }
}
impl Environment {
    pub fn new(primitives: Vec<PrimitiveInfo>) -> Self {
        Self {
            modules: Vec::new(),
            primitives,
        }
    }

    pub fn create_module(&mut self, name: impl Into<Box<str>>) -> ModuleId {
        let id = ModuleId(self.modules.len() as _);
        self.modules.push(Module {
            name: name.into(),
            functions: Vec::new(),
            globals: Vec::new(),
        });
        id
    }

    pub fn create_module_from_functions(
        &mut self,
        name: impl Into<Box<str>>,
        functions: Vec<Function>,
    ) -> ModuleId {
        let id = ModuleId(self.modules.len() as _);
        self.modules.push(Module {
            name: name.into(),
            functions,
            globals: Vec::new(),
        });
        id
    }

    pub fn add_inst_module<I: Inst>(&mut self) -> ModuleOf<I> {
        let id = self.create_module_from_functions(I::MODULE_NAME, I::functions());
        ModuleOf(id, PhantomData)
    }

    pub fn add_function(&mut self, module: ModuleId, function: Function) -> FunctionId {
        let module_data = &mut self.modules[module.0 as usize];
        let id = LocalFunctionId(module_data.functions.len() as _);
        module_data.functions.push(function);
        FunctionId {
            module,
            function: id,
        }
    }

    pub fn add_global(
        &mut self,
        module: ModuleId,
        name: impl Into<Box<str>>,
        align: u64,
        value: Box<[u8]>,
    ) -> GlobalId {
        let module_data = &mut self.modules[module.0 as usize];
        let idx = module_data.globals.len() as u32;
        module_data.globals.push(Global {
            name: name.into(),
            align,
            value,
        });
        GlobalId { module, idx }
    }

    #[must_use]
    pub fn display_module(&mut self, module: ModuleId) -> impl fmt::Display + use<'_> {
        ModuleDisplay {
            env: self,
            module: &self[module],
        }
    }
}
impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for module in &self.modules {
            write!(f, "{}", ModuleDisplay { env: self, module })?;
        }
        Ok(())
    }
}
struct ModuleDisplay<'a> {
    env: &'a Environment,
    module: &'a Module,
}
impl fmt::Display for ModuleDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { env, module } = self;
        cwriteln!(f, "#m<begin module> #u;c<{}>", module.name)?;
        for global in &module.globals {
            cwrite!(
                f,
                "  #m<global> #b<{}> [align {}] = ",
                global.name,
                global.align
            )?;
            if let Ok(s) = str::from_utf8(&global.value) {
                cwriteln!(f, "#y<{s:?}>")?;
            } else {
                cwrite!(f, "[")?;
                let mut line_len = 20 + global.name.len(); // roughly estimate length for wrapping
                for (i, &byte) in global.value.iter().enumerate() {
                    let entry_len = 2 + if byte == 0 { 1 } else { byte.ilog10() as usize };
                    if line_len + entry_len > 100 {
                        cwrite!(f, "\n    ")?;
                        line_len = 4;
                    } else if i != 0 {
                        cwrite!(f, " ")?;
                    }
                    line_len += entry_len;
                    cwrite!(f, "#y<{byte}>")?;
                }
                cwriteln!(f, "]")?;
            }
        }
        if !module.globals.is_empty() {
            writeln!(f)?;
        }
        for function in &module.functions {
            if let Some(ir) = &function.ir {
                cwriteln!(f, "  #m<begin> #b<{}>", function.name)?;
                let digits = if ir.insts.len() < 2 {
                    1
                } else {
                    (ir.insts.len() - 1).ilog10() + 1
                };
                for block in ir.block_ids() {
                    cwriteln!(f, "  #r<b{}>:", block.0)?;
                    for (r, inst) in ir.get_block(block) {
                        let called_module = &env.modules[inst.function.module.0 as usize];
                        let called = &called_module.functions[inst.function.function.0 as usize];

                        cwrite!(f, "    ")?;
                        if called.terminator {
                            for _ in 0..digits + 4 {
                                write!(f, " ")?;
                            }
                        } else {
                            let r_digits = if r.0 == 0 { 1 } else { r.0.ilog10() + 1 };
                            for _ in 0..digits - r_digits {
                                cwrite!(f, " ")?;
                            }
                            cwrite!(f, "#c<%{}> = ", r.0)?;
                        }
                        cwrite!(f, "#c<{}>.", called_module.name)?;
                        cwrite!(f, "#b<{}>", called.name)?;
                        for arg in inst.args(&called.params, &ir.extra) {
                            match arg {
                                Argument::Ref(r) => cwrite!(f, " #c<%{}>", r.0)?,
                                Argument::Block(block_id) => cwrite!(f, " #r<b{}>", block_id.0)?,
                                Argument::Int(n) => cwrite!(f, " #y<{}>", n)?,
                                Argument::TypeId(ty) => {
                                    let display = function.types.display_type(ty, &env.primitives);
                                    write!(f, " {display}")?;
                                }
                                Argument::FunctionId(id) => {
                                    let module = &env[id.module];
                                    let function = &module[id.function];
                                    cwrite!(f, " #c<{}>.#b<{}>", module.name, function.name)?;
                                }
                                Argument::GlobalId(id) => {
                                    let module = &env[id.module];
                                    let global = &module.globals[id.idx as usize];
                                    cwrite!(f, " @#c<{}>.#b<{}>", module.name, global.name)?;
                                }
                            }
                        }
                        if !called.terminator {
                            let display = function.types.display_type(inst.ty, &env.primitives);
                            write!(f, " :: {display}")?;
                        }
                        cwriteln!(f)?;
                    }
                }
                cwriteln!(f, "  #m<end> #b<{}>", function.name)?;
            } else {
                cwriteln!(f, "  #m<declare> #b<{}>", function.name)?;
            }
        }
        cwriteln!(f, "#m<end module> #u;c<{}>\n", module.name)
    }
}
