use core::{fmt, str};
use std::{marker::PhantomData, ops::Index};

use color_format::{cwrite, cwriteln};

use crate::{
    Argument, Function, FunctionId, Global, GlobalId, Inst, LocalFunctionId, Module, ModuleId,
    ModuleOf, PrimitiveInfo,
};

pub struct Environment {
    pub(crate) modules: Vec<Module>,
    pub(crate) primitives: Vec<PrimitiveInfo>,
    pub(crate) modules_by_type: dmap::DHashMap<std::any::TypeId, ModuleId>,
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
        let mut env = Self {
            modules: Vec::new(),
            primitives,
            modules_by_type: dmap::new(),
        };
        let id = env.add_dialect_module::<crate::builtins::Builtin>();
        debug_assert_eq!(id.id(), ModuleId::BUILTINS);
        env
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

    pub fn add_dialect_module<I: Inst + 'static>(&mut self) -> ModuleOf<I> {
        let id = self.create_module_from_functions(I::MODULE_NAME, I::functions());
        self.modules_by_type.insert(std::any::TypeId::of::<I>(), id);
        ModuleOf(id, PhantomData)
    }

    pub fn get_dialect_module<I: Inst + 'static>(&mut self) -> ModuleOf<I> {
        let id = *self
            .modules_by_type
            .entry(std::any::TypeId::of::<I>())
            .or_insert_with(|| {
                let id = ModuleId(self.modules.len() as _);
                self.modules.push(Module {
                    name: I::MODULE_NAME.into(),
                    functions: I::functions(),
                    globals: Vec::new(),
                });
                id
            });
        ModuleOf(id, PhantomData)
    }

    pub fn get_dialect_module_if_present<I: Inst + 'static>(&self) -> Option<ModuleOf<I>> {
        let id = *self.modules_by_type.get(&std::any::TypeId::of::<I>())?;
        Some(ModuleOf(id, PhantomData))
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
        crate::display::ModuleDisplay {
            env: self,
            module: &self[module],
        }
    }

    pub fn primitives(&self) -> &[PrimitiveInfo] {
        &self.primitives
    }

    pub fn get_module(&self, module: ModuleId) -> &Module {
        &self.modules[module.0 as usize]
    }
}
impl fmt::Display for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for module in &self.modules {
            write!(f, "{}", crate::display::ModuleDisplay { env: self, module })?;
        }
        Ok(())
    }
}
