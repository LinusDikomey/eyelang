use core::{fmt, str};
use std::marker::PhantomData;

use color_format::{cwrite, cwriteln};

use crate::{
    Argument, Environment, Function, FunctionIr, MCReg, Module, Parameter, Ref, Types, builtins,
    mc::{Register, UnknownRegister},
};

impl fmt::Display for Ref {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::UNIT => cwrite!(f, "#m<unit>"),
            Self::FALSE => cwrite!(f, "#m<false>"),
            Self::TRUE => cwrite!(f, "#m<true>"),
            _ => cwrite!(f, "#c<%{}>", self.0),
        }
    }
}

impl fmt::Display for crate::BlockId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        cwrite!(f, "#r<b{}>", self.0)
    }
}

impl fmt::Display for MCReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_dead() {
            write!(f, "!")?;
        }
        if let Some(r) = self.virt() {
            cwrite!(f, "#c<${}>", r)
        } else {
            cwrite!(f, "#c<?{}>", self.0)
        }
    }
}
impl Parameter {
    pub fn display<'a>(self, types: &'a Types, env: &'a Environment) -> ParameterDisplay<'a> {
        ParameterDisplay {
            param: self,
            types,
            env,
        }
    }
}
pub struct ParameterDisplay<'a> {
    param: Parameter,
    types: &'a Types,
    env: &'a Environment,
}
impl fmt::Display for ParameterDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.param {
            crate::Parameter::Ref => cwrite!(f, "#g<val>"),
            crate::Parameter::RefOf(ty) => {
                write!(f, "{}", self.types.display_type(ty, &self.env.primitives))?;
                Ok(())
            }
            crate::Parameter::BlockId => cwrite!(f, "#g<blockid>"),
            crate::Parameter::BlockTarget => cwrite!(f, "#g<block>"),
            crate::Parameter::Int | crate::Parameter::Int32 => cwrite!(f, "#g<intliteral>"),
            crate::Parameter::Float => cwrite!(f, "#b<floatliteral>"),
            crate::Parameter::TypeId => cwrite!(f, "#g<type>"),
            crate::Parameter::FunctionId => cwrite!(f, "#g<function>"),
            crate::Parameter::GlobalId => cwrite!(f, "#g<global>"),
            crate::Parameter::MCReg(usage) => cwrite!(f, "#g<mcreg>({usage})"),
        }
    }
}

pub struct ModuleDisplay<'a> {
    pub env: &'a Environment,
    pub module: &'a Module,
}
impl fmt::Display for ModuleDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { env, module } = self;
        cwriteln!(f, "#m<begin module> #u;c<{}>", module.name)?;
        for global in &module.globals {
            cwrite!(
                f,
                "  #m<global> #b<{}> [align {}",
                global.name,
                global.align
            )?;
            if global.readonly {
                cwrite!(f, ", readonly")?;
            }
            write!(f, "] = ")?;
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
            writeln!(f, "{}", FunctionDisplay { env, function })?;
        }
        cwriteln!(f, "#m<end module> #u;c<{}>\n", module.name)
    }
}

pub struct FunctionDisplay<'a> {
    pub env: &'a Environment,
    pub function: &'a Function,
}
impl fmt::Display for FunctionDisplay<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { env, function } = self;
        let display_params = |f: &mut fmt::Formatter| {
            write!(f, "(")?;
            for (i, param) in function.params.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", param.display(&function.types, env))?;
            }
            if let Some(param) = function.varargs {
                if function.params.is_empty() {
                    write!(f, "...")?;
                } else {
                    write!(f, ", ...")?;
                }
                write!(f, "{}", param.display(&function.types, env))?;
            }
            writeln!(f, ")")
        };
        if let Some(ir) = &function.ir {
            cwrite!(f, "  #m<begin> #b<{}>", function.name)?;
            display_params(f)?;
            writeln!(
                f,
                "{}",
                BodyDisplay::<UnknownRegister> {
                    env,
                    types: &function.types,
                    ir,
                    _r: PhantomData,
                }
            )?;
            cwriteln!(f, "  #m<end> #b<{}>", function.name)?;
        } else {
            cwrite!(f, "  #m<declare> #b<{}>", function.name)?;
            display_params(f)?;
        }
        Ok(())
    }
}

pub struct BodyDisplay<'a, R: Register = UnknownRegister> {
    pub env: &'a Environment,
    pub types: &'a crate::Types,
    pub ir: &'a FunctionIr,
    pub _r: PhantomData<R>,
}
impl<R: Register> fmt::Display for BodyDisplay<'_, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let Self { env, types, ir, _r } = self;
        let digits = if ir.insts.len() < 2 {
            1
        } else {
            (ir.insts.len() - 1).ilog10() + 1
        };
        for block in ir.block_ids() {
            cwrite!(f, "  {}", block)?;
            if ir.block_arg_count(block) > 0 {
                let args = ir.get_block_args(block).iter();
                cwrite!(f, "(")?;
                for (i, arg) in args.enumerate() {
                    if i != 0 {
                        cwrite!(f, ", ")?;
                    }
                    write!(f, "{arg}: ")?;
                    let ty = ir.get_ref_ty(arg);
                    write!(f, "{}", types.display_type(ty, &env.primitives))?;
                }
                cwrite!(f, ")")?;
            }
            cwriteln!(f, ":")?;
            for (r, inst) in ir.get_block(block) {
                if inst.module() == builtins::BUILTIN.id()
                    && inst.function() == builtins::Builtin::Nothing.id()
                {
                    // don't show 'Nothing' instructions
                    continue;
                }
                let called_module = &env.modules[inst.function.module.0 as usize];
                let called = &called_module.functions[inst.function.function.0 as usize];

                cwrite!(f, "    ")?;
                let has_value = !called.terminator
                    && !matches!(types[inst.ty], crate::Type::Tuple(members) if members.count == 0);
                if has_value {
                    let r_digits = if r.0 == 0 { 1 } else { r.0.ilog10() + 1 };
                    for _ in 0..digits - r_digits {
                        cwrite!(f, " ")?;
                    }
                    write!(f, "{} = ", r)?;
                } else {
                    for _ in 0..digits + 4 {
                        write!(f, " ")?;
                    }
                }
                cwrite!(f, "#c<{}>.", called_module.name)?;
                cwrite!(f, "#b<{}>", called.name)?;
                for arg in inst.args_inner(&called.params, called.varargs, &ir.blocks, &ir.extra) {
                    match arg {
                        Argument::Ref(r) => write!(f, " {}", r)?,
                        Argument::BlockId(id) => cwrite!(f, " {}", id)?,
                        Argument::BlockTarget(target) => {
                            cwrite!(f, " {}", target.0)?;
                            let args = target.1;
                            if !args.is_empty() {
                                cwrite!(f, "(")?;
                                for (i, r) in args.iter().enumerate() {
                                    if i != 0 {
                                        write!(f, ", ")?;
                                    }
                                    write!(f, "{r}")?;
                                }
                                cwrite!(f, ")")?;
                            }
                        }
                        Argument::Int(n) => cwrite!(f, " #y<{}>", n)?,
                        Argument::Float(x) => cwrite!(f, "#y<{}>", x)?,
                        Argument::TypeId(ty) => {
                            let display = types.display_type(ty, &env.primitives);
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
                        Argument::MCReg(r) => {
                            write!(f, " ")?;
                            if r.is_dead() {
                                write!(f, "!")?;
                            }
                            if let Some(v) = r.virt() {
                                cwrite!(f, "#c<${}>", v)?;
                            } else {
                                cwrite!(f, "#c<%{}>", r.phys::<R>().unwrap().to_str())?;
                            }
                        }
                    }
                }
                if has_value {
                    let display = types.display_type(inst.ty, &env.primitives);
                    write!(f, " :: {display}")?;
                }
                cwriteln!(f)?;
            }
        }
        Ok(())
    }
}
