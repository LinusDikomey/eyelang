#[macro_export]
macro_rules! arg {
    ($modules: ident, $ir: ident, $env: ident, $arg: ident, _) => {};
    ($modules: ident, $ir: ident, $env: ident, $arg: ident, $var: ident) => {
        let $crate::Argument::Ref($var) = $arg else {
            unreachable!("invalid argument type, expected Ref");
        };
    };
    ($modules: ident, $ir: ident, $env: ident, $arg: ident, $const: literal) => {
        let $crate::Argument::Int(value) = $arg else {
            unreachable!("invalid argument type, expected Int");
        };
        if value != $const {
            return ::core::option::Option::None;
        }
    };
    ($modules: ident, $ir: ident, $env: ident, $arg: ident, (#$int: ident)) => {
        let $crate::Argument::Int($int) = $arg else {
            unreachable!("invalid argument type, expected Int");
        };
    };
    ($modules: ident, $ir: ident, $env: ident, $arg: ident, $($inner: tt)*) => {
        let $crate::Argument::Ref(r) = $arg else {
            unreachable!("invalid argument type, expected Ref");
        };
        if !r.is_ref() {
            return ::core::option::Option::None;
        };
        let inst = $ir.get_inst(r);
        $crate::pattern_ref!($modules, $ir, $env, inst, $($inner)*)
    };
}

#[macro_export]
macro_rules! args {
    ($modules: ident, $ir: ident, $env: ident, $args: expr,) => {
        let [] = $args;
    };
    ($modules: ident, $ir: ident, $env: ident, $args: expr, $a: tt) => {
        let [a] = $args;
        $crate::arg!($modules, $ir, $env, a, $a);
    };
    ($modules: ident, $ir: ident, $env: ident, $args: expr, $a: tt $b: tt) => {
        let [a, b] = $args;
        $crate::arg!($modules, $ir, $env, a, $a);
        $crate::arg!($modules, $ir, $env, b, $b);
    };
}

#[macro_export]
macro_rules! pattern_ref {
    ($modules: ident, $ir: ident, $env: ident, $inst: expr, ($module: ident.$matched_inst: ident $($arg: tt)*)) => {
        let inst = $inst.as_module($modules.$module)?;
        if inst.op() != $module::$matched_inst {
            return ::core::option::Option::None;
        }
        $crate::args!($modules, $ir, $env, $ir.args_n(&inst), $($arg)*);
    };
}

#[macro_export]
macro_rules! visitor {
    (
        impl $(<$lifetime: lifetime>)?
        for
        $rewriter: ty,
        $modules_field: ident: $modules: ident,
        $output: ty,
        $ir: ident,
        $types: ident,
        $inst: ident;

        $(use $module: ident: $module_path: path;)*

        patterns:

        $($pattern: tt $(if $cond: expr)? => $(=)? $result: expr;)*
    ) => {
        pub struct $modules {
            $(
                $module: $crate::ModuleOf<$module_path>,
            )*
        }
        impl $modules {
            pub fn new(env: &mut $crate::Environment) -> Self {
                Self {
                    $(
                        $module: env.get_dialect_module(),
                    )*
                }
            }
        }
        impl $(<$lifetime>)* $crate::rewrite::Visitor for $rewriter {
            type Output = $output;

            fn visit_instruction(
                &mut self,
                #[allow(unused)] $ir: &mut $crate::FunctionIr,
                #[allow(unused)] $types: &$crate::Types,
                env: &$crate::Environment,
                #[allow(unused)] $inst: &$crate::Instruction,
                block: $crate::BlockId,
            ) -> ::core::option::Option<$output> {
                let modules = &self.$modules_field;
                $(
                    use $module_path as $module;
                    let $module = modules.$module;
                )*
                $(
                    let result = (|| {
                        $crate::pattern_ref!(modules, $ir, env, $inst, $pattern);
                        $(
                            let cond: bool = $cond;
                            if !cond {
                                return ::core::option::Option::None;
                            }
                        )*
                        ::core::option::Option::Some(
                            $crate::rewrite::IntoVisit::into_visit($result, $ir, env, block)
                        )
                    })();
                    if let Some(value) = result {
                        return Some(value);
                    }
                )*
                ::core::option::Option::None
            }
        }
    };
}
pub use crate::visitor;
