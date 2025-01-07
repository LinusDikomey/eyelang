#[macro_export]
macro_rules! arg {
    ($self: ident, $ir: ident, $env: ident, $arg: ident, _) => {};
    ($self: ident, $ir: ident, $env: ident, $arg: ident, $var: ident) => {
        let $crate::Argument::Ref($var) = $arg else {
            unreachable!("invalid argument type, expected Ref");
        };
    };
    ($self: ident, $ir: ident, $env: ident, $arg: ident, $const: literal) => {
        let $crate::Argument::Int(value) = $arg else {
            unreachable!("invalid argument type, expected Int");
        };
        if value != $const {
            return $crate::rewrite::Rewrite::Keep;
        }
    };
    ($self: ident, $ir: ident, $env: ident, $arg: ident, $inner: tt) => {
        let $crate::Argument::Ref(r) = $arg else {
            unreachable!("invalid argument type, expected Ref");
        };
        if !r.is_ref() {
            return $crate::rewrite::Rewrite::Keep;
        };
        let inst = $ir.get_inst(r);
        $crate::pattern_ref!($self, $ir, $env, inst, $inner)
    };
}

#[macro_export]
macro_rules! args {
    ($self: ident, $ir: ident, $env: ident, $args: expr,) => {
        let [] = $args;
    };
    ($self: ident, $ir: ident, $env: ident, $args: expr, $a: tt) => {
        let [a] = $args;
        $crate::arg!($self, $ir, $env, a, $a);
    };
    ($self: ident, $ir: ident, $env: ident, $args: expr, $a: tt $b: tt) => {
        let [a, b] = $args;
        $crate::arg!($self, $ir, $env, a, $a);
        $crate::arg!($self, $ir, $env, b, $b);
    };
}

#[macro_export]
macro_rules! pattern_ref {
    ($self: ident, $ir: ident, $env: ident, $inst: expr, ($module: ident.$matched_inst: ident $($arg: tt)*)) => {
        let Some(inst) = $inst.as_module($self.$module) else {
            return $crate::rewrite::Rewrite::Keep;
        };
        if inst.op() != $module::$matched_inst {
            return $crate::rewrite::Rewrite::Keep;
        }
        $crate::args!($self, $ir, $env, $ir.args_n(&inst), $($arg)*);
    };
}

#[macro_export]
macro_rules! rewrite_rules {
    (
        $rewriter: ident
        $ir: ident
        $types: ident
        $inst: ident

        $(use $module: ident: $module_path: path;)*

        patterns:

        $($pattern: tt $(if $cond: expr)? => $(=)? $result: expr;)*
    ) => {
        pub struct $rewriter {
            $(
                $module: $crate::ModuleOf<$module_path>,
            )*
        }
        impl $rewriter {
            pub fn new(env: &mut $crate::Environment) -> Self {
                Self {
                    $(
                        $module: env.get_dialect_module(),
                    )*
                }
            }
        }
        impl $crate::rewrite::Rewriter for $rewriter {
            fn visit_instruction(
                &mut self,
                #[allow(unused)] $ir: &mut $crate::FunctionIr,
                #[allow(unused)] $types: &$crate::Types,
                env: &$crate::Environment,
                #[allow(unused)] $inst: &$crate::Instruction,
                block: $crate::BlockId,
            ) -> $crate::rewrite::Rewrite {
                $(
                    use $module_path as $module;
                    let $module = self.$module;
                )*
                $(
                    let result = (|| {
                        $crate::pattern_ref!(self, $ir, env, $inst, $pattern);
                        $(
                            let cond: bool = $cond;
                            if !cond {
                                return $crate::rewrite::Rewrite::Keep;
                            }
                        )*
                        $crate::rewrite::IntoRewrite::into_rewrite($result, $ir, env, block)
                    })();
                    if result.success() { return result; }
                )*
                $crate::rewrite::Rewrite::Keep
            }
        }
    };
}
pub use crate::rewrite_rules;
