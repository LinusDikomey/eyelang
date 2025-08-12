macro_rules! define_flags{
    ($name: ident, $offset: expr,) => {};
    ($name: ident, $offset: expr, $flag_const: ident $flag_name: ident $($rest: tt)*) => {
        impl $name {
            pub const $flag_const: Self = Self(1 << $offset);
            pub fn $flag_name(&self) -> bool {
                self.0 & Self::$flag_const.0 != 0
            }
        }
        define_flags!($name, $offset + 1, $($rest)*);
    };
}

macro_rules! bitflags {
    ($name: ident : $ty: ident { $($flag_const: ident $flag_name: ident,)* }) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Default)]
        pub struct $name($ty);

        define_flags!($name, 0, $($flag_const $flag_name)*);

        impl $name {
            pub fn set(&mut self, flag: Self, value: bool) {
                if value {
                    *self |= flag;
                } else {
                    *self &= !flag;
                }
            }
        }

        impl ::std::ops::BitOr for $name {
            type Output = Self;
            fn bitor(self, rhs: Self) -> Self::Output {
                Self(self.0 | rhs.0)
            }
        }
        impl ::std::ops::BitOrAssign for $name {
            fn bitor_assign(&mut self, rhs: Self) {
                self.0 |= rhs.0
            }
        }

        impl ::std::ops::BitAnd for $name {
            type Output = Self;
            fn bitand(self, rhs: Self) -> Self::Output {
                Self(self.0 & rhs.0)
            }
        }
        impl ::std::ops::BitAndAssign for $name {
            fn bitand_assign(&mut self, rhs: Self) {
                self.0 &= rhs.0
            }
        }
        impl ::std::ops::Not for $name {
            type Output = Self;
            fn not(self) -> Self::Output {
                Self(!self.0)
            }
        }
    };
}

bitflags! {InstFlags : u8 {
    TERMINATOR terminator,
    PURE pure,
}}
