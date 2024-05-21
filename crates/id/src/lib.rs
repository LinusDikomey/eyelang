#[macro_export]
macro_rules! id {
    ($(#[$($attrss:tt)*])* $name: ident) => {
        $crate::id!($(#[$($attrss)*])* u32 $name);
    };
    ($(#[$($attrss:tt)*])* $ty: ident $name: ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        $(#[$($attrss)*])*
        pub struct $name(pub $ty);
        impl $name {
            pub const MISSING: Self = Self($ty::MAX);
            pub fn idx(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(ProjectId);
id!(ModuleId);
id!(TypeId);
id!(ConstValueId);
id!(TraitId);
