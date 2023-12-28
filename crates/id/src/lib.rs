#[macro_export]
macro_rules! id {
    ($(#[$($attrss:tt)*])* $name: ident) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        $(#[$($attrss)*])*
        pub struct $name(pub u32);
        impl $name {
            pub const MISSING: Self = Self(u32::MAX);
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

