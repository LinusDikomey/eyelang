MyTrait :: trait {
    my_function :: fn(l Self, r Self) -> Self
} for {
    impl[T: OtherTrait] T {
        my_function ::fn(l T, r T) -> T {
            OtherTrait.f(l)
            ret l
        }
    }
}

OtherTrait :: trait {
    f :: fn(self Self) -> bool
} for {
    impl f32 {
        f :: fn(self f32) -> bool: self == 0.0
    }
    impl f64 {
        f :: fn(self f64) -> bool: self == 0.0
    }
}

main :: fn {
    f := MyTrait.my_function(3.5, 4.6 as f64)
    h: f32 = MyTrait.my_function(1.0, 2.0)
    i: f64 = MyTrait.my_function(1.0, 2.0)

    # calls with ambiguous floats/integers are NOT allowed for now, might try defaulting to f32 here
    # in the future
    # Add.add(1.0, 2.0)
}
