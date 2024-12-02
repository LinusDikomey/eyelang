
# Currently only used by ToString implementations so only what is needed is implemented.
# Will hopefully no longer be needed once generic literals and operator overloading are ready.
Int :: trait {
    zero :: fn -> Self
    one :: fn -> Self
    ten :: fn -> Self

    add :: fn(this Self, other Self) -> Self
    sub :: fn(this Self, other Self) -> Self
    mul :: fn(this Self, other Self) -> Self
    div :: fn(this Self, other Self) -> Self
    mod :: fn(this Self, other Self) -> Self
    eq :: fn(this Self, other Self) -> bool
    lt :: fn(this Self, other Self) -> bool
    as_u8 :: fn(this Self) -> u8
    from_u8 :: fn(x u8) -> Self
} for {
    impl _ for u8 {
        zero :: fn -> u8: 0
        one :: fn -> u8: 1
        ten :: fn -> u8: 10

        add :: fn(a u8, b u8) -> u8: a + b
        sub :: fn(a u8, b u8) -> u8: a - b
        mul :: fn(a u8, b u8) -> u8: a * b
        div :: fn(a u8, b u8) -> u8: a / b
        mod :: fn(a u8, b u8) -> u8: a % b
        eq :: fn(a u8, b u8) -> bool: a == b
        lt :: fn(a u8, b u8) -> bool: a < b
        as_u8 :: fn(x u8) -> u8: x
        from_u8 :: fn(x u8) -> u8: x
    }

    impl _ for u16 {
        zero :: fn -> u16: 0
        one :: fn -> u16: 1
        ten :: fn -> u16: 10

        add :: fn(a u16, b u16) -> u16: a + b
        sub :: fn(a u16, b u16) -> u16: a - b
        mul :: fn(a u16, b u16) -> u16: a * b
        div :: fn(a u16, b u16) -> u16: a / b
        mod :: fn(a u16, b u16) -> u16: a % b
        eq :: fn(a u16, b u16) -> bool: a == b
        lt :: fn(a u16, b u16) -> bool: a < b
        as_u8 :: fn(x u16) -> u8: x as u8
        from_u8 :: fn(x u8) -> u16: x as _
    }

    impl _ for u32 {
        zero :: fn -> u32: 0
        one :: fn -> u32: 1
        ten :: fn -> u32: 10

        add :: fn(a u32, b u32) -> u32: a + b
        sub :: fn(a u32, b u32) -> u32: a - b
        mul :: fn(a u32, b u32) -> u32: a * b
        div :: fn(a u32, b u32) -> u32: a / b
        mod :: fn(a u32, b u32) -> u32: a % b
        eq :: fn(a u32, b u32) -> bool: a == b
        lt :: fn(a u32, b u32) -> bool: a < b
        as_u8 :: fn(x u32) -> u8: x as u8
        from_u8 :: fn(x u8) -> u32: x as _
    }

    impl _ for u64 {
        zero :: fn -> u64: 0
        one :: fn -> u64: 1
        ten :: fn -> u64: 10

        add :: fn(a u64, b u64) -> u64: a + b
        sub :: fn(a u64, b u64) -> u64: a - b
        mul :: fn(a u64, b u64) -> u64: a * b
        div :: fn(a u64, b u64) -> u64: a / b
        mod :: fn(a u64, b u64) -> u64: a % b
        eq :: fn(a u64, b u64) -> bool: a == b
        lt :: fn(a u64, b u64) -> bool: a < b
        as_u8 :: fn(x u64) -> u8: x as u8
        from_u8 :: fn(x u8) -> u64: x as _
    }

    impl _ for i8 {
        zero :: fn -> i8: 0
        one :: fn -> i8: 1
        ten :: fn -> i8: 10

        add :: fn(a i8, b i8) -> i8: a + b
        sub :: fn(a i8, b i8) -> i8: a - b
        mul :: fn(a i8, b i8) -> i8: a * b
        div :: fn(a i8, b i8) -> i8: a / b
        mod :: fn(a i8, b i8) -> i8: a % b
        eq :: fn(a i8, b i8) -> bool: a == b
        lt :: fn(a i8, b i8) -> bool: a < b
        as_u8 :: fn(x i8) -> u8: x as u8
        from_u8 :: fn(x u8) -> i8: x as _
    }

    impl _ for i16 {
        zero :: fn -> i16: 0
        one :: fn -> i16: 1
        ten :: fn -> i16: 10

        add :: fn(a i16, b i16) -> i16: a + b
        sub :: fn(a i16, b i16) -> i16: a - b
        mul :: fn(a i16, b i16) -> i16: a * b
        div :: fn(a i16, b i16) -> i16: a / b
        mod :: fn(a i16, b i16) -> i16: a % b
        eq :: fn(a i16, b i16) -> bool: a == b
        lt :: fn(a i16, b i16) -> bool: a < b
        as_u8 :: fn(x i16) -> u8: x as u8
        from_u8 :: fn(x u8) -> i16: x as _
    }

    impl _ for i32 {
        zero :: fn -> i32: 0
        one :: fn -> i32: 1
        ten :: fn -> i32: 10

        add :: fn(a i32, b i32) -> i32: a + b
        sub :: fn(a i32, b i32) -> i32: a - b
        mul :: fn(a i32, b i32) -> i32: a * b
        div :: fn(a i32, b i32) -> i32: a / b
        mod :: fn(a i32, b i32) -> i32: a % b
        eq :: fn(a i32, b i32) -> bool: a == b
        lt :: fn(a i32, b i32) -> bool: a < b
        as_u8 :: fn(x i32) -> u8: x as u8
        from_u8 :: fn(x u8) -> i32: x as _
    }

    impl _ for i64 {
        zero :: fn -> i64: 0
        one :: fn -> i64: 1
        ten :: fn -> i64: 10

        add :: fn(a i64, b i64) -> i64: a + b
        sub :: fn(a i64, b i64) -> i64: a - b
        mul :: fn(a i64, b i64) -> i64: a * b
        div :: fn(a i64, b i64) -> i64: a / b
        mod :: fn(a i64, b i64) -> i64: a % b
        eq :: fn(a i64, b i64) -> bool: a == b
        lt :: fn(a i64, b i64) -> bool: a < b
        as_u8 :: fn(x i64) -> u8: x as u8
        from_u8 :: fn(x u8) -> i64: x as _
    }
}

# TODO: should only work on signed integers
abs :: fn[T: Int](x T) -> T: if Int.lt(x, Int.zero()): Int.sub(Int.zero(), x) else x
