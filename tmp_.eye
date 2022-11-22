
Vec2 :: struct {
    x i32,
    y i32,

    print :: fn[T](v *Vec2) {
        v^.x = 2
    }
}

A :: enum { A B C }

main :: fn {
    # x := 1 + 1
    
    a: Vec2 = Vec2(1, 2)
    a.print()
    

    a :: fn() { }

    c()
    
    use b as c

    use a as b

    x := f(3)

    y := id(4)
    
    match 3 {
        1: 1,
        2: 2,
        3: 3,
    }

    f := .Sus

    some_function(x, exit(4), 1.5)
    1
}

f :: fn(x i32) -> i32 {
    ret x
}

some_function :: fn(x i32, y Vec2, z f64) { }

exit :: fn(code i32) -> ! extern


id :: fn[T](t T) -> T: t

test :: fn {
    # x: [i32; _] = [1, 2, 3]
}