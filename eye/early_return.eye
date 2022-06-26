main :: fn {
    std.c.printf("%d, %d, %d, %d\n", half(-3), half(0), half(1), half(7))
    std.c.printf("%s, %s\n", test(7), test(11))
    std.c.printf("%d\n", while_loop())
}


half :: fn(x i32) i32 {
    if x < 2: ret 0
    ret x / 2
}

test :: fn(num i32) *i8 {
    ret if num < 10 {
        ret "Your number is small"
    } else "Your number is at least 10"
    # some unreachable code
    x := 3
    y := 4
    if x < y { ret "" }
}

while_loop :: fn i32 {
    while true {
        ret 0
    }
    ret 1
}