main :: fn {
    mode := std.input("Enter operation: ")
    a := std.parse_int(std.input("First number: "))
    b := std.parse_int(std.input("Second number: "))
    std.c.printf("Result: %d\n", calc(mode, a, b))
}

calc :: fn(mode *i8, a i32, b i32) i32 {
    ret if std.streq(mode, "+"): a + b
    else if std.streq(mode, "-"): a - b
    else if std.streq(mode, "*"): a * b
    else if std.streq(mode, "/"): a / b
    else if std.streq(mode, "<<"): shl(a, b)
    else if std.streq(mode, ">>"): shr(a, b)
    else -1
}

shl :: fn(x i32, amount i32) i32: if amount <= 0: x else shl(x, amount - 1) * 2
shr :: fn(x i32, amount i32) i32: if amount <= 0: x else shr(x, amount - 1) / 2
