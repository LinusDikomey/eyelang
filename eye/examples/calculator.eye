
main :: fn {
    mode := input("Enter operation: ")
    a := input("First number: ").parse()
    b := input("Second number: ").parse()
    std.c.printf("Result: %d\n".ptr, calc(mode, a, b))
}

calc :: fn(mode str, a i64, b i64) -> i64: match mode {
    "+": a + b,
    "-": a - b,
    "*": a * b,
    "/": a / b,
    "<<": shl(a, b),
    ">>": shr(a, b),
    _: -1
}

shl :: fn(x i64, amount i64) -> i64: if amount <= 0: x else shl(x, amount - 1) * 2
shr :: fn(x i64, amount i64) -> i64: if amount <= 0: x else shr(x, amount - 1) / 2
