main -> {
    x := 1
    mode := read("Enter operation: ")
    a := parse(read("First number: "))
    b := parse(read("Second number: "))
    print("Result: ", calc(mode, a, b))
}

calc(mode string, a i32, b i32) -> i32 {
    ret if mode == "+": a + b
    else if mode == "-": a - b
    else if mode == "*": a * b
    else if mode == "/": a / b
    else if mode == "<<": shl(a, b)
    else if mode == ">>": shr(a, b)
    else -1
}

shl(x i32, amount i32) -> i32: if amount <= 0: x else shl(x, amount - 1) * 2
shr(x i32, amount i32) -> i32: if amount <= 0: x else shr(x, amount - 1) / 2

#-
test(x u32) ->:
    while x > 0 {
        print("Test\n")
        x = x - 1
    }

-#
