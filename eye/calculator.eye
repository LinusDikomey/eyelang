# This doesn't work right now because string equality is not implemented

printf(s string, ...) -> i32 extern
malloc(size u64) -> string extern
scanf(s string, ...) -> i32 extern

# print, parse and read are no longer intrinsics so these are added to make the program work
print(s string, ...) -> { printf(s) }
parse(s string) -> i32: 0
read(msg string) -> string {
    printf(msg)
    buf := malloc(256)
    scanf("%s", buf) # this is actually a bad idea because the string buffer might overflow
    ret buf
}

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
