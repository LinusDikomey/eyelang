main -> u8 {
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
    else -1
}