main -> {
    mode := read("Enter operation: ");
    a := parse(read("First number: "));
    b := parse(read("Second number: "));
    
    print("Result: ", calc(mode, a, b));
}

calc(mode string, a i32, b i32) -> i32 {
    if mode == "+" {
        ret a + b;
    };
    if mode == "-" {
        ret a - b;
    };
    if mode == "*" {
        ret a * b;
    };
    if mode == "/" {
        ret a / b;
    };
    ret -1;
}