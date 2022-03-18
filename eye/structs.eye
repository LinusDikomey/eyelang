Person :: {
    first_name string,
    last_name string,
    age u32
}

welcome(p Person) ->:
    print(
        "Hello, my name is ",
        p.first_name, " ", p.last_name,
        " and I am ", string(p.age), if p.age > 1: " years" else " year", " old!\n"
    )

Test :: { x f32, y i32 }

main -> u8 {
    vec := Test(1.0, 2)
    vec.x = 3.5
    print(string(vec), "\n")

    p := Person("John", "Doe", 42)
    print(string(p), "\n")
    print(p.first_name, "\n")
    welcome(p)
    # assert(p.first_name == "John") # string comparisons aren't implemented in the compiler right now
    x: i32 = 10 - i32 p.age
    assert(abs(x) == 32)
    ret u8 p.age
}

abs(x i32) -> u32: u32 if x < 0: -x else x

assert(b bool) ->: if b == false: print("Assert failed")