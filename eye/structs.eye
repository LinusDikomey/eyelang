Person :: {
    first_name string,
    last_name string,
    age u32
}

welcome(p Person) ->:
    print(
        "Hello, my name is ",
        p.first_name, " ", p.last_name,
        " and I am ", p.age, if p.age > 1: " years" else " year", " old!\n"
    )

Test :: { x f32, y i32 }

main -> u8 {
    vec := Test(1.0, 2)
    vec.x = 3.5
    print(vec, "\n")

    p := Person("John", "Doe", 42)
    print(p, "\n")
    print(p.first_name, "\n")
    welcome(p)
    assert(p.first_name == "John")
    x: i16 = 10 - i16 p.age
    assert(abs(x) == 32)
    ret u8 p.age
}

abs(x i32) -> u32: u32 if x < 0: -x else x

assert(b bool) ->: if b == false: print("Assert failed")