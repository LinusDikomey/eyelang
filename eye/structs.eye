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

main -> u8 {
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

assert(b bool) ->: if not(b): panic("Assert failed")

# bool invert (!) operator is not yet implemented so this is needed
not(b bool) -> bool: if b: false else true