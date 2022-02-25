Person :: {
    name string,
    age u32
}

main -> u8 {
    x := (1 + 2) * 3
    p := Person("Linus", 18)
    print(p, "\n")
    print(p.name, "\n")
    assert(abs(-3) == abs(3))
    assert(p.name == "Linus")

    ret u8 p.age
}

abs(x i32) -> u32 {
    ret u32 if x < 0: -x else x
}

assert(b bool) -> {
    if b {} else {
        panic("Assert failed")
    }
}