Person :: {
    name string,
    age u32
}

main -> {
    p := Person("Linus", 18);
    print(p);
    print(p.name);
    assert(abs(-3) == abs(3));
    assert(p.name == "Linus");
}

abs(x:i32) -> u32 {
    if x < 0 {
        ret u32 -x;
    } else {
        ret u32 x;
    };
}

assert(b: bool) -> {
    if b {} else {
        panic("Assert failed");
    };
}