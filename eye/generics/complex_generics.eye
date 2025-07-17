

Pair :: struct[A, B] {
    a A,
    b B,
}

swap_second :: fn[A1, A2, B](p1 *Pair[A1, B], p2 *Pair[A2, B]) {
    tmp := p1^.b
    p1^.b = p2^.b
    p2^.b = tmp
}

main :: fn {
    p1 := Pair(a: 1, b: "Hello")
    p2 := Pair(a: 1.5, b: "Bye")

    std.c.printf("%s, %s\n".ptr as *i8, p1.b.ptr, p2.b.ptr)
    swap_second(&p1, &p2)
    std.c.printf("%s, %s\n".ptr as *i8, p1.b.ptr, p2.b.ptr)
}
