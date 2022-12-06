

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
    p1 := Pair(1, "Hello")
    p2 := Pair(1.5, "Bye")

    std.c.printf("%s, %s\n".ptr, p1.b.ptr, p2.b.ptr)
    swap_second(&p1, &p2)
    std.c.printf("%s, %s\n".ptr, p1.b.ptr, p2.b.ptr)
}