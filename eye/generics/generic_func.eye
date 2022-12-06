id :: fn[T](t T) -> T: t

main :: fn {
    x := id(3)
    y := id("test")
    z := &x
    w: i64 = z^
    std.c.printf("%d, %s\n".ptr, x, y)
}

