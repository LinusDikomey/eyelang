

Vec2 :: struct[T] {
    x T,
    y T
}

#-f :: fn[T] {
    x := 3
}-#

main :: fn {
    v1 := Vec2(3, 5)
    v2 := Vec2("Hello", "World")
    v3 := Vec2(Vec2(2., 3.), Vec2(3, 4))

    x: u8 = 3
    y: u16 = x
    # std.c.printf("%d %d %s %s", v1.x, v1.y, v2.x, v2.y)
}

# TODO: important typechecker bug
#-
    x := 5
    y: u8 = 4
    x *= y
    f:: fn(x u16) {}
    f(x)
-#