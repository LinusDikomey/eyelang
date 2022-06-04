fn main {
    a := Vec2.zero()
    b := Vec2(3, 4)
    a.print()
    b.print()
    b.add(Vec2(2, 7))
    b.print()
    # Vec2.zero().print()  this doesn't work yet
    Vec2(5, 6).print()
}

Vec2 :: {
    x i32,
    y i32,
    fn zero() Vec2: Vec2(0, 0),  # this comma shouldn't be needed in the future
    fn add(a *Vec2, b Vec2) {
        a^.x += b.x
        a^.y += b.y
    },
    fn print(v *Vec2) { std.c.printf("[%d, %d]\n", v^.x, v^.y) }
}
