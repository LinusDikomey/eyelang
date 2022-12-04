main :: fn {
    a := Vec2.zero()
    b := Vec2(3, 4)
    a.print()
    b.print()
    b = b.add(Vec2(2, 7))
    b.print()
    # Vec2.zero().print()  this doesn't work yet
    Vec2(5, 6).print()
}

Vec2 :: struct {
    x i32,
    y i32,

    zero :: fn() -> Vec2: Vec2(0, 0)
    add :: fn(a Vec2, b Vec2) -> Vec2 {
        a.x += b.x
        a.y += b.y
        ret a
    }
    print :: fn(v Vec2) { std.c.printf("[%d, %d]\n".ptr, v.x, v.y) }
    
}
