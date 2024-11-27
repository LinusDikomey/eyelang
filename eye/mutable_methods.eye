
Vec2 :: struct {
    x i32,
    y i32,

    inc :: fn(this *Vec2) {
        this^.x += 1
        this^.y += 1
    }
    print :: fn(this Vec2) {
        std.c.printf("[%d, %d]\n".ptr, this.x, this.y)
    }
    doubled :: fn(this Vec2) -> Vec2: Vec2(x: 2 * this.x, y: 2 * this.y)
    doubled_ptr :: fn(this *Vec2) -> Vec2: Vec2(x: 2 * this^.x, y: 2 * this^.y)
}

main :: fn {

    v := Vec2(x: 1, y: 2)
    v.inc()
    v.print()

    v.doubled().print()
    v.doubled().print()
    v.doubled().doubled().print()

    v.doubled_ptr().print()
    v.doubled().doubled_ptr().print()
    v.doubled_ptr().doubled().print()
    v.doubled_ptr().doubled_ptr().print()
}
