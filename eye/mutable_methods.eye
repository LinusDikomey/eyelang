
Vec2 :: struct {
    x i32,
    y i32,

    inc :: fn(this *Vec2) {
        this^.x += 1
        this^.y += 1
    }
    print :: fn(this Vec2) {
        std.c.printf("[%d, %d]\n", this.x, this.y)
    }
    doubled :: fn(this Vec2) -> Vec2: Vec2(2 * this.x, 2 * this.y)
    doubled_ptr :: fn(this *Vec2) -> Vec2: Vec2(2 * this^.x, 2 * this^.y)
}

main :: fn {

    v := Vec2(1, 2)
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
