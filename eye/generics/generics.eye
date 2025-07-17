main :: fn {
    v1 := Vec2(x: "A", y: "B")
    v2 := Vec2(x: 2, y: 5)
    v3 := Vec2(x: 3.5, y: 7.3)
    some_variable: f64 = v3.x

    std.c.printf("The value of the Vectors: [%s, %s], [%d, %d], [%f, %f]\n".ptr as *i8, v1.x.ptr, v1.y.ptr, v2.x, v2.y, v3.x, v3.y)

    v := Vec2(x: Vec2(x: 2.5, y: 4.3), y: Vec2(x: 3.5, y: 3.6 as f64))
    std.c.printf("[[%f, %f], [%f, %f]]".ptr as *i8, v.x.x, v.x.y, v.y.x, v.y.y)
}

Vec2 :: struct[T] {
    x T,
    y T,
}
