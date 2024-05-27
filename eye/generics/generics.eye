main :: fn {
    v1 := Vec2("A", "B")
    v2 := Vec2(2, 5)
    v3 := Vec2(3.5, 7.3)
    some_variable: f64 = v3.x
    
    std.c.printf("The value of the Vectors: [%s, %s], [%d, %d], [%f, %f]\n".ptr, v1.x.ptr, v1.y.ptr, v2.x, v2.y, v3.x, v3.y)

    v := Vec2(Vec2(2.5, 4.3), Vec2(3.5, 3.6 as f64))
    std.c.printf("[[%f, %f], [%f, %f]]".ptr, v.x.x, v.x.y, v.y.x, v.y.y)
}

Vec2 :: struct[T] {
    x T,
    y T,
}
