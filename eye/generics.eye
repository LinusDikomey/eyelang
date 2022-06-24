fn main {
    v1 := Vec2("A", "B")
    v2 := Vec2(2, 5)
    v3 := Vec2(3.5, 7.3)
    some_variable: f64 = v3.x
    
    std.c.printf("The value of the Vectors: [%s, %s], [%d, %d], [%f, %f]\n", v1.x, v1.y, v2.x, v2.y, v3.x, v3.y)

    v := Vec2(Vec2(2.5, 4.3), Vec2(3.5, f64 3.6))
    std.c.printf("[[%f, %f], [%f, %f]]", v.x.x, v.x.y, v.y.x, v.y.y)
}

Vec2[T] :: {
    x T,
    y T,
}