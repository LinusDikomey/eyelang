fn main {
    v1 := Vec2("A", "B")
    v2 := Vec2(2, 5)
    v3 := Vec2(3.5, 7.3)
    some_variable: f64 = v3.x
    
    std.c.printf("The value of the Vectors: [%s, %s], [%d, %d], [%f, %f]\n", v1.x, v1.y, v2.x, v2.y, v3.x, v3.y)

    # TODO: recursive generics have some bugs and don't work right now
    #-
    v := Vec2(Vec2(3, 4), Vec2(f64 3.5, 3.6))
    std.c.printf("[[%d, %d], [%f, %f]]", v.x.x, v.x.y, v.y.x, v.y.y)
    -#
}

Vec2 :: [T] {
    x T,
    y T,
}