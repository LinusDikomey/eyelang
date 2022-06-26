use std.c

Vec3 :: struct { x f64, y f64, z f64 }

print_vec3 :: fn(v *Vec3) {
    c.printf("Vec3: [%.1f, %.1f, %.1f]\n", v^.x, v^.y, v^.z)
}

main :: fn {
    v := c.malloc(12) as *Vec3
    v^ = Vec3(1.0, 2.0, 3.0)
    print_vec3(v)
}