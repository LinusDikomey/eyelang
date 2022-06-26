
main :: fn {
    std.c.printf("Hello, World\n")
    r := 2.5
    area := circle_area(r)
    std.c.printf("Area of circle with radius %.1f: %.2f\n, ", r, area)
}

PI :: 3.14

circle_area :: fn(r f64) f64: PI * r * r