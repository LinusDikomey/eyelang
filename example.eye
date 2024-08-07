
main :: fn {
    println("Hello, World")
    r := 2.5
    area := circle_area(r)
    std.c.printf("Area of circle with radius %.1f: %.2f\n".ptr, r, area)

    f := .Apple
    if area < 20.0 {
        # The enum can be named explicitly but it doesn't have to be if the type can be inferred
        f = Fruit.Banana
    }
    # This would give an error because 'Pear' is not defined in the enum
    # f = .Pear

    println(fruit_to_string(f))
}

PI :: 3.14

circle_area :: fn(r f64) -> f64: PI * r * r

Fruit :: enum { Apple, Banana }

fruit_to_string :: fn(f Fruit) -> str:
    if f == .Apple: "Apple"
    else "Banana"

# traits aren't finished yet and aren't usable right now
# ToString :: trait {
#     to_string :: fn -> *i8
# }
