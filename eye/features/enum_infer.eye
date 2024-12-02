
main :: fn {
    # tests that enums can be assigned to each other while maintaining correct enum ordinals
    # everywhere
    a := .Apple
    a = .Banana
    b := .Banana
    a = b
    match a {
        .Apple: println("apple"),
        .Banana: println("banana"),
        .Citrus: println("citrus"),
    }
}
