
main :: fn {
    x := 3
    y := &x
    y^ = 4
    std.c.printf("x is %d, y^ is: %d\n".ptr, x, y^)

    add_to(y, 5)

    std.c.printf("x is %d, y^ is: %d\n".ptr, x, y^)
    double_ptr_add(&y, 3)

    std.c.printf("x is %d, y^ is: %d\n".ptr, x, y^)
}

add_to :: fn(i *i64, amount i64) {
    i^ += amount
}

double_ptr_add :: fn(i **i64, amount i64) {
    i^^ += amount
}