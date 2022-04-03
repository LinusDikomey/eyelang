
main -> {
    x := 3
    y := &x
    ~y = 4

    std.c.printf("y is: %d, x is %d, ~y is: %d\n", y, x, ~y)

    add_to(y, 5)

    std.c.printf("y is: %d, x is %d, ~y is: %d\n", y, x, ~y)
    double_ptr_add(&y, 3)

    std.c.printf("y is: %d, x is %d, ~y is: %d\n", y, x, ~y)
}

add_to(i *i64, amount i64) -> {
    ~i += amount
}

double_ptr_add(i **i64, amount i64) -> {
    ~~i += amount
}