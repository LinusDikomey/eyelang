use std.c.printf

main :: fn {
    x := (1, 2.5)
    ptr := &x.1

    other_pointer: *f64 = &3.5

    other_pointer = ptr

    printf("Values are: %d, %f\n".ptr, x.0, x.1)
}
