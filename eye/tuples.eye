use std.c.printf

fn main {
    x := (1, 2.5)
    ptr := &x.1

    other_pointer: *f64 = &3.5

    other_pointer = ptr

    printf("Values are: %d, %f\n", x.0, x.1)
}
