use std.c.printf

fn main {
    arr: [u8; _] = [65, 66, 67, 68, 0]
    print_as_string(arr)
    increment(&arr(2))
    print_as_string(arr)
    arr(0) += 32
    print_as_string(arr)
}

fn increment(x *u8): x^ += 1

fn print_as_string(arr [u8; 5]) {
    printf("%s\n", &arr)
}