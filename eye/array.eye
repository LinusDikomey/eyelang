use std.c.printf

fn main {
    arr: [u8; _] = [65, 66, 68, 0, 0, 0, 0, 0, 0, 0]
    a(arr)
    printf("%s\n", &arr)
}


fn a(arr [u8; 10]) {
    printf("%s\n", &arr)
}