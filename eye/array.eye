use std.c.printf

fn main {
    arr: [u8; _] = [65, 66, 67, 68, 0]
    printf("%s\n", &arr)
    arr(2) += 1
    a(arr)
}


fn a(arr [u8; 5]) {
    printf("%s\n", &arr)
}