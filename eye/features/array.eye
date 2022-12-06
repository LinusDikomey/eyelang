use std.c.printf
use std.string.str
use std.println

main :: fn {
    arr: [u8; _] = [65, 66, 67, 68, 0]
    print_as_string(arr)
    increment(&arr[2])
    print_as_string(arr)
    arr[0] += 32
    print_as_string(arr)
}

increment :: fn(x *u8): x^ += 1

print_as_string :: fn(arr [u8; 5]) {
    println(str.from_cstr(&arr as *i8))
}