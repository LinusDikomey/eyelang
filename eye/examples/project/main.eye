
# fn printf(fmt *i8, ...) i32 extern
use std.c.printf

Point :: struct { x i32, y i32 }

use folder.file # modules can be used of course

main :: fn {
    p := Point(4, 2)
    printf("Hello World: %d\n", other.add(p.x, 2))
    printf("Square Magnitude of Point: %d\n", other.squareMag(p))
    # use file.function # this is not implemented yet (local use statements)
    file.function()
}
