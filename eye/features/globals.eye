use std.println
use std.int_to_str

global_int: i32

global_struct: Vec2

main :: fn {
    global_int = 3
    global_struct = Vec2(1, 2)
    println(int_to_str(global_int))
    println(int_to_str(global_int))
    inc_global()
    print_from_other()
    std.c.printf("[%d, %d]\n".ptr, global_struct.x, global_struct.y)
    global_struct.print()
    global_struct.x += global_struct.y
    global_struct.print()
}

inc_global :: fn: global_int += 1

print_from_other :: fn {
    println(int_to_str(global_int))
}

Vec2 :: struct {
    x i32,
    y i32,

    print :: fn(self Vec2) {
        std.c.printf("[%d, %d]\n".ptr, self.x, self.y)
    }
}