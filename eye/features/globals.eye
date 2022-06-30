

global_int: i32

global_struct: Vec2

main :: fn {
    global_int = 3
    global_struct = Vec2(1, 2)
    std.c.printf("%d\n", global_int)
    std.c.printf("%d\n", global_int)
    inc_global()
    print_from_other()
    std.c.printf("[%d, %d]\n", global_struct.x, global_struct.y)
    global_struct.print()
    global_struct.x += global_struct.y
    global_struct.print()
}

inc_global :: fn: global_int += 1

print_from_other :: fn {
    std.c.printf("%d\n", global_int)
}

Vec2 :: struct {
    x i32,
    y i32,

    print :: fn(self *Vec2) {
        std.c.printf("[%d, %d]\n", self^.x, self^.y)
    }
}