
main -> {
    x: u16 = 257 # 1_00000001
    ptr := &x
    std.c.printf("x = %d, ~ptr = %d\n", x, ~ptr)
    u8_ptr := ptr as *u8
    std.c.printf("~u8_ptr = %d\n", ~u8_ptr) # should be the same address but a value of 1

    if u8 257 != 257 as u8 { # these are equivalent but the first variant can only take primitives
        std.c.printf("Something went wrong with casts")
    }
    x := 555
    # pointer casts are only possible with 'as'
    x := "Helo" as *u32
    std.c.printf("Truncated: %d, 'Helo' as int x: %d\n", u8 257, ~x)
}