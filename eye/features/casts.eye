use std.print

# We cast all printf arguments to i64 here because varargs actually should cast all integers to i64 
# and all floats to f64. This has to be done manually right now to get correct behaviour on all platforms.

main :: fn {
    x: u16 = 257 # 1_00000001
    ptr := &x
    std.c.printf("x = %d, ptr^ = %d\n".ptr, i64(x), i64(ptr^))
    u8_ptr := ptr as *u8
    std.c.printf("u8_ptr^ = %d\n".ptr, i64(u8_ptr^)) # should be the same address but a value of 1

    if u8 257 != 257 as u8 { # these are equivalent but the first variant can only take primitives
        print("Something went wrong with casts")
    }
    x := 555
    # pointer casts are only possible with 'as'
    x := "Helo".ptr as *u32
    std.c.printf("Truncated: %d, 'Helo' as int x: %d\n".ptr, i64(u8 257), i64(x^))
}
