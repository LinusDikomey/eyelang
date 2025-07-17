use std.print

# We cast all printf arguments to i64 here because varargs actually should cast all integers to i64 
# and all floats to f64. This has to be done manually right now to get correct behaviour on all platforms.

main :: fn {
    x: u16 = 257 # 1_00000001
    ptr := &x
    std.c.printf("x = %d, ptr^ = %d\n".ptr as *i8, x as i64, ptr^ as i64)
    u8_ptr := ptr as *u8
    std.c.printf("u8_ptr^ = %d\n".ptr as *i8, u8_ptr^ as i64) # should be the same address but a value of 1

    if 257 as u8 != 257 as u8 {
        print("Something went wrong with casts")
    }
    x := 555
    # pointer casts are only possible with 'as'
    x := "Helo".ptr as *u32
    std.c.printf("Truncated: %d, 'Helo' as int x: %d\n".ptr as *i8, 257 as u8 as i64, x^ as i64)
}
