
# a constant without a specific integer type is inferred to i32
X :: 42
ONE :: 1

# simple calculation
CALC :: 3 + 3 * 9 + (12 % 8) - (5 / 2)

# dependant constants (TODO: reenable when this works again)

PI :: 3.14159
PI_SQUARED :: 9.87 #PI * PI

main :: fn {

    # constant can be used as any integer type (TODO: reenable when this works again)
    x: i32 = X
    y: u64 = 42 # X
    z: i16 = 1 # ONE
    std.c.printf("%d, %d, %d, %d\n".ptr as *i8, x, y, z as i64, CALC)

    A :: 1 < 2
    B :: 1 > 2

    if !A or B {
        std.c.printf("Invalid constant values: %d, %d\n".ptr as *i8, A, B)
    }

    std.c.printf("%.1f, %.1f\n".ptr as *i8, PI as f64, PI_SQUARED as f64)
}
