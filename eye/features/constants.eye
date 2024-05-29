
# a constant without a specific integer type
X :: 42

ONE :: 1

# simple calculation
CALC :: 3 + 3 * 9 + (12 % 8) - (5 / 2)

# dependant constants

PI :: 3.14159
PI_SQUARED :: PI * PI

main :: fn {

    # constant can be used as any integer type
    x: i32 = X
    y: u64 = X
    z: i16 = ONE
    std.c.printf("%d, %d, %d, %d\n".ptr, x, y, z as i64, CALC)

    A :: 1 < 2
    B :: 1 > 2

    if !A or B {
        std.c.printf("Invalid constant values: %d, %d\n".ptr, A, B)
    }

    std.c.printf("%.1f, %.1f\n".ptr, PI as f64, PI_SQUARED as f64)
}
