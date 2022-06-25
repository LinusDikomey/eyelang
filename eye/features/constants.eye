
# a constant without a specific integer type
X :: 42

NEGATIVE_ONE :: -1

# simple calculation
CALC :: 3 + 3 * 9 + (12 % 8) - (5 / 2)

# dependant constants

PI :: 3.14159
PI_SQUARED :: PI * PI

fn main {

    # constant can be used as any integer type
    x: i32 = X
    y: u64 = X
    z: i16 = NEGATIVE_ONE
    std.c.printf("%d, %d, %d, %d\n", x, y, i64 z, CALC)

    A :: 1 < 2
    B :: 1 > 2

    if !A or B {
        std.c.printf("Invalid constant values: %d, %d\n", A, B)
    }

    std.c.printf("%.1f, %.1f\n", f64 PI, f64 PI_SQUARED)
}
