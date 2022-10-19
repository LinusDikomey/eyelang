
printf :: fn(fmt *i8, ...) extern

# add :: fn[T](a T, b T) -> T: a + b

# swap :: fn[A, B](a A, b B) -> (B, A): (b, a)
swap :: fn(a i64, b f64) -> (f64, i64): (b, a)

main :: fn {
    x := 1 # add(1, 3)
    y := 1.5 # add(0.1, 0.2)

    tuple := swap(x, y)
    y2 : f64 = tuple.0
    x2 := tuple.1
    
    printf("%d = %d, %f = %f\n", x, x2, y, y2)
    z: i64 = x # makes x infer to i64
}

