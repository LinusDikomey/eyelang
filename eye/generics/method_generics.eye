use std.c.printf

swap :: fn[A, B](a A, b B) -> (B, A): (b, a)

fib :: fn[T](n T) -> T: match n {
    0: 0,
    1: 1,
    _: fib(n-1) + fib(n-2)
}

main :: fn {
    x := 1
    y := 1.5

    tuple := swap(x, y)
    y2 : f64 = tuple.0
    x2 := tuple.1
    
    fib_a: i32 = fib(10)
    fib_b: u64 = fib(10)
    
    printf("%d, %d\n", fib_a, fib_b)

    printf("%d = %d, %f = %f\n", x, x2, y, y2)
    z: i64 = x # makes x infer to i64

    v := Vec2(1, 2)
    v2: Vec2[u64] = Vec2(3, 4)
    v3: *Vec2 = new()
    v3^.x = 5
    v3^.y = 6
    
    v.print()
    v2.print()
    v3^.print()

    v.mul(2)
    v2.mul(3)
    v3^.mul(4)

    v.print()
    v2.print()
    v3^.print()
}

use std.c.malloc

new :: fn[T] -> *T {
    size := T.size
    printf("Instantiating with size %d\n", size)
    ret malloc(size) as *T
}

Vec2 :: struct[T] {
    x T,
    y T,

    print :: fn(this *Vec2[T]) {
        x := this^.x
        printf("[%d, %d]\n", x, this^.y)
    }

    mul :: fn(this *Vec2[T], scalar T) {
        this^.x *= scalar
        this^.y *= scalar
    }
}