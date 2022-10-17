id :: fn[T](t T) -> T: t

main :: fn {
    x := id(3)
    y := id("test")

    std.c.printf("%d, %s\n", x, y)

        #-
    pair := swap(x, y)
    
    _1: *i8 = pair.a
    _2: i64 = pair.b
    -#
}

#-
Pair :: struct[A, B] {
    a A,
    b B,
}

swap :: fn[A, B](a A, b B) -> Pair[B, A]: Pair(b, a)
-#

# null :: fn[T] -> T: (0 as *T)^
# new :: fn[T] -> *T: std.c.malloc(T.size) as _
