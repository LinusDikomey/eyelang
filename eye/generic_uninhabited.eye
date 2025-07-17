

Foo :: enum {}

main :: fn {
    x: Foo = g()
}

g :: fn[T] -> T: f().0

f :: fn[T] -> (T, T) {
    panic("f panic")
}


