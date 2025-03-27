
main :: fn {
    x: u16 = GenericTrait.f(S())
}


S :: struct {

}

GenericTrait :: trait[T] {
    f :: fn(this Self) -> T
} for {
    impl[T] _[T] for S {
        f :: fn(this S) -> T {
            print("Size of T: ")
            println(T.size)
            std.c.exit(0)
        }
    }
}
