use std.assert

main :: fn {
    x: i64 = GenericTrait.f("")
    assert(x == 10, "i64 impl")
    x: i32 = GenericTrait.f("")
    assert(x == 5, "i32 impl")
    println("Selection OK")
    # TODO: defaulting doesn't work yet
    # assert(GenericTrait.f("") == 5, "should default to i32")

    # TODO: doesn't work yet when inlining into println (bound unification)
    s := GenericTrait.f(S())
    println(s)
}


GenericTrait :: trait[T] {
    f :: fn(this Self) -> T
} for {
    impl _[i32] for str {
        f :: fn(this str) -> i32: 5
    }

    impl _[i64] for str {
        f :: fn(this str) -> i64: 10
    }
}

S :: struct {
    impl GenericTrait[str] {
        f :: fn(this S) -> str: "S"
    }
}
