main :: fn {
    f := MyAdd()
    x := Fn.call(&f, (3, 5))
    println(x)
}

MyAdd :: struct {}

Fn :: trait[Args, Output] {
    call :: fn(this *Self, args Args) -> Output
} for {
    impl _[(i32, i32), i32] for MyAdd {
        call :: fn(this *MyAdd, args (i32, i32)) -> i32 {
            ret args.0 + args.1
        }
    }
}

