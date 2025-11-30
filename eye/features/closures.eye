main :: fn {
  x := 5
  inside_g := "string used in g called with "
  g := fn(a _) {
    print(inside_g)
    println(a)
  }
  f := fn(a _) {
    g(1 + a)
    g(2 + a)
    println("called f")
    u := x
    v := a
    z := u * v
    ret 12 * a + a
  }

  f(42)
  println(call_twice(f))
}

call_twice :: fn[F: std.call.Fn[(i64), i64]](f F) -> i64: f(0) + f(1)
