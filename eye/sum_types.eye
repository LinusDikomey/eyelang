Option :: enum[T] { Some(T) None }

main :: fn {
    opt: Option[_] = .Some(3)
    l := List.new()
    l.push(.None)
    l.push(.Some(5 as u64))
    l.push(opt)

    assert(eq(l.get(0), .None))
    assert(eq(l.get(1), .Some(5)))
    std.c.printf("%d\n".ptr, l.get(2))
    assert(eq(l.get(2), .Some(3)))
}

eq :: fn[T](a Option[T], b Option[T]) -> bool: match a {
    .Some(a): if .Some(b) := b: a == b else false,
    .None: if .None := b: true else false
}

assert :: fn(b bool) {
    if !b: panic("assertion failed")
}
