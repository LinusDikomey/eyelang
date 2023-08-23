use std.queue.Queue

main :: fn {
    q := Queue.new()
    q.push_back("Other")
    print("first: ")
    println(q.first().unwrap()^)
    show(q.pop_front())
    q.push_back("A")
    q.push_back("B")
    q.push_back("C")

    print("First now: ")
    # TODO: .deref() as method doesn't work because of the additional generics
    show(Option.deref(q.first()))

    q.push_back("D")
    q.push_back("E")

    i := 0
    while i < 7 {
        show(q.pop_front())
        i += 1
    }
}

show :: fn(option Option[str]) {
    match option {
        .Some(s) {
            print("Some(")
            print(s)
            println(")")
        }
        .None: println("None")
    }
}
