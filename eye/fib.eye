fib(x i32) -> i32: if x < 2: x else fib(x-1) + fib(x-2)

# this is implemented with recursion instead of a loop because loops don't exist yet
fibs(n i32) -> {
    # possible syntax
    # for i in 0..n: print(...)
    if n > 0: fibs(n-1)
    print("The ", string(n), "th fibonacci number is ", string(fib(n)), "\n")
}

Point :: { x i32, y i32 }

main -> i32 {
    x := Point(3, 5)
    ret fib(x.x + x.y)
}