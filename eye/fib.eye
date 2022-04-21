use std.c.printf

fn fib(x i32) i32: if x < 2: x else fib(x-1) + fib(x-2)

# this is implemented with recursion instead of a loop because loops don't exist yet
fn fibs(n i32) {
    # possible syntax
    # for i in 0..n: print(...)
    if n > 0: fibs(n-1)
    printf("The %d th fibonacci number is %d\n", n, fib(n))
}

Point :: { x i32, y i32 }

fn main {
    x := Point(3, 5)
    printf("Result: %d\n", fib(x.x + x.y))
}