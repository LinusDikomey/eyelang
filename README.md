# eyelang

A basic programming language. The compiler is written in rust using LLVM as its backend.
A simple unoptimized x86 backend is also on it's way.

## Examples

```
main -> {
    std.println("Hello World")
    x := 3
    y := 2 * x + 3
    y += 1
    std.c.printf("X is %d and y is %d\n", x, y)
}
```

### Functions and pointers
```
use std.c.printf

add_pointer_values(x *i32, y *i32) -> i32: ~x + ~y

main -> {
    x := 5
    y := 7
    printf("Result: %d\n", add_pointer_values(&x, &y))
}
```

## Philosophy
- Runtime Speed: The language should make it possible to write code about as fast as C.
- Short syntax: Shorter code is more fun to write and easier to read.
- Type inference: Having to write less types makes the code shorter and refactoring easier.
- Compilation speed: Compilation speed over a few seconds makes debugging painfully slow.
- Simplicity: Syntax features are nice but too many of them make the language too complicated.
