# eyelang

A basic programming language. The compiler is written in rust using LLVM as its backend.
A simple unoptimized x86 backend is also on it's way.

## Ideas
- Runtime Speed: The language should make it possible to write code about as fast as C.
- Short syntax: Shorter code is more fun to write and easier to read.
- Type inference: Having to write less types makes the code shorter and refactoring easier.
- Compilation speed: Compilation speed over a few seconds makes debugging painfully slow.
- Simplicity: Syntax features are nice but too many of them make the language too complicated.


## Examples

### Basic
```
fn main {
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

fn add_pointer_values(x *i32, y *i32) i32: x^ + y^

fn main {
    x := 5
    y := 7
    printf("Result: %d\n", add_pointer_values(&x, &y))
}
```

### Expressions, type inference
```
fn add(x i64, y i64) i32: x + y

fn main {
    x := 3 # x is inferred to have type i64
    pointer := &x
    std.c.printf("Result: %d\n", if 1 < 2: add(pointer^, 4) else -1)
}
```

### Heap allocation
```
use std.c

Vec3 :: { x f64, y f64, z f64 }

fn print_vec3(v *Vec3) {
    c.printf("Vec3: [%.1f, %.1f, %.1f]\n", v^.x, v^.y, v^.z)
}

fn main {
    v := c.malloc(12) as *Vec3
    v^ = Vec3(1.0, 2.0, 3.0)
    print_vec3(v)
}
```
