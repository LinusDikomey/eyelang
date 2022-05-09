fn getchar() extern
fn printf(msg *i8, ...) i32 extern

fn main {
    x := calc(7, 3)
    getchar()
    printf("Hello World %d\n", x)
}


fn calc(a i32, b i32) i32: a + a + b