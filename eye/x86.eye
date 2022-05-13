fn getchar() extern
fn printf(msg *i8, ...) i32 extern

fn main {
    x := calc(7, 3)
    getchar()
    printf("Hello World %d\n", x)
}


fn calc(a i64, b i64) i64: a / b