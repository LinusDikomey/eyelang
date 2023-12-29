
ANSWER :: 42

main :: main_function

Vec2 :: struct {
    x i32
    y i32
}

# identity :: fn[T](t T) -> T: t

usize :: u64

mul :: fn(a Vec2, b Vec2) -> Vec2 extern

my_global: usize = 3

main_function :: fn -> i32 {
    my_global = 1
    # x := 3
    # x += ANSWER
    ret ANSWER
}
