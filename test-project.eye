
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

my_function :: fn -> i32: 5

main_function :: fn() -> usize {
    # my_global = 1
    x := 3
    x = 4
    # x += ANSWER
    my_function()
    ret my_function() as _
}
