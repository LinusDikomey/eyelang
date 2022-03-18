
puts(s string) -> i32 extern

main -> i32 {
    puts("Hello World")
    ret Point(1, 2).x + Point(3, 4).y
}

Point :: { x i32, y i32 }