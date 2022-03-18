
printf(s string, ...) -> i32 extern

main -> i32 {
    printf("The result is %d\n", 1 + 2 * 4)
    printf("Hello World\n")
    ret Point(1, 2).x + Point(3, 4).y
}

Point :: { x i32, y i32 }