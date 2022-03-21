
add(x i32, y i32) -> i32 {
    root.printf("Hello From Add\n")
    ret x + y
}

printf(s string) -> i32 {
    root.printf("Evil printf\n")
    ret 3
}