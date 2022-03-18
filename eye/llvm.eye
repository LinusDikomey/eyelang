
malloc(size u64) -> string extern
printf(s string, ...) -> i32 extern
fopen(filename string, mode string) -> i64 extern
fgets(buf string, n i32, file i64) -> string extern
fputs(s string, file i64) -> i32 extern
fclose(file i64) -> i32 extern

main -> u8 {
    printf("Hello World\n")
    f := fopen("eye/test.txt", "r")
    if f == 0 {
        printf("Could not open file\n")
    } else {
        buf := malloc(15)
        content := fgets(buf, 15, f)
        printf("Read from the file: %s\n", content)
        fclose(f)
    }
    #-
    printf("The result is %d\n", 1 + 2 * 4)
    printf("Hello World\n")
    # ret Point(1, 2).x + Point(3, 4).y
    -#
    ret 8
}

Point :: { x i32, y i32 }