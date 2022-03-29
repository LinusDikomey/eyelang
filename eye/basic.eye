
main -> i32 {
    #-
    x := std.string_to_int(std.input("Enter a number: "))
    y := std.string_to_int(std.input("Enter another number: "))
    op := std.input("Enter operation: ")
    res := -1
    if std.streq(op, "+"): res = x + y
    if std.streq(op, "-"): res = x - y
    if std.streq(op, "*"): res = x * y
    if std.streq(op, "/"): res = x / y
    if std.streq(op, "%"): res = x % y

    std.c.printf("%d %s %d = %d\n", x, op, y, res)
    
    std.println("This source file will now be read and printed:")
    std.print(std.file.read_to_string("eye/basic.eye"))
    -#
    x := 3
    y := 5
    ret x
}
