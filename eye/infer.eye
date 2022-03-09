main -> i8 {
    s := "Hello World"
    x := 3
    y := x + 5 * 2
    print(s, string(y))

    unknownInt := 4 # i32 should be chosen when no other information is known
    print(string(unknownInt))

    ret test(y, 3)
}

test(i i64, b i32) -> i8: 3