main -> i8 {
    s := "Hello World"
    x := 3
    x = 4
    y := x + 5 * 2
    print(s, ", ", string(y), "\n")

    unknownInt := 4 # i32 should be chosen when no other information is known
    print(string(unknownInt), "\n")

    x := if 1 < 2: 5 else x

    num := parse(read("Enter a number: "))
    if num < 5 {
        if num < 0 {
            print("Wow, your number is negative!")
        } else {
            print("Your number is smaller than 5")
        }
    } else {
        print("Your number is at least 5")
    }


    ret test(y, 3)
}

test(i i64, b i32) -> i8: 3