# print and parse are no longer intrinsics so these are added to make the program work
print(s string, ...) -> {}
parse(s string) -> i32: 0
read(msg string) -> string: ""

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
        y = y + 1
        if num < 0 {
            y = y + 3
            print("Wow, your number is negative!")
        } else {
            y = y + 4
            print("Your number is smaller than 5")
        }
    } else {
        print("Your number is at least 5")
    }


    ret test(y, 3)
}

test(i i64, b i32) -> i8: i8(i)