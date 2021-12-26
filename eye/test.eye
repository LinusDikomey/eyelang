print(s: string, newline: bool) -> { }
read(s: string) -> string { }
parse(s: string) -> i32 { }


sayHello(newline: bool) -> { print("Hello", newline); }
bye -> { print("Bye"); }

main -> {
    name := read("What's your name? ");
    sayHello(false);
    print(", ", false);
    print(name);
    inp := parse(read("Enter number: "));
    print("You entered: ", false);
    print("inp");
    x := 4;

    if inp < 5 {
        print("Your number is smaller than 5");
    } else {
        print("Your number is 5 or larger");
    };
    print("Half your number is:");
    y: i32 = inp / 2;
    print(y);
    print("Some calculations:");
    test()("Calling return value from test()");
    bye();
}

test -> string {
    print("Printing from test()");
    ret print;
}
add(x: i32, y: i32) -> i32 { ret x+y; }

Vec3 :: {
    x f32,
    y f32,
    z f32
}

Transform :: {
    pos Vec3,
    rot Vec3,
    scale Vec3
}

commentTest -> {
    # this is a comment
    #*
    This is a
    multiline comment
    *#
    #* nested #* multiline *# comment *#

    # Multiline in #*
    comment
    *#
    # #* *# Still a comment after multiline
}