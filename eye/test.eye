sayHello(newline bool) -> { print("Hello", if newline: "\n" else "";); }
bye -> { print("Bye"); }

add(x i32, y i32) -> i32: x + y;

abs(x i32) -> i32: if x < 0: -x else x;;

main -> {
    print(abs(-4), "\n");
    v := Vec3(1.0, 2.5, 3.0);
    print("Vec before assignment: ", v, "\n");
    v.y = 3.1;
    print("Vec after assignment: ", v, "\n");
    print("x: ", v.x, "\n");
    name := read("What's your name? ");
    sayHello(false);
    print(", ");
    print(name, "\n");
    inp := parse(read("Enter number: "));
    print("You entered: ", inp, "\n");
    
    x := 4;

    if inp < 5:
        print("Your number is smaller than 5\n")
    else
        print("Your number is 5 or larger\n");

    y: i32 = inp / 2;
    print("Half your number is: ", y, "\n");
    print("Some calculations:\n");
    test()("Calling return value from test()\n");
    bye();
}

test -> string {
    print("Printing from test()\n");
    ret print;
}

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