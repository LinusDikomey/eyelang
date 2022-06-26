# print and parse are no longer intrinsics so these are added to make the program work
print :: fn(s *i8, ...) {}
parse :: fn(s *i8) i32: 0

sayHello :: fn(newline bool): print("Hello", if newline: "\n" else "")
bye :: fn { print("Bye") }

add :: fn(x i32, y i32) i32: x + y

abs :: fn(x i32) i32: if x < 0: -x else x
bla :: fn(x i32, y i32) {
    z := 3
    w := 5
}

main :: fn {
    # print(string(abs(-4)), "\n")
    v := Vec3(1.0, 2.5, 3.0)

    # print("Vec before assignment: ", string(v.x), " ", string(v.y), " ", string(v.z), "\n")

    v.y = 3.1
    # print("Vec after assignment: ", string(v.x), " ", string(v.y), " ", string(v.z), "\n")
    # print("x: ", string(v.x), "\n")

    name := "John Doe"
    sayHello(false)
    print(", ")
    print(name, "\n")
    inp := parse("123456789")
    # print("You entered: ", string(inp), "\n")
    
    x := 4

    if inp < 5:
        print("Your number is smaller than 5\n")
    else
        print("Your number is 5 or larger\n")

    y: i32 = inp / 2
    # print("Half your number is: ", string(y), "\n")
    print("Some calculations:\n")
    # test()("Calling return value from test()\n")

    printVec3(addVec3(Vec3(1., 2., 3.), Vec3(4., 7., 9.)))
    
    i := 5
    while i < 10: i = incAndPrint(i)
    incAndPrint :: fn(i i32) i32 {
        std.c.printf("I is %d\n", i)
        ret i + 1
    }

    {
        obj := PhysicsObject(Vec3(1, 2, 3), Vec3(4, 5, 6))
        std.c.printf("Physics Object: %d\n", obj.pos.y + obj.rot.z)
        PhysicsObject :: struct {
            pos Vec3,
            rot Vec3
        }
        Vec3 :: struct { x i32, y i32, z i32 }
    }
    # Here Vec3 means Vec3 from the global scope again
    v := Vec3(1., 2.5, 3.141)
    printVec3(v)
    bye()
}

Vec3 :: struct {
    x f32,
    y f32,
    z f32
}

addVec3 :: fn(a Vec3, b Vec3) Vec3: Vec3(a.x + b.x, a.y + b.y, a.z + b.z)
printVec3 :: fn(v Vec3) {
    std.c.printf("Vec3[%d, %d, %d]\n", i32 v.x, i32 v.y, i32 v.z)
}

Transform :: struct {
    pos Vec3,
    rot Vec3,
    scale Vec3
}

commentTest :: fn {
    # this is a comment
    #-
    This is a
    multiline comment
    -#
    #- nested #- multiline -# comment -#

    # Multiline in #-
    comment
    -#
    # #--# Still a comment after multiline
}