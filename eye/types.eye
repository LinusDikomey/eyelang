Point :: { x i32, y i32 }
SmallPoint :: { x i8, y i8 }

main -> {
    # This is a type mismatch for the typechecker
    # ty := if read("Do you want a SmallPoint? (y/n): ") == "y": SmallPoint else Point
    ty := SmallPoint
    instance := ty(3, 5)
    print(instance, "\n")
    print(instance.x, "\n")

    unit := ()
    print("unit type: ", unit, "\n")

    unit2: () = if 1 < 2: unit else ()
    ret unit2
}
