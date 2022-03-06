Point :: { x i32, y i32 }
SmallPoint :: { x i8, y i8 }

main -> {
    # This works at the moment but will probably be a problem for a compiler
    ty := if read("Do you want a SmallPoint? (y/n): ") == "y": SmallPoint else Point
    instance := ty(3, 5)
    print(instance, "\n")
    print(instance.x)
}
