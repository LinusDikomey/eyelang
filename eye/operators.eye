
printf(fmt string, ...) -> i32 extern
assert(b bool) ->: if !b: printf("An assertion failed!\n")

main -> {
    bools()
    arithmetic()
}

bools -> {
    assert(true)
    assert(!false)
    assert(!!true)
    assert(false == false)
    assert(true == true)

    assert(true != false)
    assert(false != true)
    
    assert(!false == true)
}

arithmetic -> {
    assert(1+1 == 2)
    assert(5-3 == 2)
    assert(3*4 == 12)
    assert(12/3 == 4)
    assert(14 / 3 == 4)
    assert(5 / 2 == 2)
    assert(-5 == 5 * -1)
    assert(--4 == 4)

    assert(5 % 2 == 1)
    assert(14 % 3 == 2)
    assert(-3 % 2 == -1)
    assert(-10 % 10 == 0)
    assert(-11 % 10 == -1)
}

comparisons -> {
    assert(1 < 2)
    assert(2 > 1)
    assert(1 <= 3)
    assert(-5 < -4)
    assert(4 <= 4)
    assert(-5 >= -5)
    assert(3 > 2)
}
