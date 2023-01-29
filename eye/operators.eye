
assert :: fn(b bool): if !b: println("An assertion failed!")

main :: fn {
    bools()
    arithmetic()
    comparisons()
    assign()
}

bools :: fn {
    assert(true)
    assert(!false)
    assert(!!true)
    assert(false == false)
    assert(true == true)

    assert(true != false)
    assert(false != true)
    
    assert(!false == true)

    assert((true or true) == true)
    assert((true or false) == true)
    assert((false or true) == true)
    assert((false or false) == false)

    assert((true and true) == true)
    assert((true and false) == false)
    assert((false and true) == false)
    assert((false and false) == false)
}

arithmetic :: fn {
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

comparisons :: fn {
    assert(1 < 2)
    assert(2 > 1)
    assert(1 <= 3)
    assert(-5 < -4)
    assert(4 <= 4)
    assert(-5 >= -5)
    assert(3 > 2)
}

Point :: struct { x i32, y i32 }

assign :: fn {
    x := 3
    x += 1
    assert(x == 4)
    x -= 1
    assert(x == 3)
    x *= 4
    assert(x == 12)
    x /= 3
    assert(x == 4)
    x %= 3
    assert(x == 1)

    p := Point(1, 13)
    p.x += 3
    assert(p.x == 4)
    p.y %= 5
    assert(p.y == 3)
}
