
use root.Point

add(x i32, y i32) -> i32 {
    root.printf("Hello From Add\n")
    ret x + y
}

squareMag(p Point) -> i32: p.x * p.x + p.y * p.y