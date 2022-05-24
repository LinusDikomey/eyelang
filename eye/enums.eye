fn main {
    status := if 1 < 2: .MathWorks else .MathIsBroken

    std.println(if status == .MathWorks: "Math is ok" else "Math is broken")
}