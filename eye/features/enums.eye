main ::fn {
    status := if 1 < 2: .MathWorks else .MathIsBroken

    std.println(if .MathWorks := status: "Math is ok" else "Math is broken")
}
