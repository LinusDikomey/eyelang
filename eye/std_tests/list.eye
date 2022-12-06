use std.list.List

main :: fn {

    numbers := List.new()
    numbers.printf_all("%d".ptr)
    numbers.push(1)
    numbers.push(2)
    numbers.push(3)
    numbers.printf_all("%d".ptr)
    numbers.push(4)
    numbers.printf_all("%d".ptr)
    numbers.push(5)
    numbers.printf_all("%d".ptr)
}