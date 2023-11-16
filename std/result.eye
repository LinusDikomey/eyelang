
Result :: enum[T, E] {
    Ok(T)
    Err(E)

    unwrap :: fn(this Result[T, E]) -> T: match this {
        .Ok(value): value,
        .Err(_): panic("tried to unwrap an `Err` result")
    }
}
