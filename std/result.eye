
Result :: enum[T, E] {
  Ok(T)
  Err(E)

  or_panic :: fn(this Result[T, E]) -> T: match this {
    .Ok(value): value,
    .Err(_): panic("tried to unwrap an `Err` result"),
  }

  or_panic_with :: fn(this Result[T, E], message str) -> T: match this {
    .Ok(value): value,
    .Err(_): panic(message),
  }
}
