
Option :: enum[T] {
    Some(T)
    None

    is_some :: fn(this *Option[T]) -> bool: match this^ {
        .Some(_): true,
        .None: false
    }
    is_none :: fn(this *Option[T]) -> bool: match this^ {
        .Some(_): false,
        .None: true
    }
}

