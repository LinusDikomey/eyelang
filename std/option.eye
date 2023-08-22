
Option :: enum[T] {
    Some(T)
    None

    some_if :: fn(condition bool, value T) -> Option[T]:
        if condition: .Some(value) else .None

    is_some :: fn(this *Option[T]) -> bool: match this^ {
        .Some(_): true,
        .None: false
    }

    is_none :: fn(this *Option[T]) -> bool: match this^ {
        .Some(_): false,
        .None: true
    }

    unwrap :: fn(this *Option[T]) -> T: match this^ {
        .Some(value): value,
        .None: panic("An Option containing a 'None' value was unwrapped")
    }

    unwrap_or :: fn(this *Option[T], default T) -> T: match this^ {
        .Some(value): value,
        .None: default
    }

    deref :: fn[V](this Option[*V]) -> Option[V]: match this {
        .Some(ptr): .Some(ptr^),
        .None: .None
    }
}
