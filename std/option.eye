
Option :: enum[T] {
    Some(T)
    None

    sus :: fn(this *Option[T]) {
        this.is_some()
    }

    is_some :: fn(this *Option[T]) -> bool: match this^ {
        .Some(_): true,
        .None: false
    }
    is_none :: fn(this *Option[T]) -> bool: match this^ {
        .Some(_): false,
        .None: true
    }
}

bruh :: fn {
    x: Option = .Some(3)
    x.is_some()
}
