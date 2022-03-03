main ->: print("Hello")


InvalidTypes :: {
    valid u32,
    invalid u33,
    also_invalid u34,
}


test(x u32, y u33, z u34, valid InvalidTypes) -> {
    print("Test Function")
}
