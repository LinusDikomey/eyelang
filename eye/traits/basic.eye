
main :: fn {
    # primitives don't really work yet since the syntax
    # special-cases primitives in a bunch of places
    # println(i32.type_name())
    println(MyStruct.type_name())
    println(MyEnum.type_name())
}


TypeName :: trait {
    type_name :: fn -> str
} for {
    impl i32 {
        type_name :: fn -> str: "i32"
    }
    impl MyStruct {
        type_name :: fn -> str: "MyStruct"
    }
    impl MyEnum {
        type_name :: fn -> str: "MyEnum"
    }
}

MyStruct :: struct { }

MyEnum :: enum { }
