SomeEnum :: Variant: {x I32, y String} | OtherVariant | ThirdVariant: {}

Option T :: Some(T) | None # Problem: ambiguous syntax with optional braces
# when there is a block here (like inside a function) (or a tuple assignment: (x, y) = ...)
{

}

Maybe T :: Just(t) | Nothing deriving Clone

AStruct :: (
    x i32
)