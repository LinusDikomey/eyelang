SomeEnum :: Variant: {x I32, y *i8} | OtherVariant | ThirdVariant: {}

Option T :: Some(T) | None # Problem: ambiguous syntax with optional braces
# when there is a block here (like inside a function) (or a tuple assignment: (x, y) = ...)
{

}

Maybe T :: Just(t) | Nothing deriving Clone

AStruct :: (
    x i32
)

SomeEnum :: {
    Variant { x i32, y *i8 }
    OtherVariant
    ThirdVariant
}

fn main {
    [1, 2, 3].map(|x| 2*x)
    [1, 2, 3].map(2*_) # scala-like closure shorthands
}