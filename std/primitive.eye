# this is currently the plan for defining all primitives inside the language
# for now multiple aspects don't work like this. Until then, primitives will remain defined and 
# special-cased in the compiler

# things that are required for this:
# - [x] attributes
#   - [ ] packed attribute
#   - [ ] align attribute
# - [x] inherent trait impl syntax
# - [ ] Operator overloading via traits like Add

bool :: enum {
    false
    true

    toggle :: fn(self *bool) {
        self^ = !self^
    }
}

#- 
u8 :: @packed struct {
    bit0 bool
    bit1 bool
    bit2 bool
    bit3 bool
    bit4 bool
    bit5 bool
    bit6 bool
    bit7 bool

    impl Add[Self] {
        fn add(l Self, r Self) -> Self: root.intrinsics.add(l, r)
    }
}

u16 :: @align(2) struct {
    byte0 u8
    byte1 u8
}
-#
