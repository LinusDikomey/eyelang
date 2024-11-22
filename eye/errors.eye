main :: fn: print("Hello")

# invalid integer types
InvalidTypes :: struct {
    valid u32,
    invalid u33,
    also_invalid u34,
    multiline_invalid
    u35,
}
# invalid character in the middle of the file
µ

# a bunch of invalid characters
µ∆ºª©ƒ

# invalid character group with just spaces and newlines

µ∑®⁄¨Ω   µ∆
   º∂∑∑€®
ƒª©ƒ∂∂€®øπå√∫

test :: fn(x u32, y u33, z u34, valid InvalidTypes) {
    print("Test Function"); # oh no, a semicolon
}

#- an invalid character at the end of the file -# ;
