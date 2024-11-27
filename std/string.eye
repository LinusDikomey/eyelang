use root.list.List
use root.ptr_add
use root.c.malloc
use root.c.memcpy
use root.c.printf
use root.c.exit
use root.panic
use root.int.Int

# represents a string slice
str :: struct {
    ptr *i8
    len u64

    from_cstr :: fn(ptr *i8) -> str: str(ptr: ptr, len: len(ptr))

    is_empty :: fn(this str) -> bool: this.len == 0

    eq :: fn(this str, other str) -> bool {
        if this.len != other.len: ret false
        i := 0
        while i < this.len {
            if this.byte(i) != other.byte(i): ret false
            i += 1
        }
        ret true
    }

    clone :: fn(this str) -> str {
        new_ptr := malloc(this.len)
        memcpy(new_ptr, this.ptr, this.len)
        ret str(ptr: new_ptr, len: this.len)
    }

    slice :: fn(this str, start u64, end u64) -> str {
        if end > this.len {
            printf("[PANIC]: string slice out of range: %d..%d > %d\n".ptr, start, end, this.len)
            exit(1)
        }
        if start > end: start = end
        ret str(ptr: ptr_add(this.ptr, start), len: end - start)
    }

    byte :: fn(this str, index u64) -> u8 {
        if index >= this.len {
            printf("[PANIC]: str byte index out of range: %d >= %d".ptr, index, this.len)
            exit(1)
        }
        ret ptr_add(this.ptr, index)^ as u8
    }

    split :: fn(this str, pat str) -> Split {
        if pat.len == 0: panic("empty pattern supplied to split")
        ret Split(string: this, pat: pat)
    }

    lines :: fn(this str) -> List[str] {
        list := List.new()

        start := 0
        cur := 0

        while (true) {
            if cur == this.len {
                list.push(this.slice(start, cur))
                ret list
            }
            match this.byte(cur) {
                10 {
                    list.push(this.slice(start, cur))
                    cur += 1
                    if cur < this.len: if this.byte(cur) == 13: cur += 1
                    start = cur
                }
                _ {
                    cur += 1
                }
            }
        }
        ret list
    }

    parse :: fn(this str) -> i64 {
        ASCII_ZERO: u8 : 48
        ASCII_NINE: u8 : ASCII_ZERO + 9
        ASCII_MINUS: u8 : 45

        negate := false
        x := 0
        i := 0
        while i < this.len {
            b := this.byte(i)
            if b == ASCII_MINUS and x == 0: negate = !negate
            else if b >= ASCII_ZERO and b <= ASCII_NINE {
                x *= 10
                x += (b - ASCII_ZERO) as _
            }
            i += 1
        }
        ret if negate: -x else x
    }

    trim :: fn(this str) -> str {
        start := 0
        b := true
        while start < this.len and b {
            if is_whitespace(this.byte(start)):
                start += 1
            else b = false
        }

        end := this.len
        b = true
        while end > 0 and b {
            if is_whitespace(this.byte(end - 1)):
                end -= 1
            else b = false
        }
        ret this.slice(start, end)
    }

    make_ascii_lowercase :: fn(this *str) {
        i := 0
        while i < this.len {
            char_ptr := ptr_add(this.ptr, i)
            if char_ptr^ >= "A".ptr^ and char_ptr^ <= "Z".ptr^ {
                char_ptr^ += 32
            }
            i += 1
        }
    }

    make_ascii_uppercase :: fn(this str) {
        i := 0
        while i < this.len {
            char_ptr := ptr_add(this.ptr, i)
            if char_ptr^ >= "a".ptr^ and char_ptr^ <= "z".ptr^ {
                char_ptr^ -= 32
            }
            i += 1
        }
    }

    get :: fn(this str, index u64) -> Option[str] {
        if index >= this.len: ret .None
        ret .Some(str(ptr: ptr_add(this.ptr, index), len: 1))
    }
}

NEWLINE: i8 : 10
CARRIAGE_RETURN: i8 : 13
ASCII_0 :: 48
ASCII_MINUS :: 45

len :: fn(s *i8) -> u64: root.c.strlen(s) as _

use root.parse_int

Split :: struct {
    string str
    pat str

    # Returns the next match and true or an empty string and false otherwise.
    # This will become an Option when sum types are ready.
    next :: fn(this *Split) -> Option[str] {
        if this.string.len == 0: ret .None
        i := 0
        matched := 0
        while i < this.string.len {
            if this.string.byte(i) == this.pat.byte(matched) {
                matched += 1
                if matched == this.pat.len {
                    s := this.string.slice(0, i+1-matched)
                    this.string = this.string.slice(i+1, this.string.len)
                    ret .Some(s)
                }
            } else matched = 0
            i += 1
        }

        s := this.string
        this.string = this.string.slice(this.string.len, this.string.len)
        ret .Some(s)
    }
}

# TODO: unicode whitespace definition (when chars are handled properly)
is_whitespace :: fn(c u8) -> bool: match c {
    9..13: true, # \t, \n, \v, \f, \r
    32: true, # whitespace
    _: false,
}

ToString :: trait {
    to_string :: fn(this *Self) -> str
} for {
    impl _ for str {
        to_string :: fn(this *str) -> str: this.clone()
    }

    impl _ for u8 {
        to_string ::fn(this *u8) -> str: int_to_string(this^)
    }
    impl _ for u16 {
        to_string ::fn(this *u16) -> str: int_to_string(this^)
    }
    impl _ for u32 {
        to_string ::fn(this *u32) -> str: int_to_string(this^)
    }
    impl _ for u64 {
        to_string ::fn(this *u64) -> str: int_to_string(this^)
    }
    impl _ for i8 {
        to_string ::fn(this *i8) -> str: int_to_string(this^)
    }
    impl _ for i16 {
        to_string ::fn(this *i16) -> str: int_to_string(this^)
    }
    impl _ for i32 {
        to_string ::fn(this *i32) -> str: int_to_string(this^)
    }
    impl _ for i64 {
        to_string ::fn(this *i64) -> str: int_to_string(this^)
    }

}

int_to_string :: fn[T: Int](x T) -> str {
    # 20 digits are needed at most for a u64/i64
    MAX_LEN :: 20
    buf: [u8; 20] = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,ASCII_0]
    i := MAX_LEN - 1
    negative := false
    min_signed_int := false
    if x < Int.zero() {
        negative = true
        x = -x
        # handle min signed int
        if x < Int.zero() {
            # this is very hacky but we subtract one to get the max signed int and fix the last
            # digit later since it is never 9
            min_signed_int = true
            x = Int.sub(x, Int.one())
        }
    }
    while x >= Int.ten() {
        last_digit := Int.mod(x, Int.ten())
        buf[i] = ASCII_0 + Int.as_u8(last_digit)
        i -= 1
        x = Int.div(x, Int.ten())
    }
    if !Int.eq(x, Int.zero()) {
        buf[i] = ASCII_0 + Int.as_u8(x)
    } else if i != MAX_LEN - 1 {
        i += 1
    }
    if negative {
        i -= 1
        buf[i] = ASCII_MINUS
        if min_signed_int: buf[MAX_LEN-1] += 1
    }
    len := MAX_LEN - i
    ptr := malloc(len)
    memcpy(ptr, (&buf[i]) as *i8, len)
    ret str(ptr: ptr, len: len)
}
