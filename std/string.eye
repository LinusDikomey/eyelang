use root.list.List
use root.ptr_add
use root.c.malloc
use root.c.memcpy
use root.c.printf
use root.c.exit
use root.panic

# represents a string slice
str :: struct {
    ptr *i8
    len u64

    from_cstr :: fn(ptr *i8) -> str: str(ptr, len(ptr))
    
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

    slice :: fn(this str, start u64, end u64) -> str {
        if end > this.len {
            printf("[PANIC]: string slice out of range: %d..%d > %d\n".ptr, start, end, this.len)
            exit(1)
        }
        if start > end: start = end
        ret str(ptr_add(this.ptr, start), end - start)
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
        ret Split(this, pat)
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
}

NEWLINE: i8 : 10
CARRIAGE_RETURN: i8 : 13

len :: fn(s *i8) -> u64: root.c.strlen(s) as _

use root.parse_int

Split :: struct {
    string str
    pat str

    # Returns the next match and true or an empty string and false otherwise.
    # This will become an Option when sum types are ready.
    next :: fn(this *Split) -> (bool, str) {
        if this.string.len == 0: ret (false, "")
        i := 0
        matched := 0
        while i < this.string.len {
            if this.string.byte(i) == this.pat.byte(matched) {
                matched += 1
                if matched == this.pat.len {
                    s := this.string.slice(0, i+1-matched)
                    this.string = this.string.slice(i+1, this.string.len)
                    ret (true, s)
                }
            } else matched = 0
            i += 1
        }

        s := this.string
        this.string = this.string.slice(this.string.len, this.string.len)
        ret (true, s)
    }
}

# TODO: unicode whitespace definition (when chars are handled properly)
is_whitespace :: fn(c u8) -> bool: match c {
    9..13: true, # \t, \n, \v, \f, \r
    32: true, # whitespace
    _: false,
}
