use root.list.List
use root.ptr_add
use root.c.malloc
use root.c.memcpy
use root.c.printf
use root.c.exit

# represents a string slice
str :: struct {
    ptr *i8
    len u64

    from_cstr :: fn(ptr *i8) -> str: str(ptr, len(ptr))
    
    slice :: fn(this str, start u64, end u64) -> str {
        if end > this.len {
            printf("[PANIC]: string slice out of range: %d..%d > %d\n".ptr, start, end, this.len)
            exit(1)
        }
        if start > end: start = end
        str(ptr_add(this.ptr, start), end - start)
    }

    byte :: fn(this str, index u64) -> u8 {
        if index >= this.len {
            printf("[PANIC]: str byte index out of range: %d >= %d".ptr, index, this.len)
            exit(1)
        }
        ret ptr_add(this.ptr, index)^ as u8
    }

    eq :: fn(this str, other str) -> bool {
        if this.len != other.len: ret false
        i := 0
        while i < this.len {
            if this.byte(i) != other.byte(i): ret false
            i += 1
        }
        ret true
    }
}

NEWLINE: i8 : 10
CARRIAGE_RETURN: i8 : 13

len :: fn(s *i8) -> u64: root.c.strlen(s) as _

use root.parse_int

lines :: fn(s *i8) -> List[*i8] {
    substring :: fn(s *i8, start u64, end u64) -> *i8 {
        substr := malloc(end - start + 1)
        ptr_add(substr, end - start)^ = 0
        memcpy(substr, ptr_add(s, start), end - start)

        ret substr
    }

    list := List.new()

    start := 0
    cur := 0

    while (true) {
        match ptr_add(s, cur)^ {
            0 {
                list.push(substring(s, start, cur))
                ret list
            }
            10 {
                list.push(substring(s, start, cur))
                cur += 1
                if ptr_add(s, cur)^ == 13: cur += 1
                start = cur
            }
            _ {
                cur += 1
            }
        }
    }


    ret list
}