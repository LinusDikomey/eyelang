use string.str
use option.Option

print :: fn[T: ToString](value T) {
    s := ToString.to_string(&value)
    c.printf("%.*s".ptr, s.len as i32, s.ptr)
    c.free(s.ptr)
}
println :: fn[T: ToString](value T) {
    s := ToString.to_string(&value)
    c.printf("%.*s\n".ptr, s.len as i32, s.ptr)
    c.free(s.ptr)
}

skip_char :: fn {
    tmp: u64 = 0
    c.scanf("%c".ptr, (&tmp) as *i8)
}

readline :: fn -> str {
    line: *i8 = c.malloc(1024)
    c.scanf("%1023[^\n]".ptr, line)
    skip_char()
    ret str.from_cstr(line)
}

input :: fn(msg str) -> str {
    print(msg)
    line := readline()
    ret line
}

int_to_str :: fn(i i32) -> str {
    max_len := 10
    buffer := c.malloc(max_len)
    c.snprintf(buffer, max_len, "%d".ptr, i)
    ret str.from_cstr(buffer)
}

parse_int :: fn(s *i8) -> i32 {
    ret c.atoi(s)
}

streq :: fn(a *i8, b *i8) -> bool {
    ret c.strcmp(a, b) == 0
}

Buf :: struct {
    ptr *i8,
    size u64,
    cap u64
}

buf :: fn(initial_cap u64) -> Buf: Buf(ptr: c.malloc(initial_cap), size: 0, cap: initial_cap)

buf_write :: fn(buf Buf, ptr *i8, len u64) -> Buf {
    if buf.cap - buf.size >= len {
        # enough capacity
        c.memcpy((buf.ptr as u64 + buf.size) as *i8, ptr as *i8, len)
        buf.size += len
    } else {
        # not enough capacity, reallocate
        new_size := buf.size + len
        new_cap := new_size
        new_ptr := c.malloc(new_size)
        c.memcpy(new_ptr, buf.ptr as *i8, buf.size)
        c.free(buf.ptr as *i8)

        c.memcpy((new_ptr as u64 + buf.size) as *i8, ptr as *i8, len)

        buf = Buf(ptr: new_ptr, size: new_size, cap: new_cap)
    }
    ret buf
}

panic :: fn(msg str) -> ! {
    c.printf("[PANIC]: %.*s\n".ptr, msg.len as i32, msg.ptr)
    c.exit(1)
}

assert :: fn(b bool, message str) {
    if !b {
        panic(message)
    }
}

## Adds an offset to the pointer and returns the offset pointer.
## The offset is element-wise, so the number of bytes added will be multiplied by the size of T.
ptr_add :: fn[T](ptr *T, offset u64) -> *T: (ptr as u64 + offset * T.size) as *T

## returns a null pointer
null :: fn[T] -> *T: 0 as u64 as *T

# TODO: should be generic over the element type and probably work on slices
sort :: fn(l *List[u64]) {
    if l.len < 2: ret
    i := 0
    while i < l.len {
        j := 0
        while j < l.len - 1 - i {
            a := l.get(j)
            b := l.get(j+1)
            if a > b {
                l.put(j+1, a)
                l.put(j, b)
            }
            j += 1
        }
        i += 1
    }
}
