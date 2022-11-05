
print :: fn(s *i8) {
    c.printf("%s", s)
}
println :: fn(s *i8) {
    c.printf("%s\n", s)
}

skip_char :: fn {
    tmp: u64 = 0
    c.scanf("%c", (&tmp) as *i8)
}

readline :: fn -> *i8 {
    line := c.malloc(1024)
    c.scanf("%1023[^\n]", line)
    skip_char()
    ret line
}

input :: fn(msg *i8) -> *i8 {
    print(msg)
    line := readline()
    ret line
}

int_to_string :: fn(i i32) -> *i8 {
    max_len := 10
    buffer := c.malloc(max_len)
    c.snprintf(buffer, max_len, "%d", i)
    ret buffer
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

buf :: fn(initial_cap u64) -> Buf: Buf(c.malloc(initial_cap), 0, initial_cap)

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

        buf = Buf(new_ptr, new_size, new_cap)
    }
    ret buf
}

panic :: fn(msg *i8) -> ! {
    c.printf("PANIC: %s\n", msg)
    c.exit(1)
}

## Adds an offset to the pointer and returns the offset pointer.
## The offset is element-wise, so the number of bytes added will be multiplied by the size of T.
ptr_add :: fn[T](ptr *T, offset u64) -> *T: (ptr as u64 + offset * T.size) as *T