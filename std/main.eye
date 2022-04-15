
print(s string) -> {
    c.printf("%s", s)
}
println(s string) -> {
    c.printf("%s\n", s)
}

skip_char -> {
    c.scanf("%c", c.malloc(8))
}

readline -> string {
    line := c.malloc(1024)
    c.scanf("%1023[^\n]", line)
    skip_char()
    ret line
}

input(msg string) -> string {
    print(msg)
    line := readline()
    ret line
}

int_to_string(i i32) -> string {
    max_len := 10
    buffer := c.malloc(max_len)
    c.snprintf(buffer, max_len, "%d", i)
    ret buffer
}

parse_int(s string) -> i32 {
    ret c.atoi(s)
}

streq(a string, b string) -> bool {
    ret c.strcmp(a, b) == 0
}

Buf :: {
    ptr string,
    size u64,
    cap u64
}
buf(initial_cap u64) -> Buf: Buf(c.malloc(initial_cap), 0, initial_cap)

buf_write(buf Buf, ptr string, len u64) -> Buf {
    if buf.cap - buf.size >= len {
        # enough capacity
        c.memcpy(c.ptr_add(buf.ptr, buf.size), ptr, len)
        buf.size += len
    } else {
        # not enough capacity, reallocate
        new_size := buf.size + len
        new_cap := new_size
        new_ptr := c.malloc(new_size)
        c.memcpy(new_ptr, buf.ptr, buf.size)
        c.free(buf.ptr)

        c.memcpy(c.ptr_add(new_ptr, buf.size), ptr, len)

        buf = Buf(new_ptr, new_size, new_cap)
    }
    ret buf
}
