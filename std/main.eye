
fn print(s *i8) {
    c.printf("%s", s)
}
fn println(s *i8) {
    c.printf("%s\n", s)
}

fn skip_char {
    tmp: u64 = 0
    c.scanf("%c", (&tmp) as *i8)
}

fn readline *i8 {
    line := c.malloc(1024)
    c.scanf("%1023[^\n]", line)
    skip_char()
    ret line
}

fn input(msg *i8) *i8 {
    print(msg)
    line := readline()
    ret line
}

fn int_to_string(i i32) *i8 {
    max_len := 10
    buffer := c.malloc(max_len)
    c.snprintf(buffer, max_len, "%d", i)
    ret buffer
}

fn parse_int(s *i8) i32 {
    ret c.atoi(s)
}

fn streq(a *i8, b *i8) bool {
    ret c.strcmp(a, b) == 0
}

Buf :: {
    ptr *i8,
    size u64,
    cap u64
}

fn buf(initial_cap u64) Buf: Buf(c.malloc(initial_cap), 0, initial_cap)

fn buf_write(buf Buf, ptr *i8, len u64) Buf {
    if buf.cap - buf.size >= len {
        # enough capacity
        c.memcpy(c.ptr_add(buf.ptr as *i8, buf.size), ptr as *i8, len)
        buf.size += len
    } else {
        # not enough capacity, reallocate
        new_size := buf.size + len
        new_cap := new_size
        new_ptr := c.malloc(new_size)
        c.memcpy(new_ptr, buf.ptr as *i8, buf.size)
        c.free(buf.ptr as *i8)

        c.memcpy(c.ptr_add(new_ptr, buf.size), ptr as *i8, len)

        buf = Buf(new_ptr, new_size, new_cap)
    }
    ret buf
}
