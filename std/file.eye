
read_to_string(path *i8) -> *i8 {
    chunk_size := 64
    buf := root.std.buf(chunk_size)
    str := root.std.c.malloc(chunk_size+1) # reserve one byte for zero terminator

    handle := root.std.c.fopen(path, "r")
    if handle.ptr == 0 {
        root.std.println("Failed to open file")
    }

    finished := false
    while !finished {
        read_count := root.std.c.fread(str, 1, chunk_size, handle)
        buf = root.std.buf_write(buf, str, read_count)
        
        if read_count != chunk_size: finished = true
    }
    buf = root.std.buf_write(buf, "\0", 1)
    ret buf.ptr
}