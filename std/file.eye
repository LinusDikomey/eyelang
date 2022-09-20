
read_to_string :: fn(path *i8) -> *i8 {
    chunk_size := 64
    buf := root.buf(chunk_size)
    str := root.c.malloc(chunk_size+1) # reserve one byte for zero terminator

    handle := root.c.fopen(path, "r")
    if handle.ptr == 0 {
        root.println("Failed to open file")
    }

    finished := false
    while !finished {
        read_count := root.c.fread(str, 1, chunk_size, handle)
        buf = root.buf_write(buf, str, read_count)
        
        if read_count != chunk_size: finished = true
    }
    buf = root.buf_write(buf, "\0", 1)
    ret buf.ptr
}