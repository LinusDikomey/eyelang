use root.c
use root.c.FILE
use root.string.str
use root.list.List
use root.panic

File :: struct {
    handle *FILE

    open :: fn(path str, mode FileMode) -> File {
        handle := c.fopen(path.ptr, file_mode_str(mode))
        if handle as u64 == 0 {
            panic("failed to open file")
        }
        ret File(handle)
    }

    close :: fn(this File) {
        c.fclose(this.handle)
    }
}
FileMode :: enum { Read, ReadWrite, Create, CreateReadWrite, Append, AppendReadWrite }

file_mode_str :: fn(m FileMode) -> *i8: match m {
    .Read: "r",
    .ReadWrite: "r+",
    .Create: "w",
    .CreateReadWrite: "w+",
    .Append: "a",
    .AppendReadWrite: "a+",
}.ptr


read_to_string :: fn(path str) -> str {
    chunk_size := 64
    buf := List.with_capacity(chunk_size)

    file := File.open(path, FileMode.Read)

    finished := false
    while !finished {
        ptr := buf.reserve(chunk_size)
        read_count := root.c.fread(ptr, 1, chunk_size, file.handle)
        if read_count > chunk_size {
            panic("unexpected buf count encountered during file read")
        }
        buf.len += read_count

        if read_count != chunk_size: finished = true
    }
    # don't include zero byte in string slice but still add it for easier interop
    buf.push(0)
    buf.realloc_to_cap(buf.len)
    file.close()
    ret str(buf.buf, buf.len - 1)
}
