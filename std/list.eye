use root.ptr_add
use root.c.printf
use root.c.malloc   
use root.c.memcpy

# FIRST_CAPACITY :: 4

List :: struct[T] {
    buf *T,
    len u64,
    cap u64,

    new :: fn() -> List[T]: List(u64(0) as *T, 0, 0)
    with_capacity :: fn(cap u64) -> List[T]: List(malloc(cap * T.size) as _, 0, cap)

    push :: fn(this *List[T], item T) {
        if this^.len < this^.cap {
            # printf("Pushing item %d { len %d cap %d } \n", item, this^.len, this^.cap)
        } else {
            new_cap := if this^.cap == 0: 4 else this^.cap * 2
            new_buf := malloc(new_cap * T.size) as *T
            if this^.len != 0 {
                memcpy(new_buf as *i8, this^.buf as *i8, this^.len * T.size)
            }
            this^.buf = new_buf
            this^.cap = new_cap
            # printf("Pushing item %d after relocating { len %d cap %d } \n", item, this^.len, this^.cap)
        }
        ptr_add(this^.buf, this^.len)^ = item
        this^.len += 1
    }

    printf_all :: fn(this *List[T], fmt *i8) {
        i := 0
        printf("[")
        while (i < this^.len) {
            if i != 0: printf(", ")
            val: T = ptr_add(this^.buf, i)^
            printf(fmt, val)

            i += 1
        }
        printf("]\n")
    }
}