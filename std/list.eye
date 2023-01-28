use root.ptr_add
use root.print
use root.println
use root.c.printf
use root.c.malloc
use root.c.memcpy

# FIRST_CAPACITY :: 4

new_cap :: fn(cap u64) -> u64: if cap == 0: 4 else cap * 2

List :: struct[T] {
    buf *T,
    len u64,
    cap u64,

    new :: fn() -> List[T]: List(u64(0) as *T, 0, 0)
    with_capacity :: fn(cap u64) -> List[T]: List(malloc(cap * T.stride) as _, 0, cap)

    push :: fn(this *List[T], item T) {
        if this^.len < this^.cap {
            # printf("Pushing item %d { len %d cap %d } \n", item, this^.len, this^.cap)
        } else {
            this.realloc_to_cap(new_cap(this^.cap))
            # printf("Pushing item %d after relocating { len %d cap %d } \n", item, this^.len, this^.cap)
        }
        ptr_add(this^.buf, this^.len)^ = item
        this^.len += 1
    }

    realloc_to_cap :: fn(this *List[T], new_cap u64) {
        new_buf := malloc(new_cap * T.stride) as *T
        if this^.len != 0 {
            memcpy(new_buf as *i8, this^.buf as *i8, this^.len * T.stride)
        }
        this^.buf = new_buf
        this^.cap = new_cap
    }

    get :: fn(this *List[T], idx u64) -> T {
        if this^.len <= idx {
            root.panic("List index out of bounds")
        }
        ret ptr_add(this^.buf, idx)^
    }

    printf_all :: fn(this *List[T], fmt *i8) {
        i := 0
        print("[")
        while (i < this^.len) {
            if i != 0: print(", ")
            val: T = ptr_add(this^.buf, i)^
            printf(fmt, val)

            i += 1
        }
        println("]")
    }

    reserve :: fn(this *List[T], n u64) -> *T {
        if this.len + n > this.cap {
            next_cap := new_cap(this.cap)
            if this.len + n > next_cap {
                next_cap = this.len + n
            }
            this.realloc_to_cap(next_cap)
        }
        ret ptr_add(this.buf, this.len)
    }
}
