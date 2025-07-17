use root.ptr_add
use root.print
use root.println
use root.c.printf
use root.c.malloc
use root.c.memcpy

FIRST_CAPACITY :: 4
new_cap :: fn(cap u64) -> u64: if cap == 0: 4 else cap * 2

List :: struct[T] {
    buf *T
    len u64
    cap u64

    new :: fn -> List[T]: List(buf: root.null(), len: 0, cap: 0)
    with_capacity :: fn(cap u64) -> List[T]: List(buf: malloc(cap * T.stride) as _, len: 0, cap: cap)
    fill :: fn(item T, count u64) -> List[T] {
        buf := malloc(count * T.stride) as *T
        i := 0
        while i < count {
            ptr_add(buf, i)^ = item
            i += 1
        }
        ret List(buf: buf, len: count, cap: count)
    }

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
            memcpy(new_buf as *u8, this^.buf as *u8, this^.len * T.stride)
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

    put :: fn(this *List[T], idx u64, value T) {
        if this^.len <= idx {
            root.panic("List index out of bounds")
        }
        ptr_add(this^.buf, idx)^ = value
    }

    get_ptr :: fn(this *List[T], idx u64) -> *T {
        if this^.len <= idx {
            root.panic("List index out of bounds")
        }
        ret ptr_add(this^.buf, idx)
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

    iter :: fn(this *List[T]) -> ListIter[T] {
        ret ListIter(current: this.buf, end: root.ptr_add(this.buf, this.len))
    }
}

ListIter :: struct[T] {
    current *T
    end *T

    impl Iterator[T] {
        next :: fn(self *ListIter[T]) -> Option[T] {
            if self.current >= self.end: ret .None
            v := self.current
            self.current = root.ptr_add(self.current, 1)
            ret .Some(v^)
        }
    }

}

