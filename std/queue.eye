use root.Option
use root.ptr_add
use root.c.malloc
use root.c.memcpy

new_cap :: fn(cap u64) -> u64: if cap == 0: 4 else cap * 2

Queue :: struct[T] {
    buf *T
    len u64
    cap u64
    head u64

    new :: fn -> Queue[T]: Queue(u64(0) as *T, 0, 0, 0)

    tail :: fn(this *Queue[T]) -> u64 {
        ret (this.head + this.len) % this.cap
    }

    realloc_to_cap :: fn(this *Queue[T], new_cap u64) {
        new_buf := malloc(new_cap * T.stride) as *T
        if this.len != 0 {
            if this.head + this.len <= this.cap {
                memcpy(new_buf as *i8, ptr_add(this.buf, this.head) as *i8, this.len * T.stride)
            } else {
                first_len := this.cap - this.head
                second_len := this.len - first_len
                memcpy(new_buf as *i8, ptr_add(this.buf, this.head) as *i8, first_len * T.stride)
                memcpy(ptr_add(new_buf, first_len) as *i8, this.buf as *i8, second_len * T.stride)
            }
        }
        this.head = 0
        this.buf = new_buf
        this.cap = new_cap
    }

    first :: fn(this *Queue[T]) -> Option[*T]:
        Option.some_if(this.len != 0, ptr_add(this.buf, this.head))

    push_front :: fn(this *Queue[T], item T) {
        if this.len == this.cap {
            # we don't use realloc_to_cap here because we want to leave space
            # for the item we add to the front when copying.
            new_cap := new_cap(this.cap)
            new_buf := malloc(new_cap * T.stride) as *T
            if this.len != 0 {
                if this.head + this.len <= this.cap {
                    memcpy(ptr_add(new_buf as *i8, 1), ptr_add(this.buf, this.head) as *i8, this.len * T.stride)
                } else {
                    first_len := this.cap - this.head
                    second_len := this.len - first_len
                    memcpy(ptr_add(new_buf as *i8, 1), ptr_add(this.buf, this.head) as *i8, first_len * T.stride)
                    memcpy(ptr_add(new_buf, first_len + 1) as *i8, this.buf as *i8, second_len * T.stride)
                }
            }
            this.buf^ = item
            this.head = 0
            this.buf = new_buf
            this.cap = new_cap
        } else if this.head == 0 {
            ptr_add(this.buf, this.cap - 1)^ = item
            this.head = this.cap - 2
        } else {
            this.head -= 1
            ptr_add(this.buf, this.head)^ = item
        }
    }

    push_back :: fn(this *Queue[T], item T) {
        if this.len == this.cap {
            this.realloc_to_cap(new_cap(this.cap))
        }
        ptr_add(this.buf, this.tail())^ = item
        this.len += 1
    }

    pop_front :: fn(this *Queue[T]) -> Option[T] {
        if this.len == 0: ret .None
        item := ptr_add(this.buf, this.head)^
        this.head = (this.head + 1) % this.cap
        this.len -= 1
        ret .Some(item)
    }

    pop_back :: fn(this *Queue[T]) -> Option[T] {
        if this.len == 0: ret .None
        index := (this.head + this.len - 1) % this.cap
        item := ptr_add(this.buf, index)^
        this.len -= 1
        ret .Some(item)
    }
}
