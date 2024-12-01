use root.list.ListIter

range :: fn(start u64, end u64) -> Range: Range(start: start, end: end)

filter :: fn[T, I: Iterator[T]](it I, filter fn(*T) -> bool) -> Filter[T, I]: Filter(it: it, filter: filter)

map :: fn[T, U, I: Iterator[T]](it I, map fn(T) -> U) -> Map[T, U, I]: Map(it: it, map: map)

collect :: fn[T, I: Iterator[T]](it I) -> List[T] {
    l := List.new()
    while .Some(item) := Iterator.next(&it) {
        l.push(item)
    }
    ret l
}

Iterator :: trait[Item] {
    next :: fn(self *Self) -> Option[Item]
} for {
    impl _[u64] for Range {
        next :: fn(self *Range) -> Option[u64] {
            if self.start >= self.end: ret .None
            v := self.start
            self.start += 1
            ret .Some(v)
        }
    }

    impl[T] _[T] for ListIter[T] {
        next :: fn(self *ListIter[T]) -> Option[T] {
            if self.current >= self.end: ret .None
            v := self.current
            self.current = root.ptr_add(self.current, 1)
            ret .Some(v^)
        }
    }

    impl[T, I: Iterator[T]] _[T] for Filter[T, I] {
        next :: fn(self *Filter[T, I]) -> Option[T] {
            while .Some(item) := Iterator.next(&self.it) {
                if self.filter(&item) {
                    ret .Some(item)
                }
            }
            ret .None
        }
    }

    impl[T, U, I: Iterator[T]] _[U] for Map[T, U, I] {
        next :: fn(self *Map[T, U, I]) -> Option[U] {
            ret match Iterator.next(&self.it) {
                .Some(item): .Some(self.map(item)),
                .None: .None
            }
        }
    }

    impl _[str] for root.string.Split {
        next :: fn (self *root.string.Split) -> Option[str]: self.next()
    }
}

# doesn't work yet
#-
FromIterator :: trait[Item] {
    from_iter :: fn[I: Iterator[Item]](iter I) -> Self
} for {
    impl[T] _[T] for List[T] {
        from_iter :: fn[I: Iterator[Item]](iter I) -> Self {
            l := List.new()
            while .Some(item) := Iterator.next(&it) {
                l.push(item)
            }
            ret l
        }
    }
}
-#

Filter :: struct[T, I] {
    it I
    filter fn(*T) -> bool  
}



Map :: struct[T, U, I] {
    it I
    map fn(T) -> U
}

Range :: struct {
    start u64
    end u64
}

