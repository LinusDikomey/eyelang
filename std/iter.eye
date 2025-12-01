use root.list.ListIter
use root.hash.MapIter
use root.int.Int
use root.call.Fn

range :: fn(start u64, end u64) -> Range: Range(start: start, end: end)

filter :: fn[T, I: Iterator[T], F: Fn[(*T), bool]](it I, filter F) -> Filter[T, I, F]: Filter(
  it: it
  filter: filter
)

map :: fn[T, U, I: Iterator[T], F: Fn[(T), U]](it I, map F) -> Map[T, U, I, F]: Map(
  it: it
  map: map
)

zip :: fn[T1, T2, I1: Iterator[T1], I2: Iterator[T2]](i1 I1, i2 I2) -> Zip[T1, T2, I1, I2]: Zip(
  i1: i1
  i2: i2
)

collect :: fn[T, I: Iterator[T]](it I) -> List[T] {
  l := List.new()
  while .Some(item) := Iterator.next(&it) {
    l.push(item)
  }
  ret l
}

sum :: fn[T: Int, I: Iterator[T]](it I) -> T {
  s := Int.zero()
  while .Some(x) := Iterator.next(&it) {
    s = Int.add(s, x)
  }
  ret s
}

for_each :: fn[T, I: Iterator[T], U](it I, f fn(T) -> U) {
  while .Some(x) := Iterator.next(&it) {
    f(x)
  }
}

Iterator :: trait[Item] {
  next :: fn(self *Self) -> Option[Item]
}

# doesn't work yet
#-
FromIterator :: trait[Item] {
    from_iter :: fn[I: Iterator[Item]](iter I) -> Self
} for {
    impl[T] _[T] for List[T] {
        from_iter :: fn[I: Iterator[T]](iter I) -> List[T] {
            l := List.new()
            while .Some(item) := Iterator.next(&iter) {
                l.push(item)
            }
            ret l
        }
    }
}
-#

Filter :: struct[T, I: Iterator[T], F: Fn[(*T), bool]] {
  it I
  filter F

  impl Iterator[T] {
    next :: fn(self *Filter[T, I, F]) -> Option[T] {
      while .Some(item) := Iterator.next(&self.it) {
        if self.filter(&item) {
          ret .Some(item)
        }
      }
      ret .None
    }
  }
}

Map :: struct[T, U, I: Iterator[T], F: Fn[(T), U]] {
  it I
  map F

  impl Iterator[U] {
    next :: fn(self *Map[T, U, I, F]) -> Option[U] {
      ret match Iterator.next(&self.it) {
        .Some(item): .Some(self.map(item)),
        .None: .None,
      }
    }
  }
}

Zip :: struct[T1, T2, I1: Iterator[T1], I2: Iterator[T2]] {
  i1 I1
  i2 I2

  impl Iterator[(T1, T2)] {
    next :: fn(self *Zip[T1, T2, I1, I2]) -> Option[(T1, T2)] {
      ret match (Iterator.next(&self.i1), Iterator.next(&self.i2)) {
        (.Some(a), .Some(b)): .Some((a, b)),
        _: .None,
      }
    }
  }
}

Range :: struct {
  start u64
  end u64

  impl Iterator[u64] {
    next :: fn(self *Range) -> Option[u64] {
      if self.start >= self.end: ret .None
      v := self.start
      self.start += 1
      ret .Some(v)
    }
  }
}
