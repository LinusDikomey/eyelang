use root.Eq
use root.intrinsics.xor
use root.intrinsics.rotate_left
use root.ptr_add

Hash :: trait {
    hash :: fn(this *Self, hasher *Hasher)
} for {
    impl _ for u8 {
        hash :: fn(this *u8, hasher *Hasher): hasher.write(this^ as u64) 
    }
    impl _ for u16 {
        hash :: fn(this *u16, hasher *Hasher): hasher.write(this^ as u64) 
    }
    impl _ for u32 {
        hash :: fn(this *u32, hasher *Hasher): hasher.write(this^ as u64) 
    }
    impl _ for u64 {
        hash :: fn(this *u64, hasher *Hasher): hasher.write(this^) 
    }
    impl _ for i8 {
        hash :: fn(this *i8, hasher *Hasher): hasher.write(this^ as u64) 
    }
    impl _ for i16 {
        hash :: fn(this *i16, hasher *Hasher): hasher.write(this^ as u64) 
    }
    impl _ for i32 {
        hash :: fn(this *i32, hasher *Hasher): hasher.write(this^ as u64) 
    }
    impl _ for i64 {
        hash :: fn(this *i64, hasher *Hasher): hasher.write(this^ as u64) 
    }

    # TODO: refactor this with variadic generics when possible    
    impl[T: Hash, U: Hash] _ for (T, U) {
        hash :: fn(this *(T, U), hasher *Hasher) {
            Hash.hash(&this^.0, hasher)
            Hash.hash(&this^.1, hasher)
        }
    }
    impl[T: Hash, U: Hash, V: Hash] _ for (T, U, V) {
        hash :: fn(this *(T, U, V), hasher *Hasher) {
            Hash.hash(&this^.0, hasher)
            Hash.hash(&this^.1, hasher)
            Hash.hash(&this^.2, hasher)
        }
    }
    impl[T: Hash, U: Hash, V: Hash, W: Hash] _ for (T, U, V, W) {
        hash :: fn(this *(T, U, V, W), hasher *Hasher) {
            Hash.hash(&this^.0, hasher)
            Hash.hash(&this^.1, hasher)
            Hash.hash(&this^.2, hasher)
            Hash.hash(&this^.3, hasher)
        }
    }
}

K: u64 : 5871781006564002453

Hasher :: struct {
    hash u64

    new :: fn -> Hasher: Hasher(hash: 0)

    write :: fn(self *Hasher, value u64) {
        self.hash = xor(rotate_left(self.hash, 5), value) * K
    } 

    finish :: fn(self *Hasher) -> u64: self.hash
}

SlotState :: enum {
    Vacant
    Occupied
    Tombstone

    is_occupied :: fn(this SlotState) -> bool: if .Occupied := this: true else false
}

Slot :: struct[K, V] {
    key K
    value V
    state SlotState
}

stride_of_ptr :: fn[T](ptr *T) -> u64: ret T.stride

FIRST_CAPACITY :: 4
new_cap :: fn(cap u64) -> u64: if cap == 0: FIRST_CAPACITY else cap * 2

Map :: struct[K: Hash + Eq, V] {

    table *Slot[K, V]
    len u64
    cap u64

    new :: fn -> Map[K, V]: Map(table: root.null(), len: 0, cap: 0)
    with_capacity :: fn(cap u64) -> Map[K, V] {
        ptr := 0 as *Slot[K, V]
        table := root.c.malloc(stride_of_ptr(ptr) * cap) as *Slot[K, V]
        i := 0
        while i < cap {
            ptr_add(table, i).state = .Vacant
            i += 1
        }
        ret Map(table: table, len: 0, cap: cap)
    }

    insert :: fn(this *Map[K, V], key K, value V) {
        if this.len == this.cap {
            new_map := Map.with_capacity(new_cap(this.cap))
            i := 0
            while i < this.len {
                entry := ptr_add(this.table, i)
                new_map.insert(entry.key, entry.value)
                i += 1
            }
            this^ = new_map
        }
        h := Hasher.new()
        Hash.hash(&key, &h)
        hash := h.finish()
        slot := hash % this.cap
        while .Occupied := ptr_add(this.table, slot).state {
            slot = (slot + 1) % this.cap
        }
        ptr_add(this.table, slot)^ = Slot(key: key, value: value, state: .Occupied)
        this.len += 1
    }

    get :: fn(this *Map[K, V], key *K) -> Option[*V] {
        if this.len == 0: ret .None
        h := Hasher.new()
        Hash.hash(key, &h)
        hash := h.finish()
        slot := hash % this.cap
        initial_slot := slot
        while true {
            entry := ptr_add(this.table, slot)
            match entry.state {
                .Vacant: ret .None,
                .Tombstone {}
                .Occupied {
                    if Eq.eq(key^, entry.key): ret .Some(&entry.value)
                }
            }
            slot = (slot + 1) % this.cap
            if slot == initial_slot {
                ret .None
            }
        }
        # unreachable but no loop {} yet
        ret .None
    }

    remove :: fn(this *Map[K, V], key *K) -> Option[V] {
        if this.len == 0: ret .None
        h := Hasher.new()
        Hash.hash(key, &h)
        hash := h.finish()
        slot := hash % this.cap
        initial_slot := slot
        while true {
            entry := ptr_add(this.table, slot)
            match entry.state {
                .Vacant: ret .None,
                .Tombstone {}
                .Occupied {
                    if Eq.eq(key^, entry.key) {
                        entry.state = .Tombstone
                        ret .Some(entry.value)
                    }
                }
            }
            slot = (slot + 1) % this.cap
            if slot == initial_slot {
                ret .None
            }
        }
        # unreachable but no loop {} yet
        ret .None
        
    }

    iter :: fn(this *Map[K, V]) -> MapIter[K, V]: MapIter(
        current: this.table
        items: this.len
    )
}

MapIter :: struct[K, V] {
    current *Slot[K, V]
    items u64

    impl Iterator[(*K, *V)] {
        next :: fn(self *MapIter[K, V]) -> Option[(*K, *V)] {        
            if self.items == 0: ret .None
            while !self.current.state.is_occupied() {
                self.current = ptr_add(self.current, 1)
            }
            self.items -= 1
            slot := self.current
            self.current = ptr_add(self.current, 1)
            ret .Some((&slot.key, &slot.value))
        }
    }
    

}
