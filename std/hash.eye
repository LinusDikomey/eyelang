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
    impl[T: Hash, U: Hash] _ for (T, U) {
        hash :: fn(this *(T, U), hasher *Hasher) {
            Hash.hash(&this^.0, hasher)
            Hash.hash(&this^.1, hasher)
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
}

Slot :: struct[K, V] {
    key K
    value V
    state SlotState
}

Map :: struct[K: Hash + Eq, V] {

    table *Slot[K, V]
    len u64
    cap u64

    new :: fn -> Map[K, V]: Map(table: root.null(), len: 0, cap: 0)

    insert :: fn(this *Map[K, V], key K, value V) {
        if this.cap == 0 {
            this.table = root.c.malloc(Slot.size * 4) as _
            this.len = 0
            this.cap = 4
            i := 0
            while i < this.cap {
                ptr_add(this.table, i).state = .Vacant
                i += 1
            }
        } else if this.len == this.cap: panic("TODO: resize")
        h := Hasher.new()
        Hash.hash(&key, &h)
        hash := h.finish()
        slot := hash % this.cap
        while .Occupied := ptr_add(this.table, slot).state {
            slot = (slot + 1) % this.cap
        }
        ptr_add(this.table, slot)^ = Slot(key: key, value: value, state: .Occupied)
    }

    get :: fn(this *Map[K, V], key K) -> Option[*V] {
        h := Hasher.new()
        Hash.hash(&key, &h)
        hash := h.finish()
        slot := hash % this.cap
        while true {
            entry := ptr_add(this.table, slot)
            match entry.state {
                .Vacant: ret .None,
                .Tombstone {}
                .Occupied {
                    if Eq.eq(key, entry.key): ret .Some(&entry.value)
                }
            }
            slot = (slot + 1) % this.cap
        }
        # unreachable but no loop {} yet
        ret .None
    }
}

