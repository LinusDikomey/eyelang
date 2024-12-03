use root.Eq
use root.intrinsics.xor
use root.intrinsics.rotate_left

Hash :: trait {
    hash :: fn(this *Self, hasher *Hasher)
} for {
    impl _ for u8 {
        hash :: fn(this *u8, hasher *Hasher): hasher.write(this^ as u64) 
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

Map :: struct[K: Hash + Eq, V] {

    new :: fn -> Map[K, V]: Map()
    insert :: fn(this *Map[K, V], key K, value V) {
        h := Hasher.new()
        Hash.hash(&key, &h)
        println(h.finish())
    }
}

