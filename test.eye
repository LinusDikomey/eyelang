
main :: fn {
	x := new()
	y: i64 = Add.add(6, x)
}

new :: fn[T] -> T: panic("")

Add :: trait {
	add :: fn(self Self, other Self) -> Self
} for {
	impl i32 {
		add :: fn(self i32, other i32) -> i32: self + other
	}
	impl i64 {
		add :: fn(self i64, other i64) -> i64: self + other
	}
}

