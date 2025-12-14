use std.hash.Map

main :: fn {
  m := Map.new()
  m.insert((1, 2), "hello")
  println(m.get(&(1, 2)).or_panic()^)
  println(m.get(&(3, 4)).is_some())
  m.insert((3, 5), "world")
  println(m.get(&(3, 5)).is_some())
  println(m.get(&(1, 2)).or_panic()^)
  println(m.get(&(3, 5)).or_panic()^)
  it := range(0, 10)
  while .Some(i) := Iterator.next(&it) {
    m.insert((i, 10), "abc")
  }
  println(m.len)
  println(m.cap)
  println(m.get(&(1, 2)).or_panic()^)

  it := m.iter()
  print("len: ")
  print(m.len)
}
