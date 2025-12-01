
main :: fn {
  l: List[_] = collect(filter(map(range(1, 10), fn(x): 2 * x), fn(x): x^ != 10))
  for i in l.iter() {
    println(i)
  }
}
