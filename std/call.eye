
# WARNING: this should never be implemented manually. Right now, the calling convention of closures
# is not modeled properly. The arguments tuple is spread out in the actual call. Since this is not
# known by the compiler when implementing `Fn` manually, an invalid function will be generated.
Fn :: trait[Args, Output] {
  call :: fn(this Self, args Args) -> Output
}
