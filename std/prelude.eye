# All items defined here are included in all modules by default. They can be
# shadowed by other definitions so adding new items here won't break anything.
use root.primitive.bool
use root.primitive.usize
use root.primitive.isize

true :: bool.true
false :: bool.false

use root.primitive.Never

use root.print
use root.println
use root.input
use root.panic
use root.Eq

use root.option.Option
use root.result.Result

use root.string.str
use root.string.ToString

use root.list.List

use root.int.abs

use root.iter.Iterator
use root.iter.filter
use root.iter.map
use root.iter.zip
use root.iter.range
use root.iter.collect
use root.iter.sum
use root.iter.for_each
