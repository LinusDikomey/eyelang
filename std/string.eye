use root.list.List
use root.ptr_add
use root.c.malloc
use root.c.memcpy

NEWLINE: i8 : 10
CARRIAGE_RETURN: i8 : 13

len :: fn(s *i8) -> u64: root.c.strlen(s) as _

use root.parse_int

lines :: fn(s *i8) -> List[*i8] {
    substring :: fn(s *i8, start u64, end u64) -> *i8 {
        substr := malloc(end - start + 1)
        ptr_add(substr, end - start)^ = 0
        memcpy(substr, ptr_add(s, start), end - start)

        ret substr
    }

    list := List.new()

    start := 0
    cur := 0

    while (true) {
        match ptr_add(s, cur)^ {
            0 {
                list.push(substring(s, start, cur))
                ret list
            }
            10 {
                list.push(substring(s, start, cur))
                cur += 1
                if ptr_add(s, cur)^ == 13: cur += 1
                start = cur
            }
            _ {
                cur += 1
            }
        }
    }


    ret list
}