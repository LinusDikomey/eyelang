
puts :: fn(s *i8) -> i32 extern
printf :: fn(fmt *i8, ...) -> i32 extern
snprintf :: fn(buffer *i8, max_len u64, fmt *i8, ...) -> i32 extern
scanf :: fn(fmt *i8, ...) -> i32 extern
strcmp :: fn(str1 *i8, str2 *i8) -> i32 extern
strlen :: fn(str *i8) -> i32 extern

malloc :: fn(size u64) -> *i8 extern
free :: fn(ptr *i8) extern
memcpy :: fn(dest *i8, src *i8, n u64) extern

atoi :: fn(s *i8) -> i32 extern


FileHandle :: struct { ptr u64 }

INVALID_FILE :: fn -> FileHandle: FileHandle(0)

fopen :: fn(path *i8, mode *i8) -> FileHandle extern
fclose :: fn(handle FileHandle) -> i32 extern
fread :: fn(ptr *i8, size u64, count u64, stream FileHandle ) -> u64 extern

sleep :: fn(seconds u32) extern

rand :: fn -> i32 extern
srand :: fn(seed u32) extern

exit :: fn(status i32) -> ! extern

# from help.c

ptr_add :: fn(ptr *i8, offset u64) -> *i8 extern
ptr_sub :: fn(ptr *i8, offset u64) -> *i8 extern

ptr_to_int :: fn(ptr *()) -> u64 extern
int_to_ptr :: fn(i u64) -> *() extern