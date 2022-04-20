
puts(s *i8) -> i32 extern
printf(fmt *i8, ...) -> i32 extern
snprintf(buffer *i8, max_len u64, fmt *i8, ...) -> i32 extern
scanf(fmt *i8, ...) -> i32 extern
strcmp(str1 *i8, str2 *i8) -> i32 extern
strlen(str *i8) -> i32 extern

malloc(size u64) -> *i8 extern
free(ptr *i8) -> extern
memcpy(dest *i8, src *i8, n u64) -> extern

atoi(s *i8) -> i32 extern


FileHandle :: { ptr u64 }

INVALID_FILE -> FileHandle: FileHandle(0)

fopen(path *i8, mode *i8) -> FileHandle extern
fclose(handle FileHandle) -> i32 extern
fread(ptr *i8, size u64, count u64, stream FileHandle ) -> u64 extern

sleep(seconds u32) -> extern

ptr_add(ptr *i8, offset u64) -> *i8 extern
ptr_sub(ptr *i8, offset u64) -> *i8 extern