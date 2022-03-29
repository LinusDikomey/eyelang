
puts(s string) -> i32 extern
printf(fmt string, ...) -> i32 extern
snprintf(buffer string, max_len u64, fmt string, ...) -> i32 extern
scanf(fmt string, ...) -> i32 extern
strcmp(str1 string, str2 string) -> i32 extern

malloc(size u64) -> string extern
free(ptr string) -> extern
memcpy(dest string, src string, n u64) -> extern

atoi(s string) -> i32 extern


FileHandle :: { ptr u64 }

INVALID_FILE -> FileHandle: FileHandle(0)

fopen(path string, mode string) -> FileHandle extern
fclose(handle FileHandle) -> i32 extern
fread(ptr string, size u64, count u64, stream FileHandle ) -> u64 extern


ptr_add(ptr string, offset u64) -> string extern
ptr_sub(ptr string, offset u64) -> string extern