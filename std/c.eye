
fn puts(s *i8) i32 extern
fn printf(fmt *i8, ...) i32 extern
fn snprintf(buffer *i8, max_len u64, fmt *i8, ...) i32 extern
fn scanf(fmt *i8, ...) i32 extern
fn strcmp(str1 *i8, str2 *i8) i32 extern
fn strlen(str *i8) i32 extern

fn malloc(size u64) *i8 extern
fn free(ptr *i8) extern
fn memcpy(dest *i8, src *i8, n u64) extern

fn atoi(s *i8) i32 extern


FileHandle :: { ptr u64 }

fn INVALID_FILE FileHandle: FileHandle(0)

fn fopen(path *i8, mode *i8) FileHandle extern
fn fclose(handle FileHandle) i32 extern
fn fread(ptr *i8, size u64, count u64, stream FileHandle ) u64 extern

fn sleep(seconds u32) extern

fn rand() i32 extern
fn srand(seed u32) extern

fn exit(status i32) ! extern

# from help.c

fn ptr_add(ptr *i8, offset u64) *i8 extern
fn ptr_sub(ptr *i8, offset u64) *i8 extern

fn ptr_to_int(ptr *()) u64 extern
fn int_to_ptr(i u64) *() extern