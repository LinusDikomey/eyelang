#include <stddef.h>

void* ptr_add(void* p, size_t offset) {
    return p + offset;
}
void* ptr_sub(void* p, size_t offset) {
    return p - offset;
}

size_t ptr_to_int(void* p) {
    return (size_t) p;
}

void* int_to_ptr(size_t i) {
    return (void*) i;
}