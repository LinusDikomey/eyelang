#include <stddef.h>

void* ptr_add(void* p, size_t offset) {
    return p + offset;
}
void* ptr_sub(void* p, size_t offset) {
    return p - offset;
}
