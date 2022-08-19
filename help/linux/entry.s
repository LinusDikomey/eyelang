extern main ; from the eyelang module
extern exit ; from libc

global _start

section .note.GNU-stack
section .text

_start:
  call main
  mov rdi, rax ; mov result of main into the exit result
  call exit ; better than a raw syscall because it flushes io buffers