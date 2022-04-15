extern main ; from the eyelang module
extern exit ; from libc

global _start

section .text

_start:
  call main
  
  ; mov rdi, rax ; mov result of main into the exit result
  ; mov rax, 60       ; exit(
  ; syscall           ; );

  mov rdi, 0 ; set exit code to 0
  call exit ; better than a raw syscall because it flushes io buffers

section .rodata
  msg: db "Eyelang entry point", 10
  msglen: equ $ - msg