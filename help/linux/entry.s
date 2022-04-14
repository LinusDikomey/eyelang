extern main
global _start

section .text

_start:
  mov rax, 1        ; write(
  mov rdi, 1        ;   STDOUT_FILENO,
  mov rsi, msg      ;   message
  mov rdx, msglen   ;   sizeof message
  syscall           ; );
  call main
  mov rax, 60       ; exit(
  mov rdi, 0        ;   EXIT_SUCCESS
  syscall           ; );

section .rodata
  msg: db "Eyelang entry point", 10
  msglen: equ $ - msg