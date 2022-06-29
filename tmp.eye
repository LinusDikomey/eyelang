#NOCHECKIN


main :: fn {
    asm("push 0x21") # put '!' on the stack
    asm("mov rax, 1") # call number
    asm("mov rdi, 1") # fd
    asm("mov rsi, rsp") # print what is on the stack
    asm("mov rdx, 4") # length
    asm("syscall")
}