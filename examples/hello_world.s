# Syscall: print(hello, 13)
# x17: syscall number
# x10: address of string
# x11: length of string
li x17, 0
la x10, hello
li x11, 13
ecall

# End execution
ebreak

hello:
.ascii "Hello world!\n"
