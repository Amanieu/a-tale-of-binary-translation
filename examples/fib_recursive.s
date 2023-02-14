# Get N from command-line arguments.
# Syscall: x10 = get_arg(0)
li x17, 2
li x10, 0
ecall

# x10 = fib(x10)
call fib

# Syscall: print_int(x10)
li x17, 1
ecall

# End execution
ebreak

# fn fib(n: u32) -> u32 {
#     if n < 2 {
#         n
#     } else {
#         fib(n - 1) + fib(n - 2)
#     }
# }
fib:
    # if n < 2 { return n; }
    li t0, 2
    bgeu a0, t0, fib_recursive
    ret

fib_recursive:
    # Push caller-saved registers to the stack
    addi sp, sp, -16
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw ra, 8(sp)

    # fib(n - 1)
    mv s0, a0
    addi a0, a0, -1
    call fib
    mv s1, a0

    # fib(n - 2)
    addi a0, s0, -2
    call fib

    add a0, a0, s1

    # Pop caller-saved registers from the stack and return.
    lw s0, 0(sp)
    lw s1, 4(sp)
    lw ra, 8(sp)
    addi sp, sp, 16
    ret
