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
#         let mut fib_n_m1 = 0;
#         let mut fib_n = 1;
#         for _ in 1..n {
#             let tmp = fib_n + fib_n_m1;
#             fib_n_m1 = fib_n;
#             fib_n = tmp;
#         }
#         fib_n
#     }
# }
fib:
    # if n < 2 { return n; }
    li x5, 2
    bltu x10, x5, return

    li x5, 0 # fib(n - 1)
    li x6, 1 # fib(n)
loop:
    # Run this loop N times.
    addi x10, x10, -1
    beqz x10, return_x6

    # fib(n + 1) = fib(n) + fib(n - 1)
    add x7, x5, x6
    mv x5, x6
    mv x6, x7
    j loop

return_x6:
    mv x10, x6

return:
    ret
