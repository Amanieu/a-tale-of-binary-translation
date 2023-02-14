# A tale of binary translation

This repo contains the code for the RISC-V emulator that I presented at [Rust Nation 2023](https://www.rustnationuk.com/).

It is intended as a teaching example to introduce people to the principles behind binary translation, and not a proper production-ready emulator. However, pull requests are still welcome!

## Building the examples

A `build.sh` script is provided in the `examples` directory to build the assembly code examples used in the presentation. This requires `clang` and `llvm-objcopy` to be installed. Pass the name of the assembly file to the script to build it.

The resulting `.bin` file can be passed as an argument to the emulator:

```sh
examples/build.sh examples/hello_word.s
cargo run -- -b interpreter examples/hello_world.bin
```

## System calls

The behavior of the `ecall` and `ebreak` instructions is defined in `syscall.rs`. Currently, `ebreak` will stop the emulator and exit the process. `ecall` invokes a system call depending on the value of `x17`:

| System call number (x17) | Name        | Description                                            | Arguments                               | Return value        |
|--------------------------|-------------|--------------------------------------------------------|-----------------------------------------|---------------------|
| 0                        | `print`     | Prints a string                                        | x10: string address  x11: string length |                     |
| 1                        | `print_int` | Prints an integer                                      | x10: integer to print                   |                     |
| 2                        | `get_arg`   | Returns the Nth argument as an integer, or 0 if absent | x10: argument index                     | x10: argument value |

You can easily define additional system calls by extending `syscall.rs`.

## License

Licensed under either of:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or https://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or https://opensource.org/licenses/MIT)

at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
