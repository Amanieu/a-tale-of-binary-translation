#!/bin/bash
set -ex
if [ "$#" -lt "1" ]; then
    echo "Usage: ${0} ASM_FILE"
    exit 1
fi
clang -target riscv32-elf-none -march=rv32i "${1}" -nostdlib -Wl,-Ttext=0 -o "${1%.*}.elf"
llvm-objcopy -O binary "${1%.*}.elf" "${1%.*}.bin"
