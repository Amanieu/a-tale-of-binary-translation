use std::{process, str};

use crate::EmulatorState;

/// Handler function for the `ECALL` instruction.
pub(crate) extern "C" fn ecall_handler(state: &mut EmulatorState) {
    // Register a7 (x17) holds the system call number.
    match state.regs[17] {
        // Print string in x10 with length in x11.
        0 => {
            let start = state.regs[10];
            let end = start
                .checked_add(state.regs[11])
                .expect("string length overflow");
            let bytes = &state.mem[start as usize..end as usize];
            let string = str::from_utf8(bytes).expect("string is not utf-8");
            print!("{string}");
        }

        // Print integer in x10.
        1 => {
            let val = state.regs[10];
            println!("{val}");
        }

        // Get integer command-line argument at index x10. Value returned in
        // x10.
        //
        // Returns 0 if there is no argument at this index.
        2 => {
            let index = state.regs[10] as usize;
            state.regs[10] = *state.args.args.get(index).unwrap_or(&0);
        }

        _ => panic!("Unknown syscall {}", state.regs[17]),
    }

    // Increment the PC to resume execution after the ECALL instruction.
    state.pc = state.pc.wrapping_add(4);
}

/// Handler function for the `EBREAK` instruction.
///
/// Currently this is just used to end the emulation.
pub(crate) extern "C" fn ebreak_handler(state: &mut EmulatorState) {
    // Explicitly flush the cache before exiting so that temporary directories
    // are cleaned up.
    unsafe {
        state.jit_cache.flush();
    }
    process::exit(0)
}

/// Handler function for undefined encodings.
///
/// Currently this just panics.
pub(crate) extern "C" fn undefined_encoding_handler(state: &mut EmulatorState, instr: u32) {
    // Explicitly flush the cache before exiting so that temporary directories
    // are cleaned up.
    unsafe {
        state.jit_cache.flush();
    }
    panic!(
        "Undefined instruction encoding at {:#x}: {instr:8x}",
        state.pc
    );
}
