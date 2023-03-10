use std::{error::Error, fs, path::PathBuf};

use backend::jit::{JitCache, JitFunction};
use clap::Parser;

mod backend;
mod frontend;
mod syscall;

/// Translation back-end to use.
#[derive(clap::ValueEnum, Clone, Copy, PartialEq, Eq)]
enum Backend {
    /// Interpreter backend
    Interpreter,

    /// JIT backend using rustc
    JitRustc,

    /// JIT backend using Cranelift
    JitCranelift,
}

/// A simple RV32I emulator.
#[derive(clap::Parser)]
struct Args {
    /// Translation back-end to use.
    #[arg(short, long, value_enum)]
    backend: Backend,

    /// Print code generated by JIT backends.
    #[arg(long)]
    dump_jit_code: bool,

    /// Enables the block linking optimization in JIT code.
    #[arg(long)]
    jit_block_linking: bool,

    /// Path to use instead instead of a temporary directory to hold the
    /// generated code for the rustc backend. This is not cleared on exit.
    #[arg(long)]
    rustc_persist_cache: Option<PathBuf>,

    /// Program to load into the emulated memory.
    program: PathBuf,

    /// Extra integer arguments to pass to the program.
    args: Vec<u32>,
}

/// Size of the memory as viewed by the emulator. We allocate 4GB plus a bit of
/// margin so that we don't need to perform any bound checks at runtime.
///
/// The 3 bvte margin allows unaligned memory accesses to succeed, although the
/// excess bytes won't wrap around. This is allowed by the architecture and
/// simplifies our implementation.
const MEM_SIZE: usize = 0x100000003;

/// State of the emulator.
///
/// This is `#[repr(C)]` because some of its fields are accessed by JIT-compiled
/// code.
#[repr(C)]
struct EmulatorState {
    /// RISC-V register values.
    ///
    /// Register 0 should always hold a value of 0, the interpreter relies on
    /// this.
    regs: [u32; 32],

    /// Current program counter.
    pc: u32,

    /// Memory of the emulated system. This uses a fixed-sized array so that it
    /// appears as a single pointer in this struct when used by JIT code.
    mem: Box<[u8; MEM_SIZE]>,

    /// Handler function for the `ecall` instruction.
    ///
    /// This handler may modify the registers and PC.
    ecall_handler: extern "C" fn(&mut EmulatorState),

    /// Handler function for the `ebreak` instruction.
    ///
    /// This handler may modify the registers and PC.
    ebreak_handler: extern "C" fn(&mut EmulatorState),

    /// Handler function for an undefined instruction encoding.
    ///
    /// This handler may modify the registers and PC.
    undefined_encoding_handler: extern "C" fn(&mut EmulatorState, u32),

    /// Cache of JIT-compiled functions.
    jit_cache: Box<JitCache>,

    /// Function called by JIT code to lookup or translate the next code block
    /// at `state.pc`.
    lookup_or_translate: JitFunction,

    /// Command-line arguments.
    args: Box<Args>,
}

/// Helper function to read bytes from the emulated memory.
fn read_bytes<const N: usize>(mem: &[u8; MEM_SIZE], address: u32) -> [u8; N] {
    let bytes = &mem[address as usize..address as usize + N];
    bytes.try_into().unwrap()
}

/// Helper function to write bytes to the emulated memory.
fn write_bytes(mem: &mut [u8; MEM_SIZE], address: u32, bytes: &[u8]) {
    mem[address as usize..address as usize + bytes.len()].copy_from_slice(bytes)
}

fn main() -> Result<(), Box<dyn Error>> {
    let args = Args::parse();

    // Read the program into the emulated memory.
    let program = fs::read(&args.program)?;
    let mut mem: Box<[u8; MEM_SIZE]> = vec![0; MEM_SIZE].into_boxed_slice().try_into().unwrap();
    write_bytes(&mut mem, 0, &program);

    let mut state = EmulatorState {
        regs: [0; 32],
        pc: 0,
        mem,
        ecall_handler: syscall::ecall_handler,
        ebreak_handler: syscall::ebreak_handler,
        undefined_encoding_handler: syscall::undefined_encoding_handler,
        jit_cache: Box::new(JitCache::new(&args)),
        lookup_or_translate: JitFunction(backend::jit::lookup_or_translate),
        args: Box::new(args),
    };

    if state.args.backend == Backend::Interpreter {
        backend::interpreter::run(&mut state);
    } else {
        backend::jit::run(&mut state);
    }
}
