use libloading::Library;
use rustc_hash::FxHashSet;
use tempfile::TempDir;

use super::JitFunction;
use crate::{
    frontend::{translate_one_instruction, Cond, Signed, Trans, Width},
    read_bytes, Args, EmulatorState, MEM_SIZE,
};
use std::{
    fmt::{self, Write},
    fs, mem,
    process::Command,
};

/// Type responsible for holding the backing memory of compiled JIT functions.
pub(super) struct RustcJitCache {
    /// Set of currently loaded libraries. The lifetimes of the `JitFunction`s
    /// is tied to these.
    libs: Vec<Library>,

    /// Temporary directory into which the generated code and binaries are
    /// placed.
    temp_dir: Option<TempDir>,
}

impl RustcJitCache {
    pub(super) fn new(args: &Args) -> Self {
        if let Some(dir) = &args.rustc_persist_cache {
            fs::create_dir_all(dir).expect("failed to create rustc cache directory");
        }
        Self {
            libs: vec![],
            temp_dir: None,
        }
    }

    pub(super) fn compile(&mut self, pc: u32, mem: &[u8; MEM_SIZE], args: &Args) -> JitFunction {
        // Create a cache directory if needed. Note that the directory may have
        // previously been deleted by a flush().
        let cache_dir = if let Some(dir) = &args.rustc_persist_cache {
            dir
        } else {
            let temp_dir = self.temp_dir.get_or_insert_with(|| {
                TempDir::new().expect("failed to create temporary directory for rustc cache")
            });
            temp_dir.path()
        };

        // Generate the code and write it to block_{pc}.rs
        let basename = format!("block_{pc:x}");
        let rust_path = cache_dir.join(format!("{basename}.rs"));
        let code = RustcTranslator::translate(pc, mem, args);
        fs::write(&rust_path, code).unwrap();

        // Invoke rustc to compile the code to libblock_{pc}.so.
        let lib_path = cache_dir.join(libloading::library_filename(basename));
        let status = Command::new("rustc")
            .arg("--crate-type=cdylib")
            .arg("--edition=2021")
            .arg("-O")
            .arg(&rust_path)
            .arg("-Cpanic=abort")
            .arg("-o")
            .arg(&lib_path)
            .status()
            .expect("failed to run rustc");
        if !status.success() {
            panic!("rustc returned an error: {}", status);
        }

        // Load the library and extract the block_{pc} symbol.
        let lib = unsafe { Library::new(&lib_path).expect("failed to load library") };
        let symbol = format!("block_{pc:x}\0");
        let function = unsafe {
            *lib.get(symbol.as_bytes())
                .expect("symbol not found in library")
        };
        self.libs.push(lib);
        JitFunction(function)
    }

    /// Frees resources associated with previously compiled code.
    ///
    /// # Safety
    ///
    /// This function invalidates all `JitFunction`s previously returned by
    /// `compile`.
    pub(super) unsafe fn flush(&mut self) {
        self.libs.clear();
        self.temp_dir = None;
    }
}

/// Type to represent a value in the generated Rust code.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Value {
    /// A variable named `tmpN`.
    Temp(u32),

    /// A constant integer value.
    Const(u32),
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Temp(idx) => write!(f, "tmp{}", idx),
            Value::Const(val) => write!(f, "{:#x}", val),
        }
    }
}

/// Type holding the state needed to generate the Rust code.
struct RustcTranslator<'a> {
    /// The code being generated.
    code: String,

    /// The current memory state of the emulator. This is used for fetching
    /// instructions.
    mem: &'a [u8; MEM_SIZE],

    /// Command-line arguments
    args: &'a Args,

    /// Program counter value of the current instruction we are translating.
    pc: u32,

    /// Program counter value of the next instruction that we will translate.
    next_pc: u32,

    /// Whether the last operation on `Trans` was a terminator operation and a
    /// `return` has been emitted in the generated code. If this occurs inside
    /// an `if_val` then this is only true if both branches returned.
    returned: bool,

    /// Counter for generating unique `Temp`s.
    temp_counter: u32,

    /// Current values held in registers. This is only needed here to allow for
    /// propagating constants across instructions via `set_reg` and `get_reg`.
    ///
    /// A `None` indicates that the value of this register is not a constant.
    /// Register 0 always holds `Some(Value::Const(0))`.
    reg_values: [Option<Value>; 32],

    /// Set of known jump targets for which we need to emit resolvers.
    jump_targets: FxHashSet<u32>,
}

impl RustcTranslator<'_> {
    /// Translates instructions starting at at `pc` to a Rust program which
    /// mutates `EmulatorState`.
    fn translate(pc: u32, mem: &[u8; MEM_SIZE], args: &Args) -> String {
        let mut trans = RustcTranslator {
            code: String::new(),
            mem,
            args,
            pc,
            next_pc: 0,
            returned: false,
            temp_counter: 0,
            reg_values: [None; 32],
            jump_targets: FxHashSet::default(),
        };

        // Initialize register 0 with a constant 0 value.
        trans.reg_values[0] = Some(Value::Const(0));

        // Emit the common prelude and type definitions used by later code.
        trans.emit_prelude();

        // Emit the function containing the translated code.
        trans.translate_main();

        // If the block linking optimization is enabled, emit cached jump
        // targets and resolver functions.
        let mut targets: Vec<u32> = trans.jump_targets.drain().collect();
        targets.sort_unstable();
        for target in targets {
            trans.emit_jump_cache(target);
        }

        // Dump the generated code for debugging.
        if args.dump_jit_code {
            eprintln!("Translation for block at pc={pc:#x}:");
            eprintln!("================");
            eprintln!("{}", trans.code.trim());
            eprintln!("================");
        }

        trans.code
    }

    /// Generates the common code at the start of the Rust source file.
    ///
    /// This is mainly a copy of the existing type definitions for `JitFunction` and
    /// `EmulatorState`.
    fn emit_prelude(&mut self) {
        // Using no_std and a custom panic handler to reduce binary size.
        //
        // The `EmulatorState` type doesn't precisely match ours, but it is
        // enough since it is `#[repr(C)]` and the layout matches.
        write!(
            &mut self.code,
            r###"
#![no_std]
#![allow(unused_variables)]

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {{
    loop {{}}
}}

#[repr(transparent)]
#[derive(Clone, Copy)]
struct JitFunction(extern "C" fn(&mut EmulatorState) -> JitFunction);

#[repr(C)]
struct EmulatorState<'a> {{
    regs: [u32; 32],
    pc: u32,
    mem: &'a mut [u8; {MEM_SIZE}],
    ecall_handler: extern "C" fn(&mut EmulatorState<'_>),
    ebreak_handler: extern "C" fn(&mut EmulatorState<'_>),
    undefined_encoding_handler: extern "C" fn(&mut EmulatorState<'_>, u32),
    jit_cache: &'a mut (),
    lookup_or_translate: JitFunction,
    args: &'a mut (),
}}

const _: () = assert!(core::mem::size_of::<EmulatorState>() == {});
"###,
            mem::size_of::<EmulatorState>()
        )
        .unwrap();
    }

    /// Translate function holding the translated code.
    fn translate_main(&mut self) {
        // Export this function from the dynamic library.
        writeln!(&mut self.code, "#[no_mangle]").unwrap();

        // The function signature matches that of a `JitFunction`.
        writeln!(
            &mut self.code,
            "extern \"C\" fn block_{:x}(state: &mut EmulatorState<'_>) -> JitFunction {{",
            self.pc,
        )
        .unwrap();

        // Translate one instruction at a time until we reach a terminator
        // instruction.
        while !self.returned {
            translate_one_instruction(self);
            self.pc = self.next_pc;
        }

        writeln!(&mut self.code, "}}").unwrap();
    }

    /// Emits a `static` jump cache variable and a resolver function for that
    /// variable.
    ///
    /// The `static` holds the `JitFunction` to execute for a particular jump
    /// target, which avoids a `HashMap` lookup in `lookup_or_translate`.
    ///
    /// Initially this `static` points to a resolver function which will call
    /// `lookup_or_translate` with the target pc and update the jump cache
    /// `static` with the new
    fn emit_jump_cache(&mut self, target: u32) {
        writeln!(
            &mut self.code,
            r###"
static mut JUMP_CACHE_{target:X}: JitFunction = JitFunction(resolver_{target:x});

extern "C" fn resolver_{target:x}(state: &mut EmulatorState<'_>) -> JitFunction {{
    state.pc = {target:#x};
    let resolved = (state.lookup_or_translate.0)(state);
    unsafe {{
        JUMP_CACHE_{target:X} = resolved;
    }}
    resolved
}}
"###,
        )
        .unwrap();
    }

    /// Allocates a new `Value::Temp`.
    fn new_temp(&mut self) -> Value {
        let temp = self.temp_counter;
        self.temp_counter = self
            .temp_counter
            .checked_add(1)
            .expect("temp_counter overflow");
        Value::Temp(temp)
    }
}

impl Trans for RustcTranslator<'_> {
    type Value = Value;

    fn get_reg(&mut self, index: u32) -> Self::Value {
        // Re-use an existing value if one was already assigned to this register.
        if let Some(val) = self.reg_values[index as usize] {
            val
        } else {
            let tmp = self.new_temp();
            self.reg_values[index as usize] = Some(tmp);
            writeln!(self.code, "let {tmp} = state.regs[{index}];").unwrap();
            tmp
        }
    }

    fn set_reg(&mut self, index: u32, val: Self::Value) {
        if index != 0 {
            self.reg_values[index as usize] = Some(val);
            writeln!(self.code, "state.regs[{index}] = {val};").unwrap();
        }
    }

    fn get_pc(&mut self) -> u32 {
        self.pc
    }

    fn set_next_pc(&mut self, pc: u32) {
        self.next_pc = pc;
    }

    fn fetch_u32(&mut self, address: u32) -> u32 {
        u32::from_le_bytes(read_bytes(&self.mem, address))
    }

    fn const_value(&mut self, val: u32) -> Self::Value {
        Value::Const(val)
    }

    fn load(&mut self, width: Width, signed: Signed, address: Self::Value) -> Self::Value {
        let ty = match (width, signed) {
            (Width::Byte, Signed::Unsigned) => "u8",
            (Width::Byte, Signed::Signed) => "i8",
            (Width::Half, Signed::Unsigned) => "u16",
            (Width::Half, Signed::Signed) => "i16",
            (Width::Word, _) => "u32",
        };
        let width = width.bytes();
        let tmp = self.new_temp();
        writeln!(
            self.code,
            "let bytes = &state.mem[{address} as usize..{address} as usize + {width}];",
        )
        .unwrap();
        writeln!(
            self.code,
            "let {tmp} = {ty}::from_le_bytes(bytes.try_into().unwrap()) as u32;",
        )
        .unwrap();
        tmp
    }

    fn store(&mut self, width: Width, address: Self::Value, val: Self::Value) {
        let width = width.bytes();
        writeln!(
            self.code,
            "state.mem[{address} as usize..{address} as usize + {width}]\
                .copy_from_slice(&{val}.to_le_bytes()[..{width}]);"
        )
        .unwrap();
    }

    fn add(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Value::Const(a), Value::Const(b)) = (a, b) {
            return Value::Const(a.wrapping_add(b));
        }

        let tmp = self.new_temp();
        writeln!(self.code, "let {tmp} = {a}.wrapping_add({b});").unwrap();
        tmp
    }

    fn sub(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Value::Const(a), Value::Const(b)) = (a, b) {
            return Value::Const(a.wrapping_sub(b));
        }

        let tmp = self.new_temp();
        writeln!(self.code, "let {tmp} = {a}.wrapping_sub({b});").unwrap();
        tmp
    }

    fn and(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Value::Const(a), Value::Const(b)) = (a, b) {
            return Value::Const(a & b);
        }

        let tmp = self.new_temp();
        writeln!(self.code, "let {tmp} = {a} & {b};").unwrap();
        tmp
    }

    fn or(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Value::Const(a), Value::Const(b)) = (a, b) {
            return Value::Const(a | b);
        }

        let tmp = self.new_temp();
        writeln!(self.code, "let {tmp} = {a} | {b};").unwrap();
        tmp
    }

    fn xor(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        if let (Value::Const(a), Value::Const(b)) = (a, b) {
            return Value::Const(a ^ b);
        }

        let tmp = self.new_temp();
        writeln!(self.code, "let {tmp} = {a} ^ {b};").unwrap();
        tmp
    }

    fn shift_left(&mut self, val: Self::Value, shift: Self::Value) -> Self::Value {
        if let (Value::Const(val), Value::Const(shift)) = (val, shift) {
            return Value::Const(val.wrapping_shl(shift));
        }

        let tmp = self.new_temp();
        writeln!(self.code, "let {tmp} = {val}.wrapping_shl({shift});").unwrap();
        tmp
    }

    fn shift_right(&mut self, signed: Signed, val: Self::Value, shift: Self::Value) -> Self::Value {
        if let (Value::Const(val), Value::Const(shift)) = (val, shift) {
            return Value::Const(match signed {
                Signed::Unsigned => val.wrapping_shr(shift),
                Signed::Signed => (val as i32).wrapping_shr(shift) as u32,
            });
        }

        let tmp = self.new_temp();
        match signed {
            Signed::Unsigned => {
                writeln!(self.code, "let {tmp} = {val}.wrapping_shr({shift});").unwrap()
            }
            Signed::Signed => writeln!(
                self.code,
                "let {tmp} = ({val} as i32).wrapping_shr({shift}) as u32;"
            )
            .unwrap(),
        }
        tmp
    }

    fn jump(&mut self, target: Self::Value) {
        self.returned = true;

        // Block linking optimization: if the jump target is a constant then
        // use a jump cache to cache the lookup.
        if self.args.jit_block_linking {
            if let Value::Const(target) = target {
                self.jump_targets.insert(target);

                // SAFETY: This is safe because the emulator is single-threaded.
                writeln!(self.code, "return unsafe {{ JUMP_CACHE_{target:X} }};").unwrap();
                return;
            }
        }

        writeln!(self.code, "state.pc = {target};").unwrap();
        writeln!(self.code, "return state.lookup_or_translate;").unwrap();
    }

    fn ecall(&mut self) {
        writeln!(self.code, "state.pc = {};", self.pc).unwrap();
        writeln!(self.code, "(state.ecall_handler)(state);").unwrap();
        writeln!(self.code, "return state.lookup_or_translate;").unwrap();
        self.returned = true;
    }

    fn ebreak(&mut self) {
        writeln!(self.code, "state.pc = {};", self.pc).unwrap();
        writeln!(self.code, "(state.ebreak_handler)(state);").unwrap();
        writeln!(self.code, "return state.lookup_or_translate;").unwrap();
        self.returned = true;
    }

    fn undefined_encoding(&mut self, instr: u32) {
        writeln!(self.code, "state.pc = {};", self.pc).unwrap();
        writeln!(
            self.code,
            "(state.undefined_encoding_handler)(state, {instr:#x});"
        )
        .unwrap();
        writeln!(self.code, "return state.lookup_or_translate;").unwrap();
        self.returned = true;
    }

    fn if_val(
        &mut self,
        cond: Cond,
        a: Self::Value,
        b: Self::Value,
        if_true: impl FnOnce(&mut Self) -> Self::Value,
        if_false: impl FnOnce(&mut Self) -> Self::Value,
    ) -> Self::Value {
        let cond = match cond {
            Cond::Eq => format!("{a} == {b}"),
            Cond::Ne => format!("{a} != {b}"),
            Cond::Ge(Signed::Signed) => format!("{a} as i32 >= {b} as i32"),
            Cond::Lt(Signed::Signed) => format!("({a} as i32) < {b} as i32"),
            Cond::Ge(Signed::Unsigned) => format!("{a} >= {b}"),
            Cond::Lt(Signed::Unsigned) => format!("{a} < {b}"),
        };

        // Save reg_values before executing a branch: we need to restore
        // reg_values before executing the second branch, otherwise values
        // assigned to a register in one branch will spill over to the other
        // branch.
        let orig_reg_values = self.reg_values;

        // Create a new `Value::Temp` which holds the value returned by the
        // branch that is executed at runtime.
        let tmp = self.new_temp();
        writeln!(self.code, "let {tmp} = if {cond} {{").unwrap();

        // Run the closure for the true branch. If it hasn't returned, return
        // its value.
        assert!(!self.returned);
        let val_true = if_true(self);
        let true_returned = self.returned;
        if !true_returned {
            writeln!(self.code, "{val_true}").unwrap();
        }
        let reg_values_true = self.reg_values;

        writeln!(self.code, "}} else {{").unwrap();

        // Run the closure for the false branch. If it hasn't returned, return
        // its value.
        self.returned = false;
        self.reg_values = orig_reg_values;
        let val_false = if_false(self);
        let false_returned = self.returned;
        if !false_returned {
            writeln!(self.code, "{val_false}").unwrap();
        }

        // Any register values which don't match between the two branches are
        // reset to None, which means that the value is unknown and should be
        // loaded from the state.
        for i in 1..32 {
            if reg_values_true[i] != self.reg_values[i] {
                self.reg_values[i] = None;
            }
        }

        writeln!(self.code, "}};").unwrap();

        // If both branches have returned then execution cannot reach anything
        // after the if_val.
        self.returned = true_returned && false_returned;

        tmp
    }
}
