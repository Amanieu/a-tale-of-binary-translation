use std::fmt::Debug;

mod decode;
mod translate;

pub use translate::translate_one_instruction;

/// Enum to represent a comparison condition between two values.
///
/// `Le` and `Gt` comparisons can be synthesized by inverting the operands.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cond {
    Eq,
    Ne,
    Ge(Signed),
    Lt(Signed),
}

/// Enum to represent a memory access width.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Width {
    Byte,
    Half,
    Word,
}

impl Width {
    /// Number of bytes in this memory access.
    pub fn bytes(self) -> usize {
        match self {
            Width::Byte => 1,
            Width::Half => 2,
            Width::Word => 4,
        }
    }
}

/// Enum to represent whether an operation should treat operands/results as
/// signed or unsigned.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Signed {
    Unsigned,
    Signed,
}

/// This trait represents the interface between the translation front-end and
/// the various back-ends.
///
/// The front-end decodes RISC-V instructions into micro-ops which are
/// represented as function in this trait.
///
/// This trait makes a distinction between compile-time and runtime values.
/// Compile-time values are represented as plain integers while runtime values
/// are represented using the abstract `Value` type..
///
/// In an interpreter back-end, `Value` is just a plain `u32`, but for a
/// compiler back-end this is a reference to a temporary value in the compiled
/// code.
pub trait Trans {
    /// Abtract value type representing a 32-bit integer value at runtime.
    type Value: Debug + Copy;

    /// Returns the value of the given register.
    ///
    /// `index` must be between 0 and 32. Register 0 always returns a value of
    /// 0.
    fn get_reg(&mut self, index: u32) -> Self::Value;

    /// Sets the value of the given register.
    ///
    /// `index` must be between 0 and 32. Writes to register 0 are ignored.
    fn set_reg(&mut self, index: u32, val: Self::Value);

    /// Returns the value of the program counter.
    ///
    /// This is directly returned as a `u32` because it is a compile-time
    /// constant.
    fn get_pc(&mut self) -> u32;

    /// Sets the value that the program counter should be set to after the
    /// current instruction finishes executing.
    ///
    /// This may later be overridden by a `jump` operation.
    fn set_next_pc(&mut self, pc: u32);

    /// Reads a 32-bit word from a given memory address.
    ///
    /// This is a compile-time operation, intended to be used for reading
    /// instructions.
    fn fetch_u32(&mut self, address: u32) -> u32;

    /// Returns a `Value` which will hold the given value at runtime.
    fn const_value(&mut self, val: u32) -> Self::Value;

    /// Reads a value from memory at runtime from `address`.
    ///
    /// If `width` is smaller than a word, then the value is sign/zero-extended
    /// depending on `signed`.
    fn load(&mut self, width: Width, signed: Signed, address: Self::Value) -> Self::Value;

    /// Stores a value to `address` in memory at runtime.
    fn store(&mut self, width: Width, address: Self::Value, val: Self::Value);

    /// Adds 2 values at runtime.
    ///
    /// Wraps on overflow.
    fn add(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;

    /// Subtracts 2 values at runtime.
    ///
    /// Wraps on overflow.
    fn sub(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;

    /// And 2 values at runtime.
    fn and(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;

    /// Or 2 values at runtime.
    fn or(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;

    /// Xor 2 values at runtime.
    fn xor(&mut self, a: Self::Value, b: Self::Value) -> Self::Value;

    /// Shifts a value left at runtime.
    ///
    /// Only the low 5 bits of the shift value are used.
    fn shift_left(&mut self, val: Self::Value, shift: Self::Value) -> Self::Value;

    /// Shifts a value right at runtime.
    ///
    /// A signed or unsigned shift is used depending on `signed`.
    ///
    /// Only the low 5 bits of the shift value are used.
    fn shift_right(&mut self, signed: Signed, val: Self::Value, shift: Self::Value) -> Self::Value;

    /// This is a terminator operation: no other method on `Trans` should be
    /// called after this one for the current instruction.
    fn jump(&mut self, target: Self::Value);

    /// This is a terminator operation: no other method on `Trans` should be
    /// called after this one for the current instruction.
    fn ecall(&mut self);

    /// This is a terminator operation: no other method on `Trans` should be
    /// called after this one for the current instruction.
    fn ebreak(&mut self);

    /// This is a terminator operation: no other method on `Trans` should be
    /// called after this one for the current instruction.
    fn undefined_encoding(&mut self, instr: u32);

    /// Compares 2 values at runtime, and then executes one of the closures
    /// depending on the comparison result.
    ///
    /// In an interpreter, only one of the closures is executed, but both will
    /// be executed in a compiler to generate the code for both branches.
    ///
    /// Any `Value`s created in the branches cannot be used outside their
    /// closure. Instead, they should be returned by the closure and `if_val`
    /// will return a `Value` containing the result of the branch that was taken
    /// at runtime.
    fn if_val(
        &mut self,
        cond: Cond,
        a: Self::Value,
        b: Self::Value,
        if_true: impl FnOnce(&mut Self) -> Self::Value,
        if_false: impl FnOnce(&mut Self) -> Self::Value,
    ) -> Self::Value;

    /// Simpler variant of `if_val` that doesn't return a value.
    fn if_(
        &mut self,
        cond: Cond,
        a: Self::Value,
        b: Self::Value,
        if_true: impl FnOnce(&mut Self),
        if_false: impl FnOnce(&mut Self),
    ) {
        let dummy = self.const_value(0);
        self.if_val(
            cond,
            a,
            b,
            |trans| {
                if_true(trans);
                dummy
            },
            |trans| {
                if_false(trans);
                dummy
            },
        );
    }
}
