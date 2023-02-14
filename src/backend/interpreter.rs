use crate::{
    frontend::{translate_one_instruction, Cond, Signed, Trans, Width},
    read_bytes, write_bytes, EmulatorState,
};

/// Interpreter main loop.
pub(crate) fn run(state: &mut EmulatorState) -> ! {
    let mut interpreter = Interpreter { state, next_pc: 0 };

    loop {
        translate_one_instruction(&mut interpreter);

        // After every instruction, advance the program counter to the next
        // instruction.
        interpreter.state.pc = interpreter.next_pc;
    }
}

/// Wrapper around the interpreter state which implements the `Trans` trait.
struct Interpreter<'a> {
    state: &'a mut EmulatorState,
    next_pc: u32,
}

impl Trans for Interpreter<'_> {
    type Value = u32;

    fn get_reg(&mut self, index: u32) -> Self::Value {
        self.state.regs[index as usize]
    }

    fn set_reg(&mut self, index: u32, val: Self::Value) {
        if index != 0 {
            self.state.regs[index as usize] = val;
        }
    }

    fn get_pc(&mut self) -> u32 {
        self.state.pc
    }

    fn set_next_pc(&mut self, pc: u32) {
        self.next_pc = pc;
    }

    fn fetch_u32(&mut self, address: u32) -> u32 {
        u32::from_le_bytes(read_bytes(&self.state.mem, address))
    }

    fn const_value(&mut self, val: u32) -> Self::Value {
        val
    }

    fn load(&mut self, width: Width, signed: Signed, address: Self::Value) -> Self::Value {
        match (width, signed) {
            (Width::Byte, Signed::Unsigned) => {
                u8::from_le_bytes(read_bytes(&self.state.mem, address)) as u32
            }
            (Width::Byte, Signed::Signed) => {
                i8::from_le_bytes(read_bytes(&self.state.mem, address)) as u32
            }
            (Width::Half, Signed::Unsigned) => {
                u16::from_le_bytes(read_bytes(&self.state.mem, address)) as u32
            }
            (Width::Half, Signed::Signed) => {
                i16::from_le_bytes(read_bytes(&self.state.mem, address)) as u32
            }
            (Width::Word, _) => u32::from_le_bytes(read_bytes(&self.state.mem, address)),
        }
    }

    fn store(&mut self, width: Width, address: Self::Value, val: Self::Value) {
        write_bytes(
            &mut self.state.mem,
            address,
            &val.to_le_bytes()[..width.bytes()],
        );
    }

    fn add(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        a.wrapping_add(b)
    }

    fn sub(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        a.wrapping_sub(b)
    }

    fn and(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        a & b
    }

    fn or(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        a | b
    }

    fn xor(&mut self, a: Self::Value, b: Self::Value) -> Self::Value {
        a ^ b
    }

    fn shift_left(&mut self, val: Self::Value, shift: Self::Value) -> Self::Value {
        val.wrapping_shl(shift)
    }

    fn shift_right(&mut self, signed: Signed, val: Self::Value, shift: Self::Value) -> Self::Value {
        match signed {
            Signed::Unsigned => val.wrapping_shr(shift),
            Signed::Signed => (val as i32).wrapping_shr(shift) as u32,
        }
    }

    fn jump(&mut self, target: Self::Value) {
        self.next_pc = target;
    }

    fn ecall(&mut self) {
        (self.state.ecall_handler)(&mut self.state);

        // ecall_handler may modify the PC, take that into account.
        self.next_pc = self.state.pc;
    }

    fn ebreak(&mut self) {
        (self.state.ebreak_handler)(&mut self.state);

        // ebreak_handler may modify the PC, take that into account.
        self.next_pc = self.state.pc;
    }

    fn undefined_encoding(&mut self, instr: u32) {
        (self.state.undefined_encoding_handler)(&mut self.state, instr);

        // undefined_encoding_handler may modify the PC, take that into account.
        self.next_pc = self.state.pc;
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
            Cond::Eq => a == b,
            Cond::Ne => a != b,
            Cond::Ge(Signed::Signed) => a as i32 >= b as i32,
            Cond::Lt(Signed::Signed) => (a as i32) < b as i32,
            Cond::Ge(Signed::Unsigned) => a >= b,
            Cond::Lt(Signed::Unsigned) => a < b,
        };
        if cond {
            if_true(self)
        } else {
            if_false(self)
        }
    }
}
