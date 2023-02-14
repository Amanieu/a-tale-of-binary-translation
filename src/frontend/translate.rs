use super::{decode::InstrBitfields, Cond, Signed, Trans, Width};

/// Translates a single RISC-V instruction, with every operation going through
/// the methods on the [`Trans`] trait. This allows a single implementation of
/// this function to be shared between the interpreter and the compiler.
///
/// For more details on RISC-V instruction encodings, refer to this excellent
/// reference card: https://github.com/jameslzhu/riscv-card
pub fn translate_one_instruction<T: Trans>(trans: &mut T) {
    // Get the address of the next instruction. We force-align this value to
    // 4 bytes, although according to the architecture we should technically be
    // raising an instruction address misaligned exception.
    let pc = trans.get_pc() & !3;

    // Read the instruction using a "compile-time" instruction fetch which
    // returns a raw `u32`.
    let instr = trans.fetch_u32(pc);

    // Set the address of the next instruction to `pc + 4`. For RV32I this is
    // trivial, but some RISC-V extensions (C) add support for variable-length
    // instructions.
    //
    // This may later be overridden by a jump operation.
    let next_pc = pc.wrapping_add(4);
    trans.set_next_pc(next_pc);

    // Now decode the instruction, starting by looking at the opcode field.
    let fields = InstrBitfields(instr);
    match fields.opcode() {
        // Register-register arithmetic & logic instructions
        0b0110011 => {
            let a = trans.get_reg(fields.rs1());
            let b = trans.get_reg(fields.rs2());
            let result = match (fields.funct3(), fields.funct7()) {
                // ADD
                (0x0, 0x00) => trans.add(a, b),
                // SUB
                (0x0, 0x20) => trans.sub(a, b),
                // XOR
                (0x4, 0x00) => trans.xor(a, b),
                // OR
                (0x6, 0x00) => trans.or(a, b),
                // AND
                (0x7, 0x00) => trans.and(a, b),
                // SLL
                (0x1, 0x00) => trans.shift_left(a, b),
                // SRL
                (0x5, 0x00) => trans.shift_right(Signed::Unsigned, a, b),
                // SRA
                (0x5, 0x20) => trans.shift_right(Signed::Signed, a, b),
                // SLT
                (0x2, 0x00) => trans.if_val(
                    Cond::Lt(Signed::Signed),
                    a,
                    b,
                    |trans| trans.const_value(1),
                    |trans| trans.const_value(0),
                ),
                // SLTU
                (0x3, 0x00) => trans.if_val(
                    Cond::Lt(Signed::Unsigned),
                    a,
                    b,
                    |trans| trans.const_value(1),
                    |trans| trans.const_value(0),
                ),
                _ => return trans.undefined_encoding(instr),
            };
            trans.set_reg(fields.rd(), result);
        }

        // Register-immediate arithmetic & logic instructions
        0b0010011 => {
            let a = trans.get_reg(fields.rs1());
            let b = trans.const_value(fields.imm_i());
            let result = match (fields.funct3(), fields.funct7()) {
                // ADDI
                (0x0, _) => trans.add(a, b),
                // XORI
                (0x4, _) => trans.xor(a, b),
                // ORI
                (0x6, _) => trans.or(a, b),
                // ANDI
                (0x7, _) => trans.and(a, b),
                // SLLI
                (0x1, 0x00) => trans.shift_left(a, b),
                // SRLI
                (0x5, 0x00) => trans.shift_right(Signed::Unsigned, a, b),
                // SRAI
                (0x5, 0x20) => trans.shift_right(Signed::Signed, a, b),
                // SLTI
                (0x2, _) => trans.if_val(
                    Cond::Lt(Signed::Signed),
                    a,
                    b,
                    |trans| trans.const_value(1),
                    |trans| trans.const_value(0),
                ),
                // SLTIU
                (0x3, _) => trans.if_val(
                    Cond::Lt(Signed::Unsigned),
                    a,
                    b,
                    |trans| trans.const_value(1),
                    |trans| trans.const_value(0),
                ),
                _ => return trans.undefined_encoding(instr),
            };
            trans.set_reg(fields.rd(), result);
        }

        // Memory load instructions
        0b0000011 => {
            let (width, signed) = match fields.funct3() {
                // LB
                0x0 => (Width::Byte, Signed::Signed),
                // LH
                0x1 => (Width::Half, Signed::Signed),
                // LW
                0x2 => (Width::Word, Signed::Signed),
                // LBU
                0x4 => (Width::Byte, Signed::Unsigned),
                // LHU
                0x5 => (Width::Half, Signed::Unsigned),
                _ => return trans.undefined_encoding(instr),
            };
            let base = trans.get_reg(fields.rs1());
            let offset = trans.const_value(fields.imm_i());
            let address = trans.add(base, offset);
            let result = trans.load(width, signed, address);
            trans.set_reg(fields.rd(), result);
        }

        // Memory store instructions
        0b0100011 => {
            let width = match fields.funct3() {
                // SB
                0x0 => Width::Byte,
                // SH
                0x1 => Width::Half,
                // SW
                0x2 => Width::Word,
                _ => return trans.undefined_encoding(instr),
            };
            let base = trans.get_reg(fields.rs1());
            let offset = trans.const_value(fields.imm_s());
            let address = trans.add(base, offset);
            let val = trans.get_reg(fields.rs2());
            trans.store(width, address, val);
        }

        // Branch instructions
        0b1100011 => {
            let cond = match fields.funct3() {
                // BEQ
                0x0 => Cond::Eq,
                // BNE
                0x1 => Cond::Ne,
                // BLT
                0x4 => Cond::Lt(Signed::Signed),
                // BGE
                0x5 => Cond::Ge(Signed::Signed),
                // BLTU
                0x6 => Cond::Lt(Signed::Unsigned),
                // BGEU
                0x7 => Cond::Ge(Signed::Unsigned),
                _ => return trans.undefined_encoding(instr),
            };
            let a = trans.get_reg(fields.rs1());
            let b = trans.get_reg(fields.rs2());
            trans.if_(
                cond,
                a,
                b,
                |trans| {
                    let target = trans.const_value(pc.wrapping_add(fields.imm_b()));
                    trans.jump(target);
                },
                |_| {},
            )
        }

        // Jump-and-link (JAL)
        0b1101111 => {
            let target = trans.const_value(pc.wrapping_add(fields.imm_j()));
            let link = trans.const_value(next_pc);
            trans.set_reg(fields.rd(), link);
            trans.jump(target);
        }

        // Jump-and-link register (JALR)
        0b1100111 => {
            if fields.funct3() != 0 {
                return trans.undefined_encoding(instr);
            }

            let a = trans.get_reg(fields.rs1());
            let b = trans.const_value(fields.imm_i());
            let target = trans.add(a, b);
            let link = trans.const_value(next_pc);
            trans.set_reg(fields.rd(), link);
            trans.jump(target);
        }

        // Load upper immediate (LUI)
        0b0110111 => {
            let val = trans.const_value(fields.imm_u());
            trans.set_reg(fields.rd(), val);
        }

        // Add upper immediate to PC (AUIPC)
        0b0010111 => {
            let val = trans.const_value(pc.wrapping_add(fields.imm_u()));
            trans.set_reg(fields.rd(), val);
        }

        // Environment call instructions (ECALL/EBREAK)
        0b1110011 => {
            // These instructions use the I format but require these fields to
            // be zero.
            if fields.funct3() != 0 || fields.rd() != 0 || fields.rs1() != 0 {
                return trans.undefined_encoding(instr);
            }

            match fields.imm_i() {
                0x0 => trans.ecall(),
                0x1 => trans.ebreak(),
                _ => return trans.undefined_encoding(instr),
            }
        }

        _ => return trans.undefined_encoding(instr),
    }
}
