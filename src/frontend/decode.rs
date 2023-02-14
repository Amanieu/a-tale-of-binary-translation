/// Helper type to decode the various bitfields in RISC-V instruction
/// encodings.
#[derive(Clone, Copy)]
pub struct InstrBitfields(pub u32);

/// Internal helper function to sign-extend a bitfield.
fn sign_extend(val: u32, bits: u32) -> u32 {
    let shift = 32 - bits;
    let tmp = val << shift;
    (tmp as i32 >> shift) as u32
}

impl InstrBitfields {
    /// Internal helper function to extract a sequence of bits.
    fn extract_bitfield(self, lsb: u32, width: u32) -> u32 {
        (self.0 >> lsb) & (!0 >> (32 - width))
    }

    /// `opcode` field for all instruction types.
    pub fn opcode(self) -> u32 {
        self.extract_bitfield(0, 7)
    }

    /// `rd` field for R/I/U/J instruction types.
    pub fn rd(self) -> u32 {
        self.extract_bitfield(7, 5)
    }

    /// `funct3` field for R/I/S/B instruction types.
    pub fn funct3(self) -> u32 {
        self.extract_bitfield(12, 3)
    }

    /// `rs1` field for R/I/S/B instruction types.
    pub fn rs1(self) -> u32 {
        self.extract_bitfield(15, 5)
    }

    /// `rs2` field for R/S/B instruction types.
    pub fn rs2(self) -> u32 {
        self.extract_bitfield(20, 5)
    }

    /// `funct7` field for R instruction types.
    pub fn funct7(self) -> u32 {
        self.extract_bitfield(25, 7)
    }

    /// Sign-extended immediate for I instruction types.
    pub fn imm_i(self) -> u32 {
        let bits = self.extract_bitfield(20, 12);
        sign_extend(bits, 12)
    }

    /// Sign-extended immediate for S instruction types.
    pub fn imm_s(self) -> u32 {
        let low = self.extract_bitfield(7, 5);
        let high = self.extract_bitfield(25, 7);
        let combined = high << 5 | low;
        sign_extend(combined, 12)
    }

    /// Sign-extended immediate for B instruction types.
    pub fn imm_b(self) -> u32 {
        let bit11 = self.extract_bitfield(7, 1);
        let low = self.extract_bitfield(8, 4);
        let bit12 = self.extract_bitfield(31, 1);
        let high = self.extract_bitfield(25, 6);
        let combined = bit12 << 12 | bit11 << 11 | high << 5 | low << 1;
        sign_extend(combined, 12)
    }

    /// Sign-extended immediate for U instruction types.
    pub fn imm_u(self) -> u32 {
        let bits = self.extract_bitfield(12, 20);
        bits << 12
    }

    /// Sign-extended immediate for J instruction types.
    pub fn imm_j(self) -> u32 {
        let high = self.extract_bitfield(12, 8);
        let bit11 = self.extract_bitfield(20, 1);
        let low = self.extract_bitfield(21, 10);
        let bit20 = self.extract_bitfield(31, 1);
        let combined = bit20 << 20 | high << 12 | bit11 << 11 | low << 1;
        sign_extend(combined, 20)
    }
}
