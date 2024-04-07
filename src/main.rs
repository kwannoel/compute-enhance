use std::fmt;
use anyhow::{bail, Result};

#[derive(Clone, Debug)]
pub enum Reg {
    // W = 0
    AL,
    CL,
    DL,
    BL,
    AH,
    CH,
    DH,
    BH,

    // W = 1
    AX,
    CX,
    DX,
    BX,
    SP,
    BP,
    SI,
    DI,
}

#[derive(Clone, Debug)]
pub enum Mode {
    MemDisplacement0,
    MemDisplacement8,
    MemDisplacement16,
    RegDisplacement0,
}

#[derive(Clone, Debug)]
pub enum Instruction {
    Mov { w: bool, d: bool, mode: Mode, reg: Reg, rw: Reg }
}

#[derive(Clone, Debug)]
pub enum InstructionName {
    Mov
}

impl From<&Instruction> for InstructionName {
    fn from(inst: &Instruction) -> Self {
        match inst {
            Instruction::Mov {..} => InstructionName::Mov
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op: InstructionName = self.into();
        let (src, dest) = match self {
            Instruction::Mov { reg, rw, d, .. } => {
               match d {
                   // reg is src
                   false => (reg, rw),
                   // reg is dest
                   true => (rw, reg)
               }
            }
        };
        let op_str = format!("{:?}", op).to_lowercase();
        let src_str = format!("{:?}", src).to_lowercase();
        let dest_str = format!("{:?}", dest).to_lowercase();
        write!(f, "{op_str} {dest_str}, {src_str}")
    }
}

/// Check if all bits in mask are set to 1.
fn check_bitset(bits: u8, mask: u8) -> bool {
    bits & mask == mask
}

fn decode_reg(bits: u8, w: bool) -> Result<Reg> {
    use crate::Reg::*;
    match (bits, w) {
        // W = 0
        (0b0000_0000, false) => Ok(AL),
        (0b0000_0001, false) => Ok(CL),
        (0b0000_0010, false) => Ok(DL),
        (0b0000_0011, false) => Ok(BL),
        (0b0000_0100, false) => Ok(AH),
        (0b0000_0101, false) => Ok(CH),
        (0b0000_0110, false) => Ok(DH),
        (0b0000_0111, false) => Ok(BH),
        // W = 1
        (0b0000_0000, true) => Ok(AX),
        (0b0000_0001, true) => Ok(CX),
        (0b0000_0010, true) => Ok(DX),
        (0b0000_0011, true) => Ok(BX),
        (0b0000_0100, true) => Ok(SP),
        (0b0000_0101, true) => Ok(BP),
        (0b0000_0110, true) => Ok(SI),
        (0b0000_0111, true) => Ok(DI),
        _ => {
            bail!("invalid reg encoding: {bits:b}")
        }
    }
}

fn decode_instruction(buf: &[u8]) -> Result<Instruction> {
    debug_assert_eq!(buf.len(), 2);
    const OPCODE_MASK: u8 = 0b1111_1100;
    const D_MASK: u8 = 0b0000_0010;
    const W_MASK: u8 = 0b0000_0001;
    const MOD_MASK: u8 = 0b1100_0000;
    const REG_MASK: u8 = 0b0011_1000;
    const RW_MASK: u8 = 0b0000_0111;
    let b1 = buf[0];
    let b2 = buf[1];
    let instruction = match b1 & OPCODE_MASK {
        0b1000_1000 => {
            let d = check_bitset(b1, D_MASK);
            let w = check_bitset(b1, W_MASK);
            let mode = match b2 & MOD_MASK {
                0b0000_0000 => Mode::MemDisplacement0,
                0b0100_0000 => Mode::MemDisplacement8,
                0b1000_0000 => Mode::MemDisplacement16,
                0b1100_0000 => Mode::RegDisplacement0,
                e => {
                    bail!("invalid mode encoding: {e:b}")
                }
            };
            let reg = decode_reg((b2 & REG_MASK) >> 3, w)?;
            let rw = decode_reg(b2 & RW_MASK, w)?;
            Ok(Instruction::Mov {
                w,
                d,
                mode,
                reg,
                rw,
            })
        }
        unsupported_opcode => bail!("invalid opcode encoding: {unsupported_opcode:b}")
        // Mov
    };
    instruction
}

fn decode_instructions(buf: &[u8]) -> Result<Vec<Instruction>> {
    let n_instructions = buf.len() / 2;
    let mut instructions = Vec::with_capacity(n_instructions);
    for i in 0..n_instructions {
        let inst_buf = &buf[i..i+2];
        let instruction = decode_instruction(inst_buf)?;
        instructions.push(instruction);
    }
    Ok(instructions)
}

fn main() {
    // Decode file
}

#[cfg(test)]
mod tests {
    use super::*;
    use expect_test::{expect, Expect};
    use std::fmt::Debug;

    fn check_debug(actual: impl Debug, expect: Expect) {
        expect.assert_eq(&format!("{:#?}", actual));
    }

    #[test]
    fn test_37_decode() {
        let listing37 = [0b1000_1001, 0b1101_1001];
        let instructions = decode_instructions(&listing37).unwrap();
        check_debug(&instructions, expect![[r#"
            [
                Mov {
                    w: true,
                    d: false,
                    mode: RegDisplacement0,
                    reg: BX,
                    rw: CX,
                },
            ]"#]]);
        assert_eq!(
            instructions.iter().map(|i| i.to_string()).collect::<Vec<_>>().join("\n"),
            "mov cx, bx"
        )
    }
}
