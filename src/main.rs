use anyhow::{bail, Result};
use std::fmt;

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
    Mov {
        w: bool,
        d: bool,
        mode: Mode,
        reg: Reg,
        rm: Reg,
    },
}

#[derive(Clone, Debug)]
pub enum InstructionName {
    Mov,
}

impl From<&Instruction> for InstructionName {
    fn from(inst: &Instruction) -> Self {
        match inst {
            Instruction::Mov { .. } => InstructionName::Mov,
        }
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op: InstructionName = self.into();
        let (src, dest) = match self {
            Instruction::Mov { reg, rm, d, .. } => {
                match d {
                    // reg is src
                    false => (reg, rm),
                    // reg is dest
                    true => (rm, reg),
                }
            }
        };
        let op_str = format!("{:?}", op).to_lowercase();
        let src_str = format!("{:?}", src).to_lowercase();
        let dest_str = format!("{:?}", dest).to_lowercase();
        write!(f, "{op_str} {dest_str}, {src_str}")
    }
}

#[derive(Clone, Debug)]
pub struct Instructions(Vec<Instruction>);

impl fmt::Display for Instructions {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let last_idx = self.0.len() - 1;
        for inst in &self.0[..last_idx] {
            write!(f, "{inst}\n")?;
        }
        let last = &self.0[last_idx];
        write!(f, "{last}")?;
        Ok(())
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

// -------
//   MOV
// -------

type RM = Reg;
// type DispLo = u8;
// type DispHi = u8;
/// Decode 2nd byte of mov rm reg.
fn decode_mov_rm_reg_b2(d: bool, w: bool, buf: &[u8]) -> Result<(Instruction, Size)> {
    let b2 = buf[0];
    const MOD_MASK: u8 = 0b1100_0000;
    const REG_MASK: u8 = 0b0011_1000;
    const RM_MASK: u8 = 0b0000_0111;
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
    let rm = decode_reg(b2 & RM_MASK, w)?;
    Ok((
        Instruction::Mov {
            w,
            d,
            mode,
            reg,
            rm,
        },
        2,
    ))
}

type Size = usize;

fn decode_instruction(buf: &[u8]) -> Result<(Instruction, Size)> {
    debug_assert!(!buf.is_empty());

    const D_MASK: u8 = 0b0000_0010;
    const W_MASK: u8 = 0b0000_0001;

    let b1 = buf[0];
    let buf = &buf[1..];
    let instruction = match b1 {
        // MOV r/m reg
        0b10_001000 => decode_mov_rm_reg_b2(false, false, buf)?,
        0b10_001001 => decode_mov_rm_reg_b2(false, true, buf)?,
        0b10_001010 => decode_mov_rm_reg_b2(true, false, buf)?,
        0b10_001011 => decode_mov_rm_reg_b2(true, true, buf)?,
        unsupported_opcode => bail!("invalid opcode encoding: {unsupported_opcode:b}"), // Mov
    };
    Ok(instruction)
}

// TODO: Can we directly increment pointers??
fn decode_instructions(buf: &[u8]) -> Result<Instructions> {
    let n_instructions = buf.len() / 2;
    let mut instructions = Vec::with_capacity(n_instructions);
    let mut offset = 0;
    while offset < buf.len() {
        let inst_buf = &buf[offset..];
        let (instruction, size) = decode_instruction(inst_buf)?;
        instructions.push(instruction);
        offset += size;
    }
    Ok(Instructions(instructions))
}

fn main() -> Result<()> {
    use std::env;
    use std::fs::File;
    use std::io::Read;
    let args: Vec<String> = env::args().collect();
    assert!(args.len() == 2, "expect 2 args, got: {args:?}");
    let bin_path = &args[1];
    let mut file = File::open(bin_path)?;
    let mut buf: Vec<u8> = Vec::with_capacity(1000);
    file.read_to_end(&mut buf)?;
    let instructions = decode_instructions(&buf)?;
    println!("bits 16");
    println!("{}", instructions);
    Ok(())

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
        check_debug(
            &instructions,
            expect![[r#"
            Instructions(
                [
                    Mov {
                        w: true,
                        d: false,
                        mode: RegDisplacement0,
                        reg: BX,
                        rm: CX,
                    },
                ],
            )"#]],
        );
        assert_eq!(instructions.to_string(), "mov cx, bx")
    }
}
