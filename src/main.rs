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
        src: Reg,
        dest: Reg,
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
            Instruction::Mov { src, dest } => (src, dest)
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

fn decode_reg(w: u8, bits: u8) -> Result<Reg> {
    use crate::Reg::*;
    match (bits, w) {
        // Decode BYTE (u8)
        (0b0000_0000, 0) => Ok(AL),
        (0b0000_0001, 0) => Ok(CL),
        (0b0000_0010, 0) => Ok(DL),
        (0b0000_0011, 0) => Ok(BL),
        (0b0000_0100, 0) => Ok(AH),
        (0b0000_0101, 0) => Ok(CH),
        (0b0000_0110, 0) => Ok(DH),
        (0b0000_0111, 0) => Ok(BH),

        // Decode WORD (u8 u8)
        (0b0000_0000, 1) => Ok(AX),
        (0b0000_0001, 1) => Ok(CX),
        (0b0000_0010, 1) => Ok(DX),
        (0b0000_0011, 1) => Ok(BX),
        (0b0000_0100, 1) => Ok(SP),
        (0b0000_0101, 1) => Ok(BP),
        (0b0000_0110, 1) => Ok(SI),
        (0b0000_0111, 1) => Ok(DI),
        _ => {
            bail!("invalid reg encoding: {bits:b}")
        }
    }
}

// -------
//   MOV
// -------

fn decode_rm(w: u8, buf: &[u8]) -> Result<Reg> {
    let b2 = buf[0];
    const MOD_MASK: u8 = 0b1100_0000;
    const RM_MASK: u8 = 0b0000_0111;
    let _mode = match b2 & MOD_MASK {
        0b0000_0000 => Mode::MemDisplacement0,
        0b0100_0000 => Mode::MemDisplacement8,
        0b1000_0000 => Mode::MemDisplacement16,
        0b1100_0000 => Mode::RegDisplacement0,
        e => {
            bail!("invalid mode encoding: {e:b}")
        }
    };
    decode_reg(w, b2 & RM_MASK)
}

// type DispLo = u8;
// type DispHi = u8;
/// Decode 2nd byte of mov rm reg.
fn decode_mov_rm_reg_b2(d: u8, w: u8, buf: &[u8]) -> Result<(Instruction, Size)> {
    let b2 = buf[0];
    const REG_MASK: u8 = 0b0011_1000;

    // Always decode reg field as register.
    let reg = decode_reg(w, (b2 & REG_MASK) >> 3)?;

    // Decode rm depends on mode.
    let rm = decode_rm(w, buf)?;

    let (src, dest) = match d {
        0 => (reg, rm),
        1 => (rm, reg),
        _ => unreachable!(),
    };
    Ok((
        Instruction::Mov {
            src, dest
        },
        2,
    ))
}

type Size = usize;

fn decode_instruction(buf: &[u8]) -> Result<(Instruction, Size)> {
    debug_assert!(!buf.is_empty());

    let b1 = buf[0];
    let buf = &buf[1..];
    let instruction = match b1 {
        // MOV r/m reg
        0b10_001000 => decode_mov_rm_reg_b2(0, 0, buf)?,
        0b10_001001 => decode_mov_rm_reg_b2(0, 1, buf)?,
        0b10_001010 => decode_mov_rm_reg_b2(1, 0, buf)?,
        0b10_001011 => decode_mov_rm_reg_b2(0, 1, buf)?,
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
                            src: BX,
                            dest: CX,
                        },
                    ],
                )"#]],
        );
        assert_eq!(instructions.to_string(), "mov cx, bx")
    }

    #[test]
    fn test_38_decode() {
        let listing38 = [
            0b1000_1001, 0b1101_1001, 0b1000_1000, 0b1110_0101,
            0b1000_1001, 0b1101_1010, 0b1000_1001, 0b1101_1110,
            0b1000_1001, 0b1111_1011, 0b1000_1000, 0b1100_1000,
            0b1000_1000, 0b1110_1101, 0b1000_1001, 0b1100_0011,
            0b1000_1001, 0b1111_0011, 0b1000_1001, 0b1111_1100,
            0b1000_1001, 0b1100_0101
        ];

        let instructions = decode_instructions(&listing38).unwrap();
        check_debug(
            &instructions,
            expect![[r#"
                Instructions(
                    [
                        Mov {
                            src: BX,
                            dest: CX,
                        },
                        Mov {
                            src: AH,
                            dest: CH,
                        },
                        Mov {
                            src: BX,
                            dest: DX,
                        },
                        Mov {
                            src: BX,
                            dest: SI,
                        },
                        Mov {
                            src: DI,
                            dest: BX,
                        },
                        Mov {
                            src: CL,
                            dest: AL,
                        },
                        Mov {
                            src: CH,
                            dest: CH,
                        },
                        Mov {
                            src: AX,
                            dest: BX,
                        },
                        Mov {
                            src: SI,
                            dest: BX,
                        },
                        Mov {
                            src: DI,
                            dest: SP,
                        },
                        Mov {
                            src: AX,
                            dest: BP,
                        },
                    ],
                )"#]],
        );
        assert_eq!(instructions.to_string(),
                   "mov cx, bx
mov ch, ah
mov dx, bx
mov si, bx
mov bx, di
mov al, cl
mov ch, ch
mov bx, ax
mov bx, si
mov sp, di
mov bp, ax")
    }
}
