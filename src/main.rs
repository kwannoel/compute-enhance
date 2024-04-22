use anyhow::{bail, Result};
use std::fmt;

#[derive(Clone, Debug)]
pub enum MemReg {
    Two((Reg, Reg)),
    One(Reg),
    Zero,
}

#[derive(Clone, Debug)]
pub struct Mem {
    regs: MemReg,
    displacement: u16,
}

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
pub enum Arg {
    Reg(Reg),
    Mem(Mem),
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
    Mov { src: Arg, dest: Arg },
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

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = format!("{:?}", self).to_lowercase();
        write!(f, "{s}")
    }
}

impl fmt::Display for MemReg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use crate::MemReg::*;
        let s = match self {
            Two((r1, r2)) => format!("{r1} + {r2}"),
            One(r1) => r1.to_string(),
            Zero => "".to_string(),
        };
        write!(f, "{s}")
    }
}

impl fmt::Display for Mem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Self { regs, displacement } = self;
        let s = regs.to_string();
        let d = displacement.to_string();
        let sd = match (s.as_str(), d.as_str()) {
            ("", _) => d,
            (_, "0") => s,
            (_, _) => format!("{s} + {d}"),
        };
        write!(f, "[{sd}]")
    }
}

impl fmt::Display for Arg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Self::Reg(r) => format!("{:?}", r).to_lowercase(),
            Self::Mem(m) => m.to_string(),
        };
        write!(f, "{s}")
    }
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let op: InstructionName = self.into();
        let (src, dest) = match self {
            Instruction::Mov { src, dest } => (src, dest),
        };
        let op_str = format!("{:?}", op).to_lowercase();
        let src_str = format!("{}", src);
        let dest_str = format!("{}", dest);
        write!(f, "{op_str} {dest_str}, {src_str}")
    }
}

#[derive(Clone, Debug)]
pub struct Instructions(Vec<Instruction>);

impl fmt::Display for Instructions {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let last_idx = self.0.len() - 1;
        for inst in &self.0[..last_idx] {
            writeln!(f, "{inst}")?;
        }
        let last = &self.0[last_idx];
        write!(f, "{last}")?;
        Ok(())
    }
}

fn decode_reg(w: u8, bits: u8) -> Result<Reg> {
    use crate::Reg::*;
    const REG_MASK: u8 = 0b0000_0111;
    let bits = bits & REG_MASK;
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

fn decode_reg_arg(w: u8, bits: u8) -> Result<(Size, Arg)> {
    Ok((1, Arg::Reg(decode_reg(w, bits)?)))
}

// -------
//   MOV
// -------

// TODO: Can we directly cast and index a u16 value?
fn decode_u16(lo: u8, hi: u8) -> u16 {
    let mut result = 0u16;
    result &= lo as u16;
    result &= (hi as u16) << 8;
    result
}

fn decode_mem_regs(buf: &[u8]) -> Result<MemReg> {
    use crate::MemReg::*;
    use crate::Reg::*;
    let r = match buf[0] & 0b0000_0111 {
        0b0000_0000 => Two((BX, SI)),
        0b0000_0001 => Two((BX, DI)),
        0b0000_0010 => Two((BP, SI)),
        0b0000_0011 => Two((BP, DI)),
        0b0000_0100 => One(SI),
        0b0000_0101 => One(DI),
        0b0000_0110 => One(BP),
        0b0000_0111 => One(BX),
        _ => bail!("invalid encoding for rm"),
    };
    Ok(r)
}

fn decode_rm_0(buf: &[u8]) -> Result<(Size, Arg)> {
    use crate::MemReg::*;
    use crate::Reg::*;
    let regs = decode_mem_regs(buf)?;
    let (sz, displacement, regs) = match regs {
        // 110, DIRECT ADDRESS
        One(BP) => (3, decode_u16(buf[1], buf[2]), Zero),
        _ => (1, 0, regs),
    };
    Ok((sz, Arg::Mem(Mem { regs, displacement })))
}

fn decode_rm_1(buf: &[u8]) -> Result<(Size, Arg)> {
    let regs = decode_mem_regs(buf)?;
    let displacement = buf[1] as u16;
    Ok((2, Arg::Mem(Mem { regs, displacement })))
}

fn decode_rm_2(buf: &[u8]) -> Result<(Size, Arg)> {
    let regs = decode_mem_regs(buf)?;
    let displacement = decode_u16(buf[1], buf[2]);
    Ok((3, Arg::Mem(Mem { regs, displacement })))
}

fn decode_rm(w: u8, buf: &[u8]) -> Result<(Size, Arg)> {
    let b2 = buf[0];
    let sz_rm = match b2 >> 6 {
        0b0000_0000 => decode_rm_0(buf)?,
        0b0000_0001 => decode_rm_1(buf)?,
        0b0000_0010 => decode_rm_2(buf)?,
        0b0000_0011 => decode_reg_arg(w, b2)?,
        e => {
            bail!("invalid mode encoding: {e:b}")
        }
    };
    Ok(sz_rm)
}

// type DispLo = u8;
// type DispHi = u8;
fn decode_mov_rm_reg(d: u8, w: u8, buf: &[u8]) -> Result<(Size, Instruction)> {
    let b2 = buf[0];
    // Always decode reg field as register.
    let reg = Arg::Reg(decode_reg(w, b2 >> 3)?);
    let reg_sz = 1;

    // Decode rm depends on mode.
    let (rm_sz, rm) = decode_rm(w, buf)?;

    let (src, dest) = match d {
        0 => (reg, rm),
        1 => (rm, reg),
        _ => unreachable!(),
    };
    let sz = reg_sz + rm_sz;
    Ok((sz, Instruction::Mov { src, dest }))
}

type Size = usize;

fn decode_instruction(buf: &[u8]) -> Result<(Size, Instruction)> {
    debug_assert!(!buf.is_empty());

    let b1 = buf[0];
    let buf = &buf[1..];
    let instruction = match b1 {
        // MOV r/m reg
        0b10_001000..=0b10_001011 => {
            decode_mov_rm_reg((b1 & 0b0000_0010) >> 1, b1 & 0b0000_0001, buf)?
        }
        // MOV imm rm
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
        let (size, instruction) = decode_instruction(inst_buf)?;
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
        expect.assert_eq(&format!("{:?}", actual));
    }

    #[test]
    fn test_37_decode() {
        let listing37 = [0b1000_1001, 0b1101_1001];
        let instructions = decode_instructions(&listing37).unwrap();
        check_debug(
            &instructions,
            expect!["Instructions([Mov { src: Reg(BX), dest: Reg(CX) }])"],
        );
        assert_eq!(instructions.to_string(), "mov cx, bx")
    }

    #[test]
    fn test_38_decode() {
        let listing38 = [
            0b1000_1001,
            0b1101_1001,
            0b1000_1000,
            0b1110_0101,
            0b1000_1001,
            0b1101_1010,
            0b1000_1001,
            0b1101_1110,
            0b1000_1001,
            0b1111_1011,
            0b1000_1000,
            0b1100_1000,
            0b1000_1000,
            0b1110_1101,
            0b1000_1001,
            0b1100_0011,
            0b1000_1001,
            0b1111_0011,
            0b1000_1001,
            0b1111_1100,
            0b1000_1001,
            0b1100_0101,
        ];

        let instructions = decode_instructions(&listing38).unwrap();
        check_debug(
            &instructions,
            expect!["Instructions([Mov { src: Reg(BX), dest: Reg(CX) }, Mov { src: Reg(AH), dest: Reg(CH) }, Mov { src: Reg(BX), dest: Reg(DX) }, Mov { src: Reg(BX), dest: Reg(SI) }, Mov { src: Reg(DI), dest: Reg(BX) }, Mov { src: Reg(CL), dest: Reg(AL) }, Mov { src: Reg(CH), dest: Reg(CH) }, Mov { src: Reg(AX), dest: Reg(BX) }, Mov { src: Reg(SI), dest: Reg(BX) }, Mov { src: Reg(DI), dest: Reg(SP) }, Mov { src: Reg(AX), dest: Reg(BP) }])"],
        );
        assert_eq!(
            instructions.to_string(),
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
mov bp, ax"
        )
    }

    #[test]
    fn test_39_decode() {
        let listing39 = [
            0b1000_1001,
            0b11011110,
            0b1000_1000,
            0b1100_0110,
            // 0b10110001, 0b0000_1100, 0b10110101,
            // 11110100 10111001 00001100 00000000 10111001  ...... //
            // 0000000c: 11110100 11111111 10111010 01101100 00001111 10111010  ...l..
            // 00000012: 10010100 11110000 10001010 00000000 10001011 00011011  ......
            // 00000018: 10001011 01010110 00000000 10001010 01100000 00000100  .V..`.
            // 0000001e: 10001010 10000000 10000111 00010011 10001001 00001001  ......
            // 00000024: 10001000 00001010 10001000 01101110 00000000           ...n.
        ];

        let instructions = decode_instructions(&listing39).unwrap();
        check_debug(
            &instructions,
            expect!["Instructions([Mov { src: Reg(BX), dest: Reg(SI) }, Mov { src: Reg(AL), dest: Reg(DH) }])"],
        );
        assert_eq!(
            instructions.to_string(),
            "mov si, bx
mov dh, al" // mov cl, 12
                        // "
        )
    }
}
