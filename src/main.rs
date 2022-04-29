use anyhow::{bail, Result};
use minifb::{Key, Scale, Window, WindowOptions};
use rand::prelude::*;
use std::time::{Duration, Instant};

const WIDTH: usize = 64;
const HEIGHT: usize = 32;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Address(u16);
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Register(u8);
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Constant(u8);

enum Behavior {
    Old,
    New,
}

#[derive(Debug)]
enum Instruction {
    SysCall(Address),
    ClearScreen,
    Return,
    Jump(Address),
    Call(Address),
    SkipIfEqual(Register, Constant),
    SkipIfNotEqual(Register, Constant),
    SkipIfRegistersEqual(Register, Register),
    SetImmediate(Register, Constant),
    AddImmediate(Register, Constant),
    SetRegister(Register, Register),
    OrRegister(Register, Register),
    AndRegister(Register, Register),
    XorRegister(Register, Register),
    AdcRegister(Register, Register),
    SwbRegister(Register, Register),
    ShrRegister(Register, Register),
    ReverseSwbRegister(Register, Register),
    ShlRegister(Register, Register),
    SkipIfRegistersNotEqual(Register, Register),
    StoreAddress(Address),
    JumpOffset(Address),
    StoreRandom(Register, Constant),
    DrawSprite(Register, Register, Constant),
    SkipIfPressed(Register),
    SkipIfNotPressed(Register),
    SetFromDelay(Register),
    WaitKeyPress(Register),
    SetToDelay(Register),
    SetToSound(Register),
    AddAddress(Register),
    SetAddressToSprite(Register),
    StoreBCD(Register),
    StoreRegisters(Register),
    LoadRegisters(Register),
}

impl Instruction {
    fn decode(state: &State, mem: &Memory) -> Result<Instruction> {
        let a = (mem.mem[state.ip as usize + 0] & 0xf0) >> 4;
        let b = (mem.mem[state.ip as usize + 0] & 0x0f) >> 0;
        let c = (mem.mem[state.ip as usize + 1] & 0xf0) >> 4;
        let d = (mem.mem[state.ip as usize + 1] & 0x0f) >> 0;

        let addr = |x: u8, y: u8, z: u8| {
            Address(((x as u16) << 8) | ((y as u16) << 4) | ((z as u16) << 0))
        };
        let const2 = |x: u8, y: u8| Constant((x << 4) | y);

        let inst = match a {
            0 if b == 0 && c == 0xe && d == 0 => Instruction::ClearScreen,
            0 if b == 0 && c == 0xe && d == 0xe => Instruction::Return,
            0 => Instruction::SysCall(addr(b, c, d)),
            1 => Instruction::Jump(addr(b, c, d)),
            2 => Instruction::Call(addr(b, c, d)),
            3 => Instruction::SkipIfEqual(Register(b), const2(c, d)),
            4 => Instruction::SkipIfNotEqual(Register(b), const2(c, d)),
            5 if d == 0 => Instruction::SkipIfRegistersEqual(Register(b), Register(c)),
            6 => Instruction::SetImmediate(Register(b), const2(c, d)),
            7 => Instruction::AddImmediate(Register(b), const2(c, d)),
            8 if d == 0 => Instruction::SetRegister(Register(b), Register(c)),
            8 if d == 1 => Instruction::OrRegister(Register(b), Register(c)),
            8 if d == 2 => Instruction::AndRegister(Register(b), Register(c)),
            8 if d == 3 => Instruction::XorRegister(Register(b), Register(c)),
            8 if d == 4 => Instruction::AdcRegister(Register(b), Register(c)),
            8 if d == 5 => Instruction::SwbRegister(Register(b), Register(c)),
            8 if d == 6 => Instruction::ShrRegister(Register(b), Register(c)),
            8 if d == 7 => Instruction::ReverseSwbRegister(Register(b), Register(c)),
            8 if d == 0xe => Instruction::ShlRegister(Register(b), Register(c)),
            9 if d == 0 => Instruction::SkipIfRegistersNotEqual(Register(b), Register(c)),
            0xa => Instruction::StoreAddress(addr(b, c, d)),
            0xb => Instruction::JumpOffset(addr(b, c, d)),
            0xc => Instruction::StoreRandom(Register(b), const2(c, d)),
            0xd => Instruction::DrawSprite(Register(b), Register(c), Constant(d)),
            0xe if c == 0x9 && d == 0xe => Instruction::SkipIfPressed(Register(b)),
            0xe if c == 0xa && d == 0x1 => Instruction::SkipIfNotPressed(Register(b)),
            0xf if c == 0x0 && d == 0x7 => Instruction::SetFromDelay(Register(b)),
            0xf if c == 0x0 && d == 0xa => Instruction::WaitKeyPress(Register(b)),
            0xf if c == 0x1 && d == 0x5 => Instruction::SetToDelay(Register(b)),
            0xf if c == 0x1 && d == 0x8 => Instruction::SetToSound(Register(b)),
            0xf if c == 0x1 && d == 0xe => Instruction::AddAddress(Register(b)),
            0xf if c == 0x2 && d == 0x9 => Instruction::SetAddressToSprite(Register(b)),
            0xf if c == 0x3 && d == 0x3 => Instruction::StoreBCD(Register(b)),
            0xf if c == 0x5 && d == 0x5 => Instruction::StoreRegisters(Register(b)),
            0xf if c == 0x6 && d == 0x5 => Instruction::LoadRegisters(Register(b)),
            _ => {
                bail!(
                    "Unknown opcode at {:03x}: {:x}{:x}{:x}{:x}",
                    state.ip,
                    a,
                    b,
                    c,
                    d
                );
            }
        };

        Ok(inst)
    }

    fn execute(
        &self,
        s: &mut State,
        mem: &mut Memory,
        screen: &mut [u32],
        timer: &mut Timer,
    ) -> Result<()> {
        let mut ip = s.ip + 2;
        match *self {
            Instruction::ClearScreen => {
                screen.fill(0xff000000);
            }
            Instruction::SysCall(_) => {
                todo!();
            }
            Instruction::Return => {
                ip = mem.stack[s.sp];
                s.sp -= 1;
            }
            Instruction::Jump(a) => {
                ip = a.0;
            }
            Instruction::Call(a) => {
                s.sp += 1;
                mem.stack[s.sp] = ip;
                ip = a.0;
            }
            Instruction::SkipIfEqual(r, c) => {
                if s.get(r) == c {
                    ip += 2;
                }
            }
            Instruction::SkipIfNotEqual(r, c) => {
                if s.get(r) != c {
                    ip += 2;
                }
            }
            Instruction::SkipIfRegistersEqual(x, y) => {
                if s.get(x) == s.get(y) {
                    ip += 2;
                }
            }
            Instruction::SetImmediate(r, c) => {
                s.set(r, c);
            }
            Instruction::AddImmediate(r, c) => {
                s.set(r, Constant(s.get(r).0.wrapping_add(c.0)));
            }
            Instruction::SetRegister(x, y) => {
                s.set(x, s.get(y));
            }
            Instruction::AndRegister(x, y) => {
                let val = s.get(x).0 & s.get(y).0;
                s.set(x, Constant(val));
            }
            Instruction::AdcRegister(x, y) => {
                let a = s.get(x);
                let b = s.get(y);
                let c = a.0.checked_add(b.0).is_some();
                s.set(x, Constant(a.0.wrapping_add(b.0)));
                s.set(VF, Constant(if c { 1 } else { 0 }));
            }
            Instruction::SwbRegister(x, y) => {
                let a = s.get(x);
                let b = s.get(y);
                let c = a.0.checked_sub(b.0).is_some();
                s.set(x, Constant(a.0.wrapping_sub(b.0)));
                s.set(VF, Constant(if c { 1 } else { 0 }));
            }
            Instruction::StoreAddress(a) => {
                s.address = a;
            }
            Instruction::StoreRandom(r, c) => {
                let val = rand::random::<u8>() & c.0;
                s.set(r, Constant(val))
            }
            Instruction::DrawSprite(x, y, n) => {
                let mut flipped_any_pixels_to_unset = false;
                let x = s.get(x).0 as usize;
                let y = s.get(y).0 as usize;
                for row in 0..n.0 as usize {
                    let offset = x + (y + row) * WIDTH;
                    let pixels = mem.mem[s.address.0 as usize + row];
                    for bit in 0..8 {
                        let sprite_bit = if (pixels & (1 << (7 - bit))) != 0 {
                            1
                        } else {
                            0
                        };
                        let screen_bit = if screen[offset + bit as usize] == 0xffffffff {
                            1
                        } else {
                            0
                        };
                        let new_bit = screen_bit ^ sprite_bit;
                        if new_bit == 0 && screen_bit == 1 {
                            flipped_any_pixels_to_unset = true;
                        }
                        if new_bit == 0 {
                            if screen_bit == 1 {
                                flipped_any_pixels_to_unset = true;
                            }
                            screen[offset + bit as usize] = 0xFF000000;
                        } else {
                            screen[offset + bit as usize] = 0xffffffff;
                        }
                    }
                }
                s.set(
                    VF,
                    Constant(if flipped_any_pixels_to_unset { 1 } else { 0 }),
                )
            }
            Instruction::SkipIfPressed(_) => {
                //
            }
            Instruction::SkipIfNotPressed(_) => {
                ip += 2;
            }
            Instruction::SetFromDelay(r) => {
                s.set(r, Constant(timer.delay_value));
            }
            Instruction::SetToDelay(r) => timer.delay_value = s.get(r).0,
            Instruction::SetToSound(r) => timer.sound_value = s.get(r).0,
            Instruction::AddAddress(r) => {
                s.address = Address(s.address.0 + s.get(r).0 as u16);
            }
            Instruction::SetAddressToSprite(x) => {
                let val = s.get(x).0;
                if val <= 0xf {
                    s.address = Address(5 * val as u16);
                }
            }
            Instruction::StoreBCD(r) => {
                let val = s.get(r).0;
                let h = val / 100;
                mem.mem[s.address.0 as usize + 0] = h;
                let t = (val - 100 * h) / 10;
                mem.mem[s.address.0 as usize + 1] = t;
                let o = val - 100 * h - 10 * t;
                mem.mem[s.address.0 as usize + 2] = o;
            }
            Instruction::StoreRegisters(x) => {
                for i in 0..x.0 {
                    mem.mem[s.address.0 as usize + i as usize] = s.v[i as usize];
                }
            }
            Instruction::LoadRegisters(x) => {
                for i in 0..x.0 {
                    s.v[i as usize] = mem.mem[s.address.0 as usize + i as usize];
                }
            }
            _ => {
                todo!("{:?}", *self);
            }
        }
        s.ip = ip;
        Ok(())
    }
}

const VF: Register = Register(0xf);

struct State {
    ip: u16,
    finished: bool,
    address: Address,
    sp: usize,
    v: [u8; 16],
}

impl State {
    fn get(&self, r: Register) -> Constant {
        Constant(self.v[r.0 as usize])
    }

    fn set(&mut self, r: Register, c: Constant) {
        self.v[r.0 as usize] = c.0;
    }
}

impl Default for State {
    fn default() -> Self {
        State {
            ip: 0x200,
            finished: false,
            address: Address(0),
            sp: 0,
            v: [0; 16],
        }
    }
}

struct Timer {
    delay_value: u8,
    sound_value: u8,
    last_update: Instant,
}

impl Default for Timer {
    fn default() -> Self {
        Timer {
            delay_value: 0,
            sound_value: 0,
            last_update: Instant::now(),
        }
    }
}

impl Timer {
    fn update(&mut self) -> bool {
        let now = Instant::now();
        let diff = now - self.last_update;
        if diff.as_micros() >= 16600 {
            if self.delay_value > 0 {
                self.delay_value -= 1;
            }
            if self.sound_value > 0 {
                self.sound_value -= 1;
            }
            self.last_update = now;
            true
        } else {
            false
        }
    }
}

struct Memory {
    stack: [u16; 16],
    mem: [u8; 4096],
}

impl Default for Memory {
    fn default() -> Self {
        Memory {
            stack: [0; 16],
            mem: [0; 4096],
        }
    }
}

fn main() -> Result<()> {
    let mut buffer: Vec<u32> = vec![0; WIDTH * HEIGHT];
    let options = WindowOptions {
        scale: Scale::X8,
        ..WindowOptions::default()
    };

    let mut window = Window::new("Chip8", WIDTH, HEIGHT, options)?;

    //window.limit_update_rate(Some(Duration::from_micros(16600)));
    window.limit_update_rate(None);

    let mut timer = Timer::default();
    let mut memory = Memory::default();
    let mut state = State::default();

    // Load ROM.
    let rom = std::fs::read("roms/BLINKY")?;
    memory.mem[0x200..0x200 + rom.len()].copy_from_slice(&rom);

    // Load ROM font.
    memory.mem[5 * 0x0..5 * 0x1].copy_from_slice(&[0xf0, 0x90, 0x90, 0x90, 0xf0]);
    memory.mem[5 * 0x1..5 * 0x2].copy_from_slice(&[0x20, 0x60, 0x20, 0x20, 0x70]);
    memory.mem[5 * 0x2..5 * 0x3].copy_from_slice(&[0xf0, 0x10, 0xf0, 0x80, 0xf0]);
    memory.mem[5 * 0x3..5 * 0x4].copy_from_slice(&[0xf0, 0x10, 0xf0, 0x10, 0xf0]);
    memory.mem[5 * 0x4..5 * 0x5].copy_from_slice(&[0x90, 0x90, 0xf0, 0x10, 0x10]);
    memory.mem[5 * 0x5..5 * 0x6].copy_from_slice(&[0xf0, 0x80, 0xf0, 0x10, 0xf0]);
    memory.mem[5 * 0x6..5 * 0x7].copy_from_slice(&[0xf0, 0x80, 0xf0, 0x90, 0xf0]);
    memory.mem[5 * 0x7..5 * 0x8].copy_from_slice(&[0xf0, 0x10, 0x20, 0x40, 0x40]);
    memory.mem[5 * 0x8..5 * 0x9].copy_from_slice(&[0xf0, 0x90, 0xf0, 0x90, 0xf0]);
    memory.mem[5 * 0x9..5 * 0xa].copy_from_slice(&[0xf0, 0x90, 0xf0, 0x10, 0xf0]);
    memory.mem[5 * 0xa..5 * 0xb].copy_from_slice(&[0xf0, 0x90, 0xf0, 0x90, 0x90]);
    memory.mem[5 * 0xb..5 * 0xc].copy_from_slice(&[0xe0, 0x90, 0xe0, 0x90, 0xe0]);
    memory.mem[5 * 0xc..5 * 0xd].copy_from_slice(&[0xf0, 0x80, 0x80, 0x80, 0xf0]);
    memory.mem[5 * 0xd..5 * 0xe].copy_from_slice(&[0xe0, 0x90, 0x90, 0x90, 0xe0]);
    memory.mem[5 * 0xe..5 * 0xf].copy_from_slice(&[0xf0, 0x80, 0xf0, 0x80, 0xf0]);
    memory.mem[5 * 0xf..5 * 0x10].copy_from_slice(&[0xf0, 0x80, 0xf0, 0x80, 0x80]);

    while window.is_open() && !window.is_key_down(Key::Escape) && !state.finished {
        let redraw = timer.update();
        let instruction = Instruction::decode(&state, &memory)?;
        //println!("0x{:04x}: {:?}", state.ip, instruction);
        instruction.execute(&mut state, &mut memory, &mut buffer, &mut timer)?;

        if redraw {
            window.update_with_buffer(&buffer, WIDTH, HEIGHT)?;
        }
    }

    Ok(())
}
