// Shared trace helpers. A record is one little-endian [u16;4] = (kind, a, b, c), kept as a u64.
use std::fs::File;
use std::io::{BufWriter, Read, Write};

pub const NONE: usize = 65535;
pub const K_REG: u16 = 1;
pub const K_APPQ: u16 = 2;
pub const K_BINV: u16 = 3;
pub const K_BST0: u16 = 4;
pub const K_BST1: u16 = 5;
pub const K_X: u16 = 6;
pub const K_Z: u16 = 7;
pub const K_CX: u16 = 8;
pub const K_CZ: u16 = 9;
pub const K_HMR: u16 = 12;
pub const K_CCX: u16 = 13;
pub const K_PUSH: u16 = 15;
pub const K_POP: u16 = 16;
pub const K_APPB: u16 = 18;

#[inline(always)] pub fn kind(r: u64) -> u16 { r as u16 }
#[inline(always)] pub fn fa(r: u64) -> usize { ((r >> 16) & 0xffff) as usize }
#[inline(always)] pub fn fb(r: u64) -> usize { ((r >> 32) & 0xffff) as usize }
#[inline(always)] pub fn fc(r: u64) -> usize { (r >> 48) as usize }
#[inline(always)] pub fn rec(k: u16, a: usize, b: usize, c: usize) -> u64 {
    (k as u64) | ((a as u64) << 16) | ((b as u64) << 32) | ((c as u64) << 48)
}

pub fn load_trace(path: &str) -> Vec<u64> {
    let mut f = File::open(path).expect("open trace");
    let len = f.metadata().unwrap().len() as usize;
    assert!(len % 8 == 0);
    let n = len / 8;
    let mut v: Vec<u64> = vec![0; n];
    let bytes = unsafe { std::slice::from_raw_parts_mut(v.as_mut_ptr() as *mut u8, len) };
    let mut off = 0;
    while off < len {
        let end = (off + (1 << 30)).min(len);
        f.read_exact(&mut bytes[off..end]).expect("read trace");
        off = end;
    }
    v
}

pub fn save_trace(path: &str, v: &[u64]) {
    let f = File::create(path).expect("create trace");
    let mut w = BufWriter::with_capacity(1 << 26, f);
    let bytes = unsafe { std::slice::from_raw_parts(v.as_ptr() as *const u8, v.len() * 8) };
    w.write_all(bytes).unwrap();
    w.flush().unwrap();
}

pub fn save_bytes(path: &str, v: &[u8]) {
    let f = File::create(path).expect("create");
    let mut w = BufWriter::with_capacity(1 << 26, f);
    w.write_all(v).unwrap();
    w.flush().unwrap();
}

/// Register layout: regs[r] = list of (is_bit, id) in append order; also qubit and bit counts.
pub struct Layout { pub regs: Vec<Vec<(bool, usize)>>, pub nq: usize, pub nb: usize }

pub fn layout(t: &[u64]) -> Layout {
    let mut regs: Vec<Vec<(bool, usize)>> = Vec::new();
    let (mut nq, mut nb) = (0usize, 0usize);
    let q = |x: usize, nq: &mut usize| { if x != NONE { *nq = (*nq).max(x + 1); } };
    for &r in t {
        let (k, a, b, c) = (kind(r), fa(r), fb(r), fc(r));
        match k {
            K_REG => { while regs.len() <= a { regs.push(Vec::new()); } }
            K_APPQ => { while regs.len() <= a { regs.push(Vec::new()); } regs[a].push((false, b)); q(b, &mut nq); }
            K_APPB => { while regs.len() <= a { regs.push(Vec::new()); } regs[a].push((true, b)); q(b, &mut nb); }
            K_BINV | K_BST0 | K_BST1 => { q(a, &mut nb); q(b, &mut nb); }
            K_X | K_Z => { q(a, &mut nq); q(b, &mut nb); }
            K_CX | K_CZ => { q(a, &mut nq); q(b, &mut nq); q(c, &mut nb); }
            K_HMR => { q(a, &mut nq); q(b, &mut nb); }
            K_CCX => { q(a, &mut nq); q(b, &mut nq); q(c, &mut nq); }
            K_PUSH => { q(a, &mut nb); }
            K_POP => {}
            _ => panic!("unknown kind {}", k),
        }
    }
    Layout { regs, nq, nb }
}
