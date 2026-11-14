use std::io::{self, Read};

const PERIODS: [usize; 32] = [
    1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,20,24,28,32,40,48,56,64,80,96,112,128,160,192,224,256,
];

fn invalid(reason: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, reason)
}
fn read_u32(r: &mut impl Read) -> io::Result<usize> {
    let mut b = [0;4];r.read_exact(&mut b)?;Ok(u32::from_le_bytes(b) as usize)
}
fn varint(code: &[u8], at: &mut usize) -> io::Result<usize> {
    let mut result=0;
    for shift in [0,7,14,21,28] {
        let byte=*code.get(*at).ok_or_else(||invalid("short run length"))?;
        *at += 1;result|=((byte&127) as usize)<<shift;
        if byte<128 {return Ok(result);}
    }
    Err(invalid("unbounded run length"))
}

fn decode_legacy(mut input: impl Read, mut emit: impl FnMut([u16;4])) -> io::Result<usize> {
    let mut total=0usize;
    loop {
        let n=read_u32(&mut input)?;
        if n==0 {break;}
        let nb=read_u32(&mut input)?;let nl=read_u32(&mut input)?;
        if n>1<<20 || nl>n || nb>2*n {return Err(invalid("invalid block dimensions"));}
        let mut data=vec![0;nb+7*nl];input.read_exact(&mut data)?;
        let (cmd,lits)=data.split_at(nb);
        let mut last=[[0u16;3];19];let mut history=Vec::<[u16;4]>::with_capacity(n);
        let (mut i,mut at,mut lit)=(0usize,0usize,0usize);
        while i<n {
            let token=*cmd.get(at).ok_or_else(||invalid("missing instruction"))? as usize;at+=1;
            if token==0 {
                if lit>=nl{return Err(invalid("missing literal"));}
                let kind=lits[lit] as usize;
                if kind>18{return Err(invalid("bad gate kind"));}
                let mut row=[kind as u16,0,0,0];
                for j in 0..3 {
                    let lo=lits[(1+2*j)*nl+lit];let hi=lits[(2+2*j)*nl+lit];
                    let z=u16::from_le_bytes([lo,hi]);
                    let d=(z>>1) ^ (0u16.wrapping_sub(z&1));
                    last[kind][j]=last[kind][j].wrapping_add(d);
                    row[j+1]=last[kind][j];
                }
                history.push(row);emit(row);i+=1;lit+=1;
            } else if (64..82).contains(&token) {
                let remapped=token>=80;
                let reverse=if remapped{token==81}else{token&8!=0};
                let distance=varint(cmd,&mut at)?+1;
                let count=varint(cmd,&mut at)?+4;
                if distance>i || count>n-i {return Err(invalid("invalid copy"));}
                let source=i-distance;
                if reverse && count>source+1{return Err(invalid("reversed copy exceeds history"));}
                let mut d=[0u16;3];
                let mut pieces=Vec::new();
                if remapped {
                    let k=varint(cmd,&mut at)?;
                    if k==0||k>128{return Err(invalid("invalid wire mapping"));}
                    let mut start=0usize;
                    for j in 0..k {
                        if j!=0 {start+=varint(cmd,&mut at)?;}
                        let z=varint(cmd,&mut at)?;
                        if start>=65535||z>65535{return Err(invalid("invalid wire mapping"));}
                        let x=z as u16;pieces.push((start as u16,(x>>1)^0u16.wrapping_sub(x&1)));
                    }
                } else {for j in 0..3 {
                    if token&(1<<j)!=0 {
                        let raw=varint(cmd,&mut at)?;
                        if raw>65535{return Err(invalid("invalid wire translation"));}
                        let z=raw as u16;d[j]=(z>>1)^0u16.wrapping_sub(z&1);
                    }
                }}
                for k in 0..count {
                    let mut row=history[if reverse{source-k}else{source+k}];
                    for j in 0..3 {if row[j+1]!=65535{
                        let off=if remapped {pieces[pieces.partition_point(|&(x,_)|x<=row[j+1])-1].1}else{d[j]};
                        row[j+1]=row[j+1].wrapping_add(off);
                    }}
                    history.push(row);emit(row);i+=1;
                }
            } else {
                let p=*PERIODS.get(token-1).ok_or_else(||invalid("bad period"))?;
                let count=varint(cmd,&mut at)?.checked_add(3).ok_or_else(||invalid("run overflow"))?;
                if i<2*p || count>n-i{return Err(invalid("invalid affine run"));}
                for _ in 0..count {
                    let x=history[i-p];let y=history[i-2*p];
                    let mut row=[0u16;4];
                    for j in 0..4 {row[j]=x[j].wrapping_mul(2).wrapping_sub(y[j]);}
                    history.push(row);emit(row);i+=1;
                }
            }
        }
        if at!=cmd.len() || lit!=nl{return Err(invalid("unused block data"));}
        total=total.checked_add(n).ok_or_else(||invalid("record count overflow"))?;
    }
    let mut extra=[0];if input.read(&mut extra)?!=0{return Err(invalid("trailing bytes"));}
    Ok(total)
}

// ---- GATEIR3: one zstd frame holding 27 field streams (see the preamble below) ----
// Layout after the 8-byte magic: 27 u32le stream lengths, then the streams in this order:
// hdr tok acnt rk dist.0-2 cnt.0-2 tr.0-2 rr.0-2 ra.0-2 rz.0-2 litk lit13 lit8 lit6 litm
const NSTREAMS: usize = 27;
const MAX_TOTAL: usize = 256 << 20;

struct Planes {
    p: [Vec<u8>; 3],
    at: [usize; 3],
}
impl Planes {
    fn get(&mut self) -> io::Result<usize> {
        let mut x = 0usize;
        for k in 0..3 {
            let c = *self.p[k].get(self.at[k]).ok_or_else(|| invalid("short plane stream"))?;
            self.at[k] += 1;
            x |= ((c & 127) as usize) << (7 * k);
            if c < 128 {
                return Ok(x);
            }
        }
        Err(invalid("plane varint too long"))
    }
    fn done(&self) -> bool {
        (0..3).all(|k| self.at[k] == self.p[k].len())
    }
}
fn take(streams: &mut std::vec::IntoIter<Vec<u8>>) -> Vec<u8> {
    streams.next().expect("stream table")
}
fn take_planes(streams: &mut std::vec::IntoIter<Vec<u8>>) -> Planes {
    Planes { p: [take(streams), take(streams), take(streams)], at: [0; 3] }
}
fn unzig(z: usize) -> io::Result<u16> {
    if z > 65535 {
        return Err(invalid("invalid zigzag value"));
    }
    let x = z as u16;
    Ok((x >> 1) ^ 0u16.wrapping_sub(x & 1))
}

/// GATEIR3: read the 27 field streams from the zstd-decompressed reader.
fn read_streams_v3(mut input: impl Read) -> io::Result<Vec<Vec<u8>>> {
    let mut lens = [0usize; NSTREAMS];
    let mut sum = 0usize;
    for l in lens.iter_mut() {
        *l = read_u32(&mut input)?;
        sum = sum.checked_add(*l).ok_or_else(|| invalid("stream length overflow"))?;
    }
    if sum > MAX_TOTAL {
        return Err(invalid("stream lengths too large"));
    }
    let mut v = Vec::with_capacity(NSTREAMS);
    for &l in lens.iter() {
        let mut s = vec![0u8; l];
        input.read_exact(&mut s)?;
        v.push(s);
    }
    let mut extra = [0];
    if input.read(&mut extra)? != 0 {
        return Err(invalid("trailing bytes"));
    }
    Ok(v)
}

/// Decode records from the 27 field streams (shared by GATEIR3 and GATEIR4).
fn decode_streams(v: Vec<Vec<u8>>, mut emit: impl FnMut([u16; 4])) -> io::Result<usize> {
    let mut it = v.into_iter();
    let hdr = take(&mut it);
    let tok = take(&mut it);
    let acnt = take(&mut it);
    let rk = take(&mut it);
    let mut dist = take_planes(&mut it);
    let mut cnt = take_planes(&mut it);
    let mut tr = take_planes(&mut it);
    let mut rr = take_planes(&mut it);
    let mut ra = take_planes(&mut it);
    let mut rz = take_planes(&mut it);
    let litk = take(&mut it);
    let lg: [Vec<u8>; 4] = [take(&mut it), take(&mut it), take(&mut it), take(&mut it)];
    let (mut tp, mut ap, mut kp, mut lkp) = (0usize, 0usize, 0usize, 0usize);
    let mut lgp = [0usize; 4];
    if hdr.len() % 4 != 0 {
        return Err(invalid("bad block table"));
    }
    let mut bm = vec![0u64; 1024];
    let mut wt: Vec<u16> = Vec::with_capacity(65537);
    let mut total = 0usize;
    for hb in hdr.chunks_exact(4) {
        let n = u32::from_le_bytes([hb[0], hb[1], hb[2], hb[3]]) as usize;
        if n == 0 || n > 1 << 20 {
            return Err(invalid("invalid block dimensions"));
        }
        let mut last = [[0u16; 3]; 19];
        let mut history = Vec::<[u16; 4]>::with_capacity(n);
        let mut i = 0usize;
        while i < n {
            let token = *tok.get(tp).ok_or_else(|| invalid("missing instruction"))? as usize;
            tp += 1;
            if token == 0 {
                let kind = *litk.get(lkp).ok_or_else(|| invalid("missing literal"))? as usize;
                lkp += 1;
                if kind > 18 {
                    return Err(invalid("bad gate kind"));
                }
                let g = match kind {
                    13 => 0,
                    8 => 1,
                    6 => 2,
                    _ => 3,
                };
                let bytes = lg[g].get(lgp[g]..lgp[g] + 6).ok_or_else(|| invalid("missing literal bytes"))?;
                lgp[g] += 6;
                let mut row = [kind as u16, 0, 0, 0];
                for j in 0..3 {
                    let z = u16::from_le_bytes([bytes[2 * j], bytes[2 * j + 1]]);
                    let d = (z >> 1) ^ (0u16.wrapping_sub(z & 1));
                    last[kind][j] = last[kind][j].wrapping_add(d);
                    row[j + 1] = last[kind][j];
                }
                history.push(row);
                emit(row);
                i += 1;
            } else if (64..82).contains(&token) {
                let remapped = token >= 80;
                let reverse = if remapped { token == 81 } else { token & 8 != 0 };
                let distance = dist.get()? + 1;
                let count = cnt.get()? + 4;
                if distance > i || count > n - i {
                    return Err(invalid("invalid copy"));
                }
                let source = i - distance;
                if reverse && count > source + 1 {
                    return Err(invalid("reversed copy exceeds history"));
                }
                let mut d = [0u16; 3];
                let mut pieces: Vec<(u16, u16)> = Vec::new();
                if remapped {
                    // W = sorted distinct non-65535 wires (fields 1..3) of the source rows available before this copy
                    let avail = if reverse { count } else { count.min(distance) };
                    let (mut lo_w, mut hi_w) = (usize::MAX, 0usize);
                    for q in 0..avail {
                        let r = &history[if reverse { source - q } else { source + q }];
                        for j in 1..4 {
                            let w = r[j];
                            if w != 65535 {
                                let wi = (w >> 6) as usize;
                                bm[wi] |= 1u64 << (w & 63);
                                lo_w = lo_w.min(wi);
                                hi_w = hi_w.max(wi);
                            }
                        }
                    }
                    wt.clear();
                    if lo_w != usize::MAX {
                        for b in lo_w..=hi_w {
                            let mut x = bm[b];
                            bm[b] = 0;
                            while x != 0 {
                                wt.push((b * 64) as u16 + x.trailing_zeros() as u16);
                                x &= x - 1;
                            }
                        }
                    }
                    wt.push(65535);
                    let wc = wt.len() - 1;
                    let k = varint(&rk, &mut kp)?;
                    if k == 0 || k > 128 {
                        return Err(invalid("invalid wire mapping"));
                    }
                    let (mut start, mut prev_rank) = (0usize, 0usize);
                    for j in 0..k {
                        if j != 0 {
                            let rank = prev_rank + rr.get()?;
                            let adj = ra.get()?;
                            if rank > wc {
                                return Err(invalid("rank out of range"));
                            }
                            let ns = (wt[rank] as usize).checked_sub(adj).ok_or_else(|| invalid("bad rank adjustment"))?;
                            if ns < start {
                                return Err(invalid("unordered wire mapping"));
                            }
                            start = ns;
                            prev_rank = rank;
                        }
                        let z = rz.get()?;
                        if start >= 65535 || z > 65535 {
                            return Err(invalid("invalid wire mapping"));
                        }
                        pieces.push((start as u16, unzig(z)?));
                    }
                } else {
                    for j in 0..3 {
                        if token & (1 << j) != 0 {
                            d[j] = unzig(tr.get()?)?;
                        }
                    }
                }
                for k in 0..count {
                    let mut row = history[if reverse { source - k } else { source + k }];
                    for j in 0..3 {
                        if row[j + 1] != 65535 {
                            let off = if remapped {
                                pieces[pieces.partition_point(|&(x, _)| x <= row[j + 1]) - 1].1
                            } else {
                                d[j]
                            };
                            row[j + 1] = row[j + 1].wrapping_add(off);
                        }
                    }
                    history.push(row);
                    emit(row);
                    i += 1;
                }
            } else {
                let p = *PERIODS.get(token - 1).ok_or_else(|| invalid("bad period"))?;
                let count = varint(&acnt, &mut ap)?.checked_add(3).ok_or_else(|| invalid("run overflow"))?;
                if i < 2 * p || count > n - i {
                    return Err(invalid("invalid affine run"));
                }
                for _ in 0..count {
                    let x = history[i - p];
                    let y = history[i - 2 * p];
                    let mut row = [0u16; 4];
                    for j in 0..4 {
                        row[j] = x[j].wrapping_mul(2).wrapping_sub(y[j]);
                    }
                    history.push(row);
                    emit(row);
                    i += 1;
                }
            }
        }
        total = total.checked_add(n).ok_or_else(|| invalid("record count overflow"))?;
    }
    let planes_done = dist.done() && cnt.done() && tr.done() && rr.done() && ra.done() && rz.done();
    if tp != tok.len() || ap != acnt.len() || kp != rk.len() || lkp != litk.len() || !planes_done
        || (0..4).any(|g| lgp[g] != lg[g].len())
    {
        return Err(invalid("unused stream data"));
    }
    Ok(total)
}

pub fn decode_records(mut input: impl Read, emit: impl FnMut([u16; 4])) -> io::Result<usize> {
    let mut magic = [0; 8];
    input.read_exact(&mut magic)?;
    if &magic == b"GATEIR3\n" {
        decode_streams(read_streams_v3(input)?, emit)
    } else if &magic == b"GATEIR4\n" {
        let mut rest = Vec::new();
        input.read_to_end(&mut rest)?;
        decode_streams(super::v4_part::read_streams_v4(&rest)?, emit)
    } else if &magic == b"GATEIR1\n" || &magic == b"GATEIR2\n" {
        decode_legacy(input, emit)
    } else {
        Err(invalid("wrong gate IR version"))
    }
}
