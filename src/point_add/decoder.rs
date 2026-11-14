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

pub fn decode_records(mut input: impl Read, mut emit: impl FnMut([u16;4])) -> io::Result<usize> {
    let mut magic=[0;8];input.read_exact(&mut magic)?;
    if &magic!=b"GATEIR1\n" && &magic!=b"GATEIR2\n" {return Err(invalid("wrong gate IR version"));}
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
