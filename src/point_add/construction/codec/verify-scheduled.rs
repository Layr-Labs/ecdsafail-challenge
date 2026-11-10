#[path="decoder.rs"]mod decoder;
#[path="schedule.rs"]mod schedule;
use std::{env,fs::{self,File},io::{self,Read,Write,Seek,SeekFrom}};
use schedule::RecordTarget;
struct Target<W:Write>{source:File,bytes:Vec<u8>,first:usize,count:usize,total:usize,out:W}
impl<W:Write> RecordTarget for Target<W>{
    fn read_prior(&mut self,i:usize)->[u16;4]{
        if i<self.first||i-self.first>=self.count{
            self.first=(i/65536)*65536;self.count=65536.min(self.total-self.first);
            self.source.seek(SeekFrom::Start((self.first as u64)*8)).unwrap();
            self.source.read_exact(&mut self.bytes[..8*self.count]).unwrap();
        }
        let start=(i-self.first)*8;let mut row=[0;4];
        for j in 0..4{row[j]=u16::from_le_bytes([self.bytes[start+2*j],self.bytes[start+2*j+1]]);}row
    }
    fn append(&mut self,r:[u16;4]){let mut data=[0;8];for j in 0..4{data[2*j..2*j+2].copy_from_slice(&r[j].to_le_bytes());}self.out.write_all(&data).unwrap();}
}
fn main()->io::Result<()>{
    let a:Vec<_>=env::args().collect();let source=File::open(&a[1])?;let len=source.metadata()?.len();
    let plan=fs::read(&a[2])?;let stdout=io::stdout();
    let mut target=Target{source,bytes:vec![0;8*65536],first:0,count:0,total:(len/8)as usize,out:io::BufWriter::with_capacity(1024*1024,stdout.lock())};
    let stdin=io::stdin();let n=schedule::expand(stdin.lock(),&plan,&mut target)?;
    target.out.flush()?;eprintln!("expanded {} complete records",n);Ok(())
}
