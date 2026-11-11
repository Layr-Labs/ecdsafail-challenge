#[path="decoder.rs"] mod decoder;
use std::io::{self,Write};
fn main()->io::Result<()> {
    let stdin=io::stdin();let stdout=io::stdout();
    let mut out=io::BufWriter::with_capacity(1024*1024,stdout.lock());
    let mut io_error=None;
    let n=decoder::decode_records(stdin.lock(),|row|{
        if io_error.is_some(){return;}
        let bytes=[row[0].to_le_bytes(),row[1].to_le_bytes(),row[2].to_le_bytes(),row[3].to_le_bytes()];
        let packed=[bytes[0][0],bytes[0][1],bytes[1][0],bytes[1][1],bytes[2][0],bytes[2][1],bytes[3][0],bytes[3][1]];
        if let Err(e)=out.write_all(&packed){io_error=Some(e);}
    })?;
    if let Some(e)=io_error{return Err(e);}out.flush()?;eprintln!("decoded {} trace records",n);Ok(())
}
