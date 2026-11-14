'use strict';
const assert=require('node:assert/strict');
const path=require('node:path');

// For q=1+2Q and g=1+2G the old minterm table toggles bit 3 XOR bit 2
// of q/g in Z/16. Compute its multilinear polynomial on the existing bits.
function table(gBits) {
    const n=gBits+3,gMask=(1<<gBits)-1,values=new Uint8Array(1<<n);
    for(let i=0;i<values.length;i++){
        const g=1+2*(i&gMask),q=1+2*(i>>gBits);
        let inv=1;while(inv*g%16!==1)inv+=2;
        const j=q*inv%16;values[i]=((j>>2)^(j>>3))&1;
    }
    for(let j=0;j<n;j++)for(let i=0;i<values.length;i++)if(i>>j&1)values[i]^=values[i^(1<<j)];
    const terms=[];for(let i=0;i<values.length;i++)if(values[i])terms.push(i);
    return terms;
}
const tables=Array.from({length:4},(_,j)=>table(j));

function transform(s) {
    const start=s.indexOf('function D14ParkCount('),end=s.indexOf('\n}',start);
    assert(start>=0&&end>start);
    let f=s.slice(start,end);
    const first="  put(D14Raw([...cs,U[1]],[...ps,true],U[3],loan));\n  for(let odd=1;odd<16;odd+=2){";
    const last='  }\n }\n put([[port,Q[3]]]);';
    const a=f.indexOf(first),b=f.indexOf(last,a);assert(a>=0&&b>a,'four-bit winding lookup');
    const code=`  const gs=L.slice(k+1,Math.min(k+4,size)),qs=Q.slice(k+1,k+4),word=gs.concat(qs);
  const avoid=new Set([...cs,...word,U[1],U[3],port]);
  const bit=loan.find(q=>!avoid.has(q));if(bit===undefined)throw Error('D14 winding loan');
  const pool=loan.filter(q=>q!==bit),terms=${JSON.stringify(tables)}[gs.length];
  const xor=()=>{put([[bit,U[1],U[3]]]);for(const mask of terms){
    const controls=[bit,...word.filter((_,j)=>mask>>j&1)];
    put(D14Raw(controls,controls.map(()=>true),U[3],pool));
  }};
  const p=D14Raw(cs,ps,bit,pool);
  xor();put(p);xor();put([...p].reverse());
`;
    f=f.slice(0,a)+code+f.slice(b+'  }\n'.length);
    return s.slice(0,start)+f+s.slice(end);
}

function install(owner) {
    const id=require.resolve(path.join(owner,'i9-divide-complete-source.cjs'));
    const old=require(id);
    require.cache[id].exports={...old,applySource(s){return transform(old.applySource(s));}};
}
function install648(owner){
    const file=require.resolve(path.join(owner,'d648-p-c2w.cjs')),old=require(file);
    require.cache[file].exports=s=>transform(old(s));
}
module.exports={tables,transform,install,install648};
