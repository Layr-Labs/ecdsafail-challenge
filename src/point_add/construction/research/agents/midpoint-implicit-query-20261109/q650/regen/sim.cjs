'use strict';
// Bit-sliced simulator of history.regenerate on logical wires.
// Inputs: Euclid midpoint states (r_j,t_j) of (p,x); R at logical 129-i, V at 259-i, U (260+i)=0, Y (389+i) random passenger.
// Checks: R,V,Y unchanged; U = (v==1?0:p*inv(r mod v,v) mod v); every non-data logical wire zero at exit.
const {loadRegen}=require('./load.cjs');
const p=(1n<<256n)-(1n<<32n)-977n,n=128;
function rng(seed){let s=BigInt(seed)|1n;return ()=>{s^=s<<13n;s&=(1n<<64n)-1n;s^=s>>7n;s^=s<<17n;s&=(1n<<64n)-1n;return s;};}
function rand256(g){let x=0n;for(let i=0;i<4;i++)x=(x<<64n)|g();return x;}
const egcd=(a,b)=>{let [r0,r1,s0,s1]=[a,b,1n,0n];while(r1){const q=r0/r1;[r0,r1]=[r1,r0-q*r1];[s0,s1]=[s1,s0-q*s1];}return [r0,s0];};
const inv=(a,m)=>{const [g,s]=egcd(((a%m)+m)%m,m);if(g!==1n)throw Error('not inv');return ((s%m)+m)%m;};
function midpoint(x){let r0=p,r1=x,t0=0n,t1=1n;while(r1>=(1n<<128n)){const q=r0/r1;[r0,r1]=[r1,r0-q*r1];[t0,t1]=[t1,t0+q*t1];}return {r:r1,v:t1,u:t0,rp:r0};}
function cases(N,seed,mode){const g=rng(seed),out=[];
  for(let k=0;k<N;k++){
    let c;
    if(mode==='rand'||(mode==='mix'&&k%4!==0)){const x=rand256(g)%(p-1n)+1n;c=midpoint(x);}
    else{ // crafted: small x (v=1), and x chosen so v has given bit length
      const sel=Number(g()%6n);
      if(sel===0){const x=(rand256(g)>>BigInt(128+Number(g()%128n)))+1n;c=midpoint(x);} // v=1
      else{const bits=Number(g()%128n)+1;let best=null;for(let t=0;t<64;t++){const x=rand256(g)%(p-1n)+1n;const m=midpoint(x);if(best===null||Math.abs(m.v.toString(2).length-bits)<Math.abs(best.v.toString(2).length-bits))best=m;}c=best;
        if(sel===1){ // synthesize coprime (r,v) directly: v of given bits, r random <2^128, coprime -> u from formula
          const v=(rand256(g)>>BigInt(256-bits))|(1n<<BigInt(bits-1));let r=rand256(g)>>128n;while(egcd(r,v)[0]!==1n)r++;c={r,v,u:v===1n?0n:p*inv(r%v,v)%v,syn:1};}
      }
    }
    if(c.u!==(c.v===1n?0n:p*inv(c.r%c.v,c.v)%c.v))throw Error('oracle mismatch');
    out.push(c);}
  return out;}
function run(patch,cs,{W=8,snap=null,seed=7}={}){
  const {emitRegenerateSparse}=loadRegen(patch);
  const NW=1024,S=new Uint32Array(NW*W),lanes=32*W;
  const g=rng(seed*977+5);const Y=[];
  const put=(wire,lane,bit)=>{if(bit)S[wire*W+(lane>>5)]|=1<<(lane&31);};
  const get=(wire,lane)=>(S[wire*W+(lane>>5)]>>>(lane&31))&1;
  for(let l=0;l<lanes;l++){const c=cs[l%cs.length];const y=rand256(g);Y.push(y);
    for(let i=0;i<n;i++){put(129-i,l,Number((c.r>>BigInt(i))&1n));put(259-i,l,Number((c.v>>BigInt(i))&1n));}
    for(let i=0;i<256;i++)put(389+i,l,Number((y>>BigInt(i))&1n));}
  for(let w=0;w<W;w++)S[645*W+w]=0xffffffff;
  const readNum=(base,step,len,l)=>{let x=0n;for(let i=len;i--;)x=(x<<1n)|BigInt(get(base+step*i,l));return x;};
  let cur=-1;globalThis.__rgStage=(i,label)=>{if(snap)snap(i,label,S,W,get);cur=i;};
  let ops=0;
  emitRegenerateSparse(chunk=>{ops+=chunk.length;for(let k=0;k<chunk.length;k++){const z=chunk[k],a=z>>>20,b=(z>>>10)&1023,t=(z&1023)*W;
    if(a===1023){for(let w=0;w<W;w++)S[t+w]^=0xffffffff;}
    else if(b===1023){const A=a*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w];}
    else{const A=a*W,B=b*W;for(let w=0;w<W;w++)S[t+w]^=S[A+w]&S[B+w];}}},false);
  if(snap)snap(7,'exit',S,W,get);
  const data=new Set();for(let i=2;i<130;i++)data.add(i);for(let i=132;i<260;i++)data.add(i);for(let i=260;i<388;i++)data.add(i);for(let i=389;i<645;i++)data.add(i);data.add(645);
  let bad=0;const dirty=new Map();const fails=[];
  for(let l=0;l<lanes;l++){const c=cs[l%cs.length];
    const r=readNum(129,-1,n,l),v=readNum(259,-1,n,l),u=readNum(260,1,n,l),y=readNum(389,1,256,l);
    let ok=r===c.r&&v===c.v&&u===c.u&&y===Y[l];
    for(let wv=0;wv<NW;wv++)if(!data.has(wv)&&get(wv,l)){ok=false;dirty.set(wv,(dirty.get(wv)||0)+1);}
    if(!ok){bad++;if(fails.length<5)fails.push({lane:l,r:c.r.toString(16),v:c.v.toString(16),u:c.u.toString(16),got:u.toString(16)});}}
  return {lanes,bad,ops,dirty:[...dirty],fails};
}
module.exports={run,cases,midpoint,p};
if(require.main===module){
  const [patch,N='256',mode='mix',seed='1',W='8']=process.argv.slice(2);
  const cs=cases(+N,+seed,mode);const t=Date.now();
  const res=run(patch==='-'?null:patch,cs,{W:+W,seed:+seed});
  console.log(JSON.stringify(res),'ms',Date.now()-t);
}
