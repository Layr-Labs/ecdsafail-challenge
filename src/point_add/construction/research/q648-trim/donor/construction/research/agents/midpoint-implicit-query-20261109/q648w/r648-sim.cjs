// Oracle sim for THEIR regen (optionally with ledger's TstRelay stage-4 edit, TR=4). Reuses our sim.cjs cases/oracle.
const S='/Users/akashbalasubramani/Desktop/ecdsafail-649rg/src/point_add/construction/research/agents/midpoint-implicit-query-20261109/q650/regen/';
const {cases}=require(S+'sim.cjs');const {load,EDITS}=require('./r648-load.cjs');
const B=load(EDITS);const n=128,Pp=(1n<<256n)-(1n<<32n)-977n;
function rng(seed){let s=BigInt(seed)|1n;return ()=>{s^=s<<13n;s&=(1n<<64n)-1n;s^=s>>7n;s^=s<<17n;s&=(1n<<64n)-1n;return s;};}
function rand256(g){let x=0n;for(let i=0;i<4;i++)x=(x<<64n)|g();return x;}
function run(cs,W,seed){const NW=1024,Sx=new Uint32Array(NW*W),lanes=32*W;const g=rng(seed*977+5);const Y=[];
  const put=(wire,lane,bit)=>{if(bit)Sx[wire*W+(lane>>5)]|=1<<(lane&31);};const get=(wire,lane)=>(Sx[wire*W+(lane>>5)]>>>(lane&31))&1;
  for(let l=0;l<lanes;l++){const c=cs[l%cs.length];const y=rand256(g);Y.push(y);for(let i=0;i<n;i++){put(129-i,l,Number((c.r>>BigInt(i))&1n));put(259-i,l,Number((c.v>>BigInt(i))&1n));}for(let i=0;i<256;i++)put(389+i,l,Number((y>>BigInt(i))&1n));}
  for(let w=0;w<W;w++)Sx[645*W+w]=0xffffffff;
  const readNum=(base,step,len,l)=>{let x=0n;for(let i=len;i--;)x=(x<<1n)|BigInt(get(base+step*i,l));return x;};
  let ops=0;const touch=new Map();let st=-1;globalThis.__rgStage=(i)=>{st=i;};
  B.emitRegenerateSparse(chunk=>{ops+=chunk.length;for(let k=0;k<chunk.length;k++){const z=chunk[k],a=z>>>20,b=(z>>>10)&1023,t=(z&1023)*W;
    for(const q of [a,b,z&1023])if(q!==1023){let m=touch.get(st);if(!m)touch.set(st,m=new Set());m.add(q);}
    if(a===1023){for(let w=0;w<W;w++)Sx[t+w]^=0xffffffff;}else if(b===1023){const A=a*W;for(let w=0;w<W;w++)Sx[t+w]^=Sx[A+w];}else{const A=a*W,B2=b*W;for(let w=0;w<W;w++)Sx[t+w]^=Sx[A+w]&Sx[B2+w];}}},false);
  const data=new Set();for(let i=2;i<130;i++)data.add(i);for(let i=132;i<260;i++)data.add(i);for(let i=260;i<388;i++)data.add(i);for(let i=389;i<646;i++)data.add(i);
  let bad=0;const dirty=new Map();
  for(let l=0;l<lanes;l++){const c=cs[l%cs.length];const r=readNum(129,-1,n,l),v=readNum(259,-1,n,l),u=readNum(260,1,n,l),y=readNum(389,1,256,l);
    let ok=r===c.r&&v===c.v&&u===c.u&&y===Y[l];for(let wv=0;wv<NW;wv++)if(!data.has(wv)&&get(wv,l)){ok=false;dirty.set(wv,(dirty.get(wv)||0)+1);}if(!ok)bad++;}
  const helpers=[0,1,130,131,388,646,647,648,649,650,651];
  const tw=[...touch].map(([i,set])=>i+':'+helpers.filter(q=>set.has(q)).join(','));
  return {lanes,bad,ops,dirty:[...dirty].slice(0,8),touched:tw};}
module.exports={runCases:run};
if(require.main===module){const [N='256',mode='mix',seed='1',W='8']=process.argv.slice(2);
console.log(JSON.stringify(run(cases(+N,+seed,mode),+W,+seed)));}
