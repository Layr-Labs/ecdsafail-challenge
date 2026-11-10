'use strict';
// q650 history.regenerate (ours). Evicts logical 388 (park's Jtop, the top quotient bit of R/V).
// Installed by p-regen650.js into the 651-patched q654-next/regen.cjs scope; receives its classes.
//
// Helper sites after eviction: 0,1,130,131,646,647,648,649,650 (nine). Window contracts:
//  park      : yq on M's normalized known-one top (constant-one M-top arithmetic, as 652's scale);
//              Jtop (quotient top bit b) on 130, the released yq; b moved 130<->650 at the park edge.
//  walk6     : Signed(n,4): tags 647..649 + row-top host; fire T[0] as in 651. 650 carries b.
//  scale     : tags 647,648,649,131,646,0,1; sign on 130 (651 mv); b stays on 650. Three exact paths,
//              each the 651 scale core (TopHost arithmetic, carry-free) with one extra control:
//               A0  clz(V)=0, control M[127]; unnormalized 128-bit; f=647, yq=648 (clean tags).
//               A1  clz(V)=1, control 649=[!M127 & M126]; unnormalized 127-bit registers; f=647, yq=648.
//               B   clz(V)>=2: normalize (uncontrolled); F=[clz>=2] on M's known-one top; under F move
//                   b->M[0], sign->M[1] (normalized low zeros); core with M[0],M[1] constant 0, M top
//                   constant 1, f=650, yq=130, sign=M[1]; undo.
//  walk      : Signed(n,3): tags 647,648 + row-top host; fire 649. 650 carries b.
const n=128,E=645,NONE=1023;
module.exports=function({UnitPark,Terminal,terms,Signed,TopHost,UnitWalk}){
  const p=(1n<<256n)-(1n<<32n)-977n;
  // ---------- exact extra-control wrapper over packed NCT gates ----------
  function mcx(out,c,t,pool){
    if(new Set(c).size!==c.length||c.includes(t))throw Error('q650 control alias');
    const raw=(a,b,z)=>out.push(((a<0?NONE:a)<<20)|((b<0?NONE:b)<<10)|z);
    if(c.length===0){raw(-1,-1,t);return;}
    if(c.length===1){raw(c[0],-1,t);return;}
    if(c.length===2){raw(c[0],c[1],t);return;}
    const k=c.length,w=[];
    for(const q of pool){if(w.length===k-2)break;if(q!==t&&!c.includes(q))w.push(q);}
    if(w.length<k-2)throw Error('q650 borrow');
    // Same dirty-borrow ladder as UnitWalk.op: value-independent, restores every borrowed wire.
    for(let s=0;s<2;s++){if(s===0)raw(c[0],c[1],w[0]);for(let i=1;i<k-2;i++)raw(c[i+1],w[i-1],w[i]);raw(c[k-1],w[k-3],t);for(let i=k-3;i>=1;i--)raw(c[i+1],w[i-1],w[i]);if(s===0)raw(c[0],c[1],w[0]);}
  }
  const POOL=Array.from({length:128},(_,i)=>517+i); // Y[128..255], dirty loans (restored)
  function controlled(gates,ctl){
    const out=[];
    for(const x of gates){const a=x>>>20,b=(x>>>10)&1023,t=x&1023,c=ctl.slice();
      if(a!==NONE&&a!==E)c.push(a);if(b!==NONE&&b!==E)c.push(b);mcx(out,c,t,POOL);}
    return out;
  }
  // Wrap blocks of generator `inst` so their gates land in the stage generator `host`, with extra controls.
  const wrap=(host,inst,blocks,ctl)=>blocks.map(bl=>({fn:()=>{inst.g=[];
    if(ctl.length&&inst instanceof Core&&process.env.Q650_WRAP!=='1'){inst.X=ctl[0];inst.ctl=true;bl.fn();inst.ctl=false;if(bl.rev)inst.g.reverse();if(globalThis.__q650seg)globalThis.__q650seg(ctl[0],inst.g);for(const z of inst.g)host.g.push(z);return;}
    bl.fn();if(bl.rev)inst.g.reverse();if(globalThis.__q650blk)globalThis.__q650blk(inst,inst.g);
    const gs=ctl.length?controlled(inst.g,ctl):inst.g;for(const z of gs)host.g.push(z);},rev:false}));
  // ---------- park with yq on the normalized top of M ----------
  class ParkTop extends UnitPark{
    add(c,a,b,unused,h){return TopHost.prototype.add.call(this,c,a,b,unused,h);}
    lt(c,a,b,h){Signed.prototype.lt.call(this,c,a,b,h);}
    // place=true: regen-entry park. Before denormalization (tags = clz) b moves 130 -> T[127-clz] for clz<=126;
    // afterwards 130 <-> 647 (V=1 keeps b on 647 through walk6). place=false: regen-exit park, b arrives on 650.
    parking(place){const b=super.parking(),k=this.tag.length,x=()=>this.raw(-1,-1,this.M[this.m-1]);
      const mid=b.slice(k,-k),put=[];
      if(place)for(let c=0;c<this.m-1;c++)put.push({fn:()=>{const neg=this.tag.filter((q,j)=>!((c>>j)&1));
        for(const q of neg)this.raw(-1,-1,q);const t=this.T[this.m-1-c];
        this.op(this.tag.concat(this.Jtop),t);this.op(this.tag.concat(t),this.Jtop);
        for(const q of neg)this.raw(-1,-1,q);},rev:false});
      return [...b.slice(0,k),{fn:x,rev:false},...mid,...put,{fn:x,rev:false},...b.slice(-k),
        {fn:()=>this.swap([],this.Jtop,place?647:650),rev:false}];}
  }
  // ---------- scale core with configurable registers and constant M bits ----------
  class Core extends Terminal{
    constructor(cfg){super(n,true,terms(p));Object.assign(this,cfg);}
    add(c,a,b,unused,h){
      if(a!==this.M){Signed.prototype.add.call(this,c,a,b,0,h);return;}
      // M bits below Moff are constant zero; M's top is a constant one (its wire is never read or written).
      // With this.lo=[w0,w1] (Moff 0): M's two low bits are read from w0,w1 and every gate touching them is
      // conditioned on this.G; with G=0 those gates vanish, which equals low bits 0 (checked by lowzero.cjs).
      const Mw=this.lo?[...this.lo,...a.slice(2)]:a;
      const A=Mw.slice(this.Moff),B=b.slice(this.Moff),lo=A.slice(0,-1),bl=B.slice(0,-1),z=B.at(-1),g0=this.g.length;
      if(h!==null)this.op(c.concat(z),h);
      Signed.prototype.add.call(this,c,lo,bl,0,z);
      this.op(c,z);
      if(h!==null){this.raw(-1,-1,z);Signed.prototype.lt.call(this,c.concat(z),lo,bl,h);this.raw(-1,-1,z);}
      if(this.lo&&process.env.Q650_NOMASK!=='1'){const tail=this.g.splice(g0),w=this.lo;
        for(const x of tail){const xa=x>>>20,xb=(x>>>10)&1023,xt=x&1023;
          if(!w.includes(xa)&&!w.includes(xb)&&!w.includes(xt)){this.g.push(x);continue;}
          const cc=[this.G];if(xa!==NONE&&xa!==E)cc.push(xa);if(xb!==NONE&&xb!==E)cc.push(xb);mcx(this.g,cc,xt,POOL);}}
    }
    lt(c,a,b,h){Signed.prototype.lt.call(this,c,a,b,h);}
    // Path control X joins every op() control list; raw() gates are the restoring ladders/conjugations around them.
    op(c,z){const cc=c.filter(q=>q!==E);if(this.X!=null&&this.ctl)cc.unshift(this.X);return UnitWalk.prototype.op.call(this,cc,z);}
    orient(sign=this.sg){return TopHost.prototype.orient.call(this,sign);}
    all(){return Terminal.prototype.plan.call(this);}
    core(){const k=this.tag.length;return this.all().slice(k,-k);}
  }
  function emit(sink,erase=false){
    const {SignedAF}=require('./walkaf.cjs');
    const walk=new SignedAF(n,4),walk6=new SignedAF(n,7),park=new ParkTop(n,false,[]),scale=new TopHost(n,true,terms(p));
    park.f=walk.R[1];park.tag[6]=walk.L[1];park.tag[5]=walk.L[0];park.tag[4]=walk.sign;park.yq=park.M[n-1];park.Jtop=walk.R[0];
    const mv=()=>{scale.raw(walk.sign,-1,walk.R[0]);scale.raw(walk.R[0],-1,walk.sign);scale.raw(-1,-1,walk.L[0]);};
    walk.aux=653;walk.tst=walk.R[n+1];walk6.aux=653;walk6.tst=walk6.R[n+1]; // aux-free walks: aux never emitted
    walk6.fire=scale.T[0];walk6.tag[4]=scale.T[1];walk6.tag[5]=walk6.L[n+1];walk.tag[3]=651;walk.fire=650;
    const shifts6={fn:()=>{for(const bank of [walk6.L,walk6.R])for(let j=n;j>=1;j--)walk6.swap([],bank[j],bank[j+1]);}};
    const exchange={fn:()=>{for(let i=0;i<n+2;i++)walk.swap([],walk.L[i],walk.R[n+1-i]);}};
    const shifts={fn:()=>{for(const bank of [walk.L,walk.R])for(let j=n;j>=1;j--)walk.swap([],bank[j],bank[j+1]);}};
    // scale paths
    const S=scale.S,T=scale.T,D=scale.D,M=scale.M,sg=walk.R[0],tags=[647,648,649,131,646,0,1];
    // One core for every clz. After the 7-tag normalization, F=[clz>=2] is put on M's known-one top and flipped to
    // G=[clz<=1]. Under G, M's two low bits move to tag wires 0,1 (tags 5,6: zero when clz<=1); now M[0],M[1] are
    // zero in every case and host b and the sign. The core reads M's low bits from wires 0,1 under G.
    const Bc=new Core({S,T,D,M,Moff:0,f:650,yq:sg,sg:M[1],tag:tags.slice(),lo:[0,1],G:M[127]});
    const Ftop=M[127],k=tags.length,Ball=Bc.all();
    const fB=()=>scale.zer([],tags.slice(1),Ftop); // M_norm top is 1; it becomes [clz>=2]
    const xG=()=>scale.raw(-1,-1,Ftop);
    const inv=bl=>bl.slice().reverse().map(x=>({fn:x.fn,rev:!x.rev}));
    const T127=T[127],move=(a,b)=>()=>{scale.raw(a,-1,b);scale.raw(b,-1,a);}; // a->b when b is clean
    const b0=()=>scale.swap([],647,T[0]); // V=1: b 647 -> T[0] = T[127-clz]; otherwise both clean
    const lowG=()=>{scale.swap([Ftop],M[0],0);scale.swap([Ftop],M[1],1);};
    const hostIn=()=>{move(T127,M[0])();move(sg,M[1])();},hostOut=()=>{move(M[0],650)();move(M[1],sg)();};
    const Lr=[{fn:mv},{fn:b0},
      ...wrap(scale,Bc,Ball.slice(0,k),[]),{fn:fB},{fn:xG},{fn:lowG},{fn:hostIn},
      ...wrap(scale,Bc,inv(Ball.slice(k,-k)),[]),
      {fn:hostOut},{fn:lowG},{fn:xG},{fn:fB},...wrap(scale,Bc,Ball.slice(-k),[]),
      {fn:mv,rev:true}];
    const scaleBlocks=inv(Lr);
    // walk6 runs with six tags; tag[4] is T[1], zero below the parked quotient whenever V>=4 (and walk6-transparent
    // for V=1). For V in {2,3} the parked top bit sits on T[1]: those three bank states are remapped to the V=1 entry
    // state (id on 648/649, transparent there), and after walk6 rewritten to their own walk6 outputs (simulated here).
    const smallV=[[2n,1n],[3n,1n],[3n,2n]],code=[[648],[649],[648,649]],idw=[648,649];
    const entry=(v,r)=>{const st=new Uint8Array(1024);for(let i=0;i<n;i++){st[129-i]=Number((r>>BigInt(i))&1n);st[259-i]=Number((v>>BigInt(i))&1n);}
      for(let i=0;i<n+2;i++){const x=i,y=259-i,t=st[x];st[x]=st[y];st[y]=t;}return st;};
    const B=[entry(1n,0n),...smallV.map(([v,r])=>entry(v,r))];
    const bankW=Array.from({length:260},(_,i)=>i),predW=[...bankW,646,647,650,T[0]];
    const POOL2=[...Array.from({length:256},(_,i)=>389+i),...T.slice(3,128)];
    const lit=(g,ws,st,extra,t)=>{const neg=ws.filter(q=>!st[q]);for(const q of neg)g.raw(-1,-1,q);const o=[];mcx(o,[...ws,...extra],t,POOL2);for(const z of o)g.g.push(z);for(const q of neg)g.raw(-1,-1,q);};
    const isId=(g,k,t)=>{const st=new Uint8Array(1024);for(const q of code[k])st[q]=1;lit(g,idw,st,[],t);};
    const pre={fn:()=>{for(let k=0;k<3;k++)for(const w of code[k])lit(walk6,bankW,B[k+1],[],w);
      for(let k=0;k<3;k++)for(let q=0;q<1024;q++)if(B[k+1][q]!==B[0][q])isId(walk6,k,q);}};
    // 4-lane simulation of walk6 from the four entry states (helpers, T and dirty pool clean) gives the exit states.
    const sim=new Uint8Array(1024*4);for(let l=0;l<4;l++){const st=l?B[l]:B[0];for(let q=0;q<1024;q++)sim[q*4+l]=st[q];}sim[645*4]=sim[645*4+1]=sim[645*4+2]=sim[645*4+3]=1;
    const simGates=gs=>{for(const z of gs){const a=z>>>20,b=(z>>>10)&1023,t=z&1023;for(let l=0;l<4;l++){const c=(a===1023||sim[a*4+l])&&(b===1023||sim[b*4+l]);if(c)sim[t*4+l]^=1;}}};
    const post={fn:()=>{const O=[0,1,2,3].map(l=>{const st=new Uint8Array(1024);for(let q=0;q<1024;q++)st[q]=sim[q*4+l];return st;});
      for(let k=0;k<3;k++)for(const q of predW)if(O[k+1][q]!==O[0][q])isId(walk6,k,q);
      for(let k=0;k<3;k++)for(const w of code[k])lit(walk6,predW,O[k+1],[],w);}};
    // stage-4 walk: b rides on L[129] (idle in the aux-free walk) while 650 is the walk's fire.
    const swapB={fn:()=>walk.swap([],650,walk.L[n+1])};
    const stages=[[park,park.parking(false),false],[walk,[exchange],false],[walk,[swapB].concat(walk.plan(),[swapB,shifts]),false],
      [scale,scaleBlocks,false],[walk6,[pre].concat(walk6.plan(),[shifts6,post]),true],[walk,[exchange],true],[park,park.parking(true),true]];
    if(!erase)stages.reverse();
    let si=0;
    for(const [g,blocks,back] of stages){
      if(globalThis.__rgStage)globalThis.__rgStage(si++,g===walk?'walk':g===park?'park':g===scale?'scale':'walk6',blocks.length);
      const rev=back!==!erase;if(rev)blocks.reverse();
      for(const block of blocks){
        g.g=[];block.fn();if(rev!==!!block.rev)g.g.reverse();
        const port=q=>{if((g===walk||g===walk6)&&q===g.tag.at(-1)){if(block.topPort==null)throw Error('height outside walk');q=block.topPort;}
          if(q===388||q>=651&&q<=656)throw Error('unused regeneration site '+q);return q;};
        for(let i=0;i<g.g.length;i++){
          const x=g.g[i],a=port(x>>>20&1023),b=port(x>>>10&1023),t=port(x&1023);
          if(t===645||a===t||b===t||a!==1023&&a===b)throw Error('bad physical history gate');
          g.g[i]=(a<<20)|(b<<10)|t;
        }
        if(g===walk6&&block!==pre&&block!==post)simGates(g.g);
        sink(g.g);
      }
    }
  }
  return {emit,ParkTop,Core,controlled};
};
