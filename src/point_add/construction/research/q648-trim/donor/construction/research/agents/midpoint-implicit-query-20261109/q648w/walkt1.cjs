'use strict';
// TstRelay1 (ledger, q648): a sector walk on ONE real tag wire Z + fire F (+ row-top port, + the walk's own zeros).
// For the divide inner walk at 7 sites (evict: 641 tag, 642 fire, no 643). Same contract as D2Canonical (opts.flat).
//  * select: z ^= [A>r] xor [A==1 & r==0]  (== [A>=2 & A>r]); no temp.
//  * balance block: qa on L[m] (u's top: zero at row start on every lane, since the block deposits cp there and the
//    reset reads it back); the cofactor comparison drops u's known-zero top: [v > ~u] = v_top & [v_low > ~u_low];
//    cp on Z.  Sector-start match result on Z.  Untagged sigma=1 sector: tst on Z.
//  * sectors per row: sigma=1 (untagged); 2-bit TstFree sectors (row top + Z) sigma in [b+2,b+3], b=0,2,4;
//    1-relay sector (row top, relayed bit on r[1]/r[0], Z) sigma in [8,11] at base 4;
//    2-relay sectors (row top, two relayed bits on r[2],r[3] -> r[0],r[1], Z) sigma in [b+8,b+15], b=4,12,20,...
//    Real part of s is Z (nonzero for every s in each tagged sector), so unconditioned eq toggles are safe.
const {TstRelay,Base}=require('./walktf.cjs');
const P=require('../q653-next/parts.cjs');
class TstRelay1 extends TstRelay{
  constructor(n,Z,fire,opts={}){const tags=Array.isArray(Z)?Z.slice():[Z];super(n,tags.length>=2?tags:[tags[0],tags[0]],fire,Object.assign({mini0:false},opts));this.tagR=tags;this.tag=tags.slice();this.Z=tags[0];this.flatOff=opts.flat===false;this.maxRelay=opts.maxRelay==null?2:opts.maxRelay;this.relayAt=opts.relayAt||null;}
  // Greedy cover of sigma in [1,m-1]: sigma=1 untagged; then the widest admissible kind at each point:
  //  high2 (2 relayed bits, s in [8, 2^(k+3)-1], base>=4), high1 (1 relayed, s in [4, 2^(k+2)-1], base>=4),
  //  low (no relay, s in [2, 2^(k+1)-1]); k = number of real tags. k=1 reproduces the original TstRelay1 layout.
  sectors(m){const out=[],k=this.tagR.length,MJ=this.relayAt&&this.relayAt[m]!=null?this.relayAt[m]:this.maxRelay;
    if(m-1>=1)out.push({base:1,lo:1,hi:1,kind:'mini'});
    for(let cur=2;cur<=m-1;){let sp=null;
      for(let J=MJ;J>=3&&!sp;J--)if(cur-(1<<(J+1))>=J+2)sp={base:cur-(1<<(J+1)),lo:cur,hi:cur-(1<<(J+1))+(1<<(k+J+1))-1,kind:'highJ',J};
      if(sp);else if(MJ>=2&&cur-8>=4)sp={base:cur-8,lo:cur,hi:cur-8+(1<<(k+3))-1,kind:'high2'};
      else if(MJ>=1&&cur-4>=4)sp={base:cur-4,lo:cur,hi:cur-4+(1<<(k+2))-1,kind:'high1'};
      else sp={base:cur-2,lo:cur,hi:cur-2+(1<<(k+1))-1,kind:'low'};
      sp.hi=Math.min(m-1,sp.hi);out.push(sp);cur=sp.hi+1;}
    if(out.length===0)out.push({base:0,lo:0,hi:m-1,kind:'mini'});
    if(out.length===1&&out[0].kind==='mini'&&m-1<=1){out[0].lo=0;out[0].hi=m-1;}
    return out.sort((a,b)=>b.lo-a.lo);}
  plan(){
    const n=this.n,L=this.L,R=this.R,F=this.fire,c=[F],all=[],Z=this.Z;
    let K=-1,BASE=-1;const blk=(fn,rev=false)=>({fn,rev,k:K,base:BASE});const one=fn=>all.push(blk(fn));
    const X=w=>this.raw(-1,-1,w);
    const dd=(Alow,B,h,e)=>{for(const z of (this.ddFn||P.dirtyDigit)(Alow,B,h,e,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z[z.length-1]);};
    const rot=(ar,w,controls,dir,base,tg)=>{if(base)ar.push(blk(()=>this.rot(controls,w,dir*base)));
      for(let j=0;j<tg.length;j++){const s=1<<j;if(s>=w.length)break;ar.push(blk(()=>this.rot(controls.concat(tg[j]),w,dir*s)));}};
    const norm=(ar,w,controls,base,tg)=>{if(base)ar.push(blk(()=>this.rot(controls,w,base)));
      for(let j=tg.length;j--;){const s=1<<j;if(s>=w.length)continue;ar.push(blk(()=>{this.zer(controls,w.slice(w.length-s),tg[j]);this.rot(controls.concat(tg[j]),w,s);}));}};
    const normH=(ar,w,controls,base,tg)=>{ar.push(blk(()=>this.rot(controls,w,base)));const ws=w.slice(base);
      for(let j=tg.length;j--;){const s=1<<j;if(s>=ws.length)continue;ar.push(blk(()=>{this.zer(controls,ws.slice(ws.length-s),tg[j]);this.rot(controls.concat(tg[j]),ws,s);}));}};
    const co=(a,t)=>Array.from({length:t},(_,i)=>a[n-i]);
    const W=L.slice(0,n),S=R.slice(0,n);
    one(()=>{const high=S[n-1];this.op([high],this.sign);X(high);this.lt([high],S.slice(0,-1),W.slice(1),this.sign);X(high);});
    one(()=>{const cc=[this.sign];for(const z of W)X(z);this.add(cc,W,S,0,null);for(const z of W)X(z);for(const z of S)this.op(cc,z);});
    one(()=>X(R[n]));
    for(let k=0;k<n;k++){K=k;BASE=-1;
      const t=k+1,m=n-k,A=L.slice(0,m),r=R.slice(0,m),u=co(L,t),v=co(R,t);
      // temp-free select: z ^= [A>r] ^ [A==1 & r==0]
      const RED=!!this.reduced,CL=RED,tmp2=CL?this.tagR[1]:null;
      const select=CL?(z=>{const large=()=>{this.zer([],RED?r:A.slice(1),tmp2);X(tmp2);};large();this.lt([tmp2],A,r,z);this.reverse(large);})
        :(z=>{this.lt([],A,r,z);const lits=[...A,...r],neg=lits.filter(q=>q!==A[0]);for(const q of neg)X(q);this.mcx(lits,z);for(const q of neg)X(q);});
      if(CL&&k>0&&k<n-1){const qa=this.tagR[0],tp=this.tagR[1],cp=[tp]; // classic temps (needs >=2 real tags)
        one(()=>select(F));
        one(()=>{const qcond=()=>{this.op([r[m-1]],qa);X(r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),qa);X(r[m-1]);};
          qcond();this.op([F,qa],tp);for(const z of u)X(z);this.lt([F,qa],v,u,tp);for(const z of u)X(z);this.reverse(qcond);});
        one(()=>{this.reverse(()=>this.add(cp,r,A,null,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,null,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
        one(()=>this.op(RED?[F,L[n-k]]:[L[n-k]],tp));
        one(()=>select(F));
      }
      if(!CL&&k>0&&k<n-1){const qa=L[m],cp=[Z];
        one(()=>select(F));
        one(()=>{const qcond=()=>{this.op([r[m-1]],qa);X(r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),qa);X(r[m-1]);};
          qcond();this.op([F,qa],Z);
          const ul=u.slice(0,-1),vl=v.slice(0,-1);for(const z of ul)X(z);this.lt([F,qa,v[t-1]],vl,ul,Z);for(const z of ul)X(z);
          this.reverse(qcond);});
        one(()=>{this.reverse(()=>this.add(cp,r,A,null,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,null,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
        one(()=>this.op([L[n-k]],Z));
        one(()=>select(F));
      }
      for(const sp of this.sectors(m)){const {base,lo,hi,kind,J}=sp;BASE=base;
        const single=lo===0&&hi===m-1;
        const match=(controls,word,out)=>{this.zer(controls,word.slice(m-lo),out);if(hi+1<m)this.zer(controls,word.slice(m-hi-1),out);};
        if(single)one(()=>select(F));
        else one(()=>{select(F);match(c,r,Z);select(F);this.op([Z],F);this.op(c,Z);});
        one(()=>this.op(c,R[m]));
        const eqT=(i,tg)=>{if(i>=lo&&i<=hi){const q=i-base,neg=tg.filter((_,j)=>!(q>>j&1));for(const w of neg)X(w);this.mcx(tg,F);for(const w of neg)X(w);}};
        const body=(phases)=>{ // phases: {tgN, tgOf(i), hopsBefore(i), topDigit, topStep(i), topRest, hopBack, normFn, unrot}
        };
        if(kind==='highJ'){ // J relayed bits: start on r[2..J+1]; before step i (2<=i<=J+1) r[i]->r[i-2]; base>=J+2
          const RT=this.tagR,pos=(j,i)=>i>=j+2?r[j]:r[j+2];
          const tgAt=i=>[R[m],...Array.from({length:J},(_,j)=>pos(j,i)),...RT];
          const tgN=tgAt(0),tgS=tgAt(J+1);
          normH(all,r,c,base,tgN);
          one(()=>{this.op(c,r[m-1]);X(r[0]);dd(r.slice(base,m-1).concat(r[0]),A.slice(base),r[m-1],F);X(r[0]);});
          for(let i=0;i<hi;i++){
            if(i>=2&&i<=J+1)one(()=>this.swap([F],r[i],r[i-2]));
            const top=i===0?r[1]:i<=J+1?r[i-1]:r[J];
            one(()=>{eqT(i,tgAt(i));const en=[F],carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);
              const st=Math.max(i+1,base);X(top);dd(r.slice(st,m-1).concat(top),A.slice(st),carry,F);X(top);
              this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});}
          const rt=r[J];
          one(()=>eqT(hi,tgS));
          for(let i=hi-1;i>=0;i--)one(()=>{eqT(i+1,tgS);const en=[F];X(rt);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(rt),u,0,A[i]));X(rt);
            for(let j=t;j--;)this.swap(en,A[i],u[j]);});
          one(()=>{const carry=r[m-1];X(rt);this.reverse(()=>dd(v.slice(0,-1).concat(rt),u,carry,F));X(rt);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
          for(let i=J+1;i>=2;i--)one(()=>this.swap([F],r[i-2],r[i]));
          one(()=>this.rot(c,L.slice(m,n+1),-1));
          rot(all,L.slice(0,n+1),c,-1,base,tgN);
          const vv=[];normH(vv,r,c,base,tgN);for(let i=vv.length;i--;)all.push({fn:vv[i].fn,rev:!vv[i].rev,k:K,base:BASE});
        }else if(kind==='high1'||kind==='high2'){
          const two=kind==='high2';
          const RT=this.tagR;const tgN=two?[R[m],r[2],r[3],...RT]:[R[m],r[1],...RT];
          const tgS=two?[R[m],r[0],r[1],...RT]:[R[m],r[0],...RT];
          const tgAt=i=>two?(i<=1?tgN:i===2?[R[m],r[0],r[3],...RT]:tgS):(i===0?tgN:tgS);
          normH(all,r,c,base,tgN);
          one(()=>{this.op(c,r[m-1]);X(r[0]);dd(r.slice(base,m-1).concat(r[0]),A.slice(base),r[m-1],F);X(r[0]);});
          for(let i=0;i<hi;i++){
            if(!two&&i===1)one(()=>this.swap([F],r[1],r[0]));
            if(two&&i===2)one(()=>this.swap([F],r[2],r[0]));
            if(two&&i===3)one(()=>this.swap([F],r[3],r[1]));
            const top=two?(i===0?r[1]:i===1?r[0]:i===2?r[1]:r[2]):(i<=1?r[2]:r[1]);
            one(()=>{eqT(i,tgAt(i));const en=[F],carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);
              const st=Math.max(i+1,base);X(top);dd(r.slice(st,m-1).concat(top),A.slice(st),carry,F);X(top);
              this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});}
          const rt=two?r[2]:r[1];
          one(()=>eqT(hi,tgS));
          for(let i=hi-1;i>=0;i--)one(()=>{eqT(i+1,tgS);const en=[F];X(rt);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(rt),u,0,A[i]));X(rt);
            for(let j=t;j--;)this.swap(en,A[i],u[j]);});
          one(()=>{const carry=r[m-1];X(rt);this.reverse(()=>dd(v.slice(0,-1).concat(rt),u,carry,F));X(rt);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
          if(two){one(()=>this.swap([F],r[1],r[3]));one(()=>this.swap([F],r[0],r[2]));}else one(()=>this.swap([F],r[0],r[1]));
          one(()=>this.rot(c,L.slice(m,n+1),-1));
          rot(all,L.slice(0,n+1),c,-1,base,tgN);
          const vv=[];normH(vv,r,c,base,tgN);for(let i=vv.length;i--;)all.push({fn:vv[i].fn,rev:!vv[i].rev,k:K,base:BASE});
        }else{
          const tagged=kind==='low',tg=tagged?[R[m],...this.tagR]:[];
          const eq=i=>{if(tagged&&i>=lo&&i<=hi)eqT(i,tg);};
          norm(all,r,c,base,tg);
          if(tagged){
            one(()=>{this.op(c,r[m-1]);X(r[0]);dd(r.slice(1,m-1).concat(r[0]),A.slice(1),r[m-1],F);X(r[0]);});
            for(let i=0;i<hi;i++)one(()=>{eq(i);const en=[F],carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);
              if(i===0){X(r[1]);dd(r.slice(2,m-1).concat(r[1]),A.slice(2),carry,F);X(r[1]);}
              else{X(r[0]);dd(r.slice(i+1,m-1).concat(r[0]),A.slice(i+1),carry,F);X(r[0]);}
              this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});
            one(()=>eq(hi));
            for(let i=hi-1;i>=0;i--)one(()=>{eq(i+1);const en=[F];X(r[0]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[0]),u,0,A[i]));X(r[0]);
              for(let j=t;j--;)this.swap(en,A[i],u[j]);});
            one(()=>{const carry=r[m-1];X(r[0]);this.reverse(()=>dd(v.slice(0,-1).concat(r[0]),u,carry,F));X(r[0]);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
          }else{
            const tst=Z;
            one(()=>{this.op(c,r[m-1]);X(tst);dd(r.slice(0,-1).concat(tst),A,r[m-1],F);X(tst);});
            one(()=>this.op(c,tst));
            for(let i=0;i<hi;i++)one(()=>{const en=[tst],carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);
              dd(r.slice(i+1,m-1).concat(F),A.slice(i+1),carry,tst);this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});
            for(let i=hi-1;i>=0;i--)one(()=>{const en=[tst];X(r[0]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[0]),u,0,A[i]));X(r[0]);
              for(let j=t;j--;)this.swap(en,A[i],u[j]);});
            one(()=>this.op(c,tst));
            one(()=>{const carry=r[m-1];X(tst);this.reverse(()=>dd(v.slice(0,-1).concat(tst),u,carry,F));X(tst);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
          }
          rot(all,r,c,-1,base,tg);
          one(()=>this.rot(c,L.slice(m,n+1),-1));
          rot(all,L.slice(0,n+1),c,-1,base,tg);
          const vv=[];norm(vv,r,c,base,tg);rot(vv,r,c,-1,base,tg);for(let i=vv.length;i--;)all.push({fn:vv[i].fn,rev:!vv[i].rev,k:K,base:BASE});
        }
        one(()=>{this.op(c,R[m]);for(let j=0;j<n+1;j++)this.swap(c,L[j],R[j]);this.op(c,this.sign);
          if(RED){const tp=this.tagR[1],non=()=>{this.zer([],R.slice(0,m+1),tp);X(tp);};non();if(single)this.op([tp,L[n-k]],F);else match([tp,L[n-k]],L.slice(0,m),F);this.reverse(non);}
          else if(single)this.op([L[n-k]],F);else match([L[n-k]],L.slice(0,m),F);});
      }
    }
    one(()=>X(this.sign));
    if(!this.flatOff){const u=Array.from({length:n},(_,i)=>L[n-i]),v=Array.from({length:n},(_,i)=>R[n-i]);
      all.push({rev:false,k:-1,base:-1,fn:()=>{this.zer([],v.slice(1),this.sign);const ctl=[this.sign];for(const z of v)X(z);this.add(ctl,v,u,0,null);
        for(const z of v)X(z);for(const z of u)this.op(ctl,z);const high=u[n-1];this.op([high],this.sign);X(high);
        this.lt([high],u.slice(0,-1),v.slice(1),this.sign);X(high);X(L[0]);for(let j=0;j<n+1;j++)this.swap([],L[j],R[n-j]);}});}
    return all;
  }
}
// emitWalk port-layout wrapper: w.tag = [Z, top placeholder] (2 entries, like D2Canonical(n,2)'s binding), fire via ws.fire
class TstRelay1E extends TstRelay1{constructor(n,opts={}){const b=new Base(n);super(n,b.tag[0],b.fire,opts);this.tag=b.tag.slice(0,2);this.tst=b.tst;this.aux=b.aux;}}
// TstRelayKE(n,k): emitWalk wrapper with k real tags (w.tag = k real + 1 top placeholder), fire via ws.fire.
class TstRelayKE extends TstRelay1{constructor(n,k,opts={}){const b=new Base(n);super(n,b.tag.slice(0,k),b.fire,opts);this.tag=b.tag.slice(0,k+1);this.tst=b.tst;this.aux=b.aux;}}
// TstRelayKR(n,realTags,fire): reduced TstRelayK (D2ReducedImpl semantics): classic select/balance temps on the first
// two real tags (select on r), fire-controlled reset, nonempty-guarded fire uncompute, and D2ReducedImpl's mark/shift
// tail; no FlatUnit tail. Needs >= 2 real tags (e.g. {641, L[n+1]}: L[n+1] is zero over the row plan).
class TstRelayKR extends TstRelay1{
  constructor(n,real,fire,opts={}){if(!Array.isArray(real)||real.length<2)throw Error('TstRelayKR needs >=2 real tags');super(n,real,fire,Object.assign({},opts,{flat:false}));this.reduced=true;}
  plan(){const all=super.plan(),n=this.n,L=this.L,R=this.R,c=[this.fire],push=fn=>all.push({fn,rev:false,k:-1,base:-1});
    for(let bits=1;bits<=n;bits++){const gap=n+1-bits,mark=()=>this.zer([R[n-bits+1]],R.slice(1,n-bits+1),this.fire);push(mark);push(()=>{for(let j=n;j>=gap;j--)this.swap(c,L[j],L[j+1]);});push(mark);}
    push(()=>{for(let j=n;j>=1;j--)this.swap([],R[j],R[j+1]);});return all;}
}
class TstRelayKRE extends TstRelayKR{constructor(n,k,opts={}){const b=new Base(n);super(n,b.tag.slice(0,k),b.fire,opts);this.tag=b.tag.slice(0,k+1);this.tst=b.tst;this.aux=b.aux;}}
// TstRelayKS(n,realTags,fire): SectorReduced semantics (plain unit walk + the mark/shift tail), tst-free and aux-free.
// For the divide OUTER walk: the old tst becomes a real tag. No FlatUnit tail.
class TstRelayKS extends TstRelay1{
  constructor(n,real,fire,opts={}){super(n,real,fire,Object.assign({},opts,{flat:false}));}
  plan(){const all=super.plan(),n=this.n,L=this.L,R=this.R,c=[this.fire],push=fn=>all.push({fn,rev:false,k:-1,base:-1});
    for(let bits=1;bits<=n;bits++){const gap=n+1-bits,mark=()=>this.zer([R[n-bits+1]],R.slice(1,n-bits+1),this.fire);push(mark);push(()=>{for(let j=n;j>=gap;j--)this.swap(c,L[j],L[j+1]);});push(mark);}
    push(()=>{for(let j=n;j>=1;j--)this.swap([],R[j],R[j+1]);});return all;}
}
class TstRelayKSE extends TstRelayKS{constructor(n,k,opts={}){const b=new Base(n);super(n,b.tag.slice(0,k),b.fire,opts);this.tag=b.tag.slice(0,k+1);this.tst=b.tst;this.aux=b.aux;}}
module.exports={TstRelay1,TstRelay1E,TstRelayK:TstRelay1,TstRelayKE,TstRelayKR,TstRelayKRE,TstRelayKS,TstRelayKSE};
