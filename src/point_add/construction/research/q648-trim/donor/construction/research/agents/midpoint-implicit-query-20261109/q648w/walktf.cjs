'use strict';
// Tst-free sector walk (ledger, q649 A3). Same contract as the aux-free walk (walkaf.cjs) but the scratch wire tst is
// gone:
//  * step enable: hosted on the fire wire F itself. Inside a tagged sector the shift is s = sigma-base in [2, 2^T-1];
//    the tag word is (R[m] = bit 0, real tags = bits 1..T-1) and its real part is nonzero for every s >= 2, while all
//    real tags are zero when the sector is not firing. So eq(i) toggles F on the tag pattern alone (no fire control),
//    which never matches a non-firing lane, and F returns to fire after the restore loop (sigma >= 2 > 0).
//  * constant-one tops of the divisor registers: in a tagged sector sigma>=2, so after normalization the divisor's
//    two low bits r[0],r[1] are zero under fire. The digit block drops the zero LSB pair (r[0],A[0]) and uses r[0]
//    (flipped) as the top; step 0 drops (r[1],A[1]) and uses r[1]; steps i>=1 and the final block use r[0], which is
//    zero under fire and untouched there. dirtyDigit with e=0 is the identity for any top value.
//  * select temp / qcond result: real tag wires (zero outside sector bodies).
//  Sectors per row: sigma=1 as an untagged single-shift sector (the original body, tst on a zero real tag), then
//  tagged sectors base=w*j, sigma in [base+2, base+2^T-1], w = 2^T-2. sigma=0 never fires (a firing row needs
//  bitlen(r) <= m-1, else the swapped r would overflow the next row's register); mini0:true keeps a sigma=0 sector.
const P=require('../q653-next/parts.cjs');
const {source}=require('./walkaf.cjs');
const Base=Function('module','dirtyDigit',source+'\nreturn UnitWalk;')({exports:{}},P.dirtyDigit);
class TstFree extends Base{
  // realTags: wires for tag bits 1..T-1 (also used as select temp / qcond hosts); fire: the fire/enable wire.
  constructor(n,realTags,fire,{mini0=true}={}){super(n);this.tagR=realTags.slice();this.tag=realTags.slice();this.fire=fire;
    this.tst=-7;this.aux=-7;this.direct=true;this.mini0=mini0;this.ddFn=arguments[3]&&arguments[3].dirtyDigit||null;if(realTags.length<2)throw Error('tf tags');}
  // Optional digit primitive (opts.dirtyDigit): same contract as parts.dirtyDigit; used by every digit and restore.
  restore(c,a,b,unused,h){if(!this.ddFn)return super.restore(c,a,b,unused,h);if(c.length!==1)throw Error('control');for(const z of this.ddFn(a,b,h,c[0],this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z[z.length-1]);}
  mcx(c,t){if(new Set(c).size!==c.length||c.includes(t))throw Error('tf alias');
    if(c.length<=2){this.raw(c.length?c[0]:-1,c.length===2?c[1]:-1,t);return;}
    const k=c.length,w=[];for(const q of this.y.slice(1)){if(w.length===k-2)break;if(q!==t&&!c.includes(q))w.push(q);}
    if(w.length<k-2)throw Error('tf borrow');
    for(let s=0;s<2;s++){if(s===0)this.raw(c[0],c[1],w[0]);for(let i=1;i<k-2;i++)this.raw(c[i+1],w[i-1],w[i]);this.raw(c[k-1],w[k-3],t);for(let i=k-3;i>=1;i--)this.raw(c[i+1],w[i-1],w[i]);if(s===0)this.raw(c[0],c[1],w[0]);}}
  sectors(m){const T=1+this.tagR.length,w=(1<<T)-2,out=[];
    for(let j=0;;j++){const base=w*j,lo=base+2;if(lo>m-1)break;out.push({base,lo,hi:Math.min(m-1,base+(1<<T)-1),tagged:true});}
    if(m-1>=1)out.push({base:1,lo:1,hi:1,tagged:false});
    if(this.mini0)out.push({base:0,lo:0,hi:0,tagged:false});
    if(out.length===1){out[0].lo=0;out[0].hi=m-1;} // single sector covers everything (only m=1: sigma=0)
    return out.sort((a,b)=>b.lo-a.lo);}
  plan(){
    const n=this.n,L=this.L,R=this.R,F=this.fire,c=[F],all=[],qa=this.tagR[0],tmp=this.tagR[1];
    let K=-1,BASE=-1;
    const blk=(fn,rev=false)=>({fn,rev,k:K,base:BASE});
    const one=fn=>all.push(blk(fn));
    const rot=(ar,w,controls,dir,base,tg)=>{if(base)ar.push(blk(()=>this.rot(controls,w,dir*base)));
      for(let j=0;j<tg.length;j++){const s=1<<j;if(s>=w.length)break;ar.push(blk(()=>this.rot(controls.concat(tg[j]),w,dir*s)));}};
    const norm=(ar,w,controls,base,tg)=>{if(base)ar.push(blk(()=>this.rot(controls,w,base)));
      for(let j=tg.length;j--;){const s=1<<j;if(s>=w.length)continue;ar.push(blk(()=>{this.zer(controls,w.slice(w.length-s),tg[j]);this.rot(controls.concat(tg[j]),w,s);}));}};
    const val=(w,controls,base,tg)=>{const a=[];norm(a,w,controls,base,tg);rot(a,w,controls,-1,base,tg);return a;};
    const co=(a,t)=>Array.from({length:t},(_,i)=>a[n-i]);
    const W=L.slice(0,n),S=R.slice(0,n);
    one(()=>{const high=S[n-1];this.op([high],this.sign);this.raw(-1,-1,high);this.lt([high],S.slice(0,-1),W.slice(1),this.sign);this.raw(-1,-1,high);});
    one(()=>{const cc=[this.sign];for(const z of W)this.raw(-1,-1,z);this.add(cc,W,S,0,null);for(const z of W)this.raw(-1,-1,z);for(const z of S)this.op(cc,z);});
    one(()=>this.raw(-1,-1,R[n]));
    for(let k=0;k<n;k++){K=k;BASE=-1;
      const t=k+1,m=n-k,A=L.slice(0,m),r=R.slice(0,m),u=co(L,t),v=co(R,t);
      const select=z=>{const large=()=>{this.zer([],this.reduced?r:A.slice(1),tmp);this.raw(-1,-1,tmp);};large();this.lt([tmp],A,r,z);this.reverse(large);};
      if(k>0&&k<n-1&&!this.noBalance){const cp=[tmp];
        one(()=>select(F));
        one(()=>{const qcond=()=>{this.op([r[m-1]],qa);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),qa);this.raw(-1,-1,r[m-1]);};
          qcond();this.op([F,qa],tmp);for(const z of u)this.raw(-1,-1,z);this.lt([F,qa],v,u,tmp);for(const z of u)this.raw(-1,-1,z);this.reverse(qcond);});
        one(()=>{this.reverse(()=>this.add(cp,r,A,null,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,null,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
        one(()=>this.op(this.reduced?[F,L[n-k]]:[L[n-k]],tmp));
        one(()=>select(F));
      }
      for(const sp of this.sectors(m)){const {base,lo,hi,tagged}=sp;BASE=base;
        const tg=tagged?[R[m]].concat(this.tagR):[];
        const single=lo===0&&hi===m-1;
        const match=(controls,word,out)=>{this.zer(controls,word.slice(m-lo),out);if(hi+1<m)this.zer(controls,word.slice(m-hi-1),out);};
        const eq=i=>{if(tagged&&i>=lo&&i<=hi){const q=i-base,neg=tg.filter((_,j)=>!(q>>j&1));for(const w of neg)this.raw(-1,-1,w);this.mcx(tg,F);for(const w of neg)this.raw(-1,-1,w);}};
        if(single)one(()=>select(F));
        else one(()=>{select(F);match(c,r,qa);select(F);this.op([qa],F);this.op(c,qa);});
        one(()=>this.op(c,R[m]));
        norm(all,r,c,base,tg);
        const dd=(Alow,B,h,e)=>{for(const z of (this.ddFn||P.dirtyDigit)(Alow,B,h,e,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z[z.length-1]);};
        const X=w=>this.raw(-1,-1,w);
        if(tagged){ // sigma>=2: r[0]=r[1]=0 under fire after norm; enable on F
          // digit: divisor r[0..m-2]+1 with r[0]=0 -> drop the LSB pair (r[0],A[0]); r[0] hosts the constant top
          one(()=>{this.op(c,r[m-1]);X(r[0]);dd(r.slice(1,m-1).concat(r[0]),A.slice(1),r[m-1],F);X(r[0]);});
          for(let i=0;i<hi;i++)one(()=>{eq(i);const en=[F],carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);
            if(i===0){X(r[1]);dd(r.slice(2,m-1).concat(r[1]),A.slice(2),carry,F);X(r[1]);}
            else{X(r[0]);dd(r.slice(i+1,m-1).concat(r[0]),A.slice(i+1),carry,F);X(r[0]);}
            this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});
          one(()=>eq(hi));
          for(let i=hi-1;i>=0;i--)one(()=>{eq(i+1);const en=[F];X(r[0]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[0]),u,0,A[i]));X(r[0]);
            for(let j=t;j--;)this.swap(en,A[i],u[j]);});
          one(()=>{const carry=r[m-1];X(r[0]);this.reverse(()=>dd(v.slice(0,-1).concat(r[0]),u,carry,F));X(r[0]);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
        }else{ // untagged single-shift sector: the original body with tst on a (zero) real tag wire
          const tst=tmp;
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
        const vv=val(r,c,base,tg);for(let i=vv.length;i--;)all.push({fn:vv[i].fn,rev:!vv[i].rev,k:K,base:BASE});
        one(()=>{this.op(c,R[m]);for(let j=0;j<n+1;j++)this.swap(c,L[j],R[j]);this.op(c,this.sign);if(this.reduced){const non=()=>{this.zer([],R.slice(0,m+1),tmp);this.raw(-1,-1,tmp);};non();if(single)this.op([tmp,L[n-k]],F);else match([tmp,L[n-k]],L.slice(0,m),F);this.reverse(non);}
          else if(single)this.op([L[n-k]],F);else match([L[n-k]],L.slice(0,m),F);});
      }
    }
    one(()=>this.raw(-1,-1,this.sign));
    return all;
  }
}
// TstRelay (ledger, q648): TstFree composed with a constructive-zero tag relay (after jackylee0424's 649 relay idea, but
// without tst). T = realTags.length+2 logical tags: bit 0 = row-top port R[m], bit 1 = RELAYED on r[1]/r[0], bits 2.. = real.
// Sectors: sigma=1 untagged; low sector base 0, T-1 tags (bits 0,2..), sigma in [2, 2^(T-1)-1] (plain TstFree rule);
// high sectors base_j (base_1 = 2^(T-1)-4 >= 4, step 2^T-4), sigma in [base+4, base+2^T-1]: the real part (bits 2..) of s
// is nonzero for every s >= 4, so the unconditioned eq toggles never match a non-firing lane even though the relayed bit's
// host is data there. In a high sector the coarse rotation by base puts known zeros on r[0..base-1]; the fine
// normalization rotates only r[base..m-1] (same result), so r[0..base-1] stay zero and untouched for the whole sector:
//   relay bit on r[1] (norm, digit, step 0), hop r[1]->r[0] under F before step 1, r[0] through the restores, hop back;
//   constant-one tops on r[0] (digit), r[2] (steps 0,1), r[1] (steps>=2, restores, final block);
//   digits drop the known-zero divisor prefix r[0..base-1] (and the matching unchanged numerator bits).
// Denormalization is the exact inverse order (fine on the sub-register, then coarse).
class TstRelay extends TstFree{
  constructor(n,realTags,fire,opts={}){if(realTags.length<2)throw Error('TstRelay needs >=2 real tags');super(n,realTags,fire,Object.assign({mini0:false},opts));this.T=realTags.length+2;}
  sectors(m){const T=this.T,out=[];
    if(m-1>=1)out.push({base:1,lo:1,hi:1,kind:'mini'});
    if(this.mini0)out.push({base:0,lo:0,hi:0,kind:'mini'});
    const lowHi=Math.min(m-1,(1<<(T-1))-1);if(lowHi>=2)out.push({base:0,lo:2,hi:lowHi,kind:'low'});
    for(let base=(1<<(T-1))-4;;base+=(1<<T)-4){const lo=base+4;if(lo>m-1)break;out.push({base,lo,hi:Math.min(m-1,base+(1<<T)-1),kind:'high'});}
    if(out.length===0)out.push({base:0,lo:0,hi:m-1,kind:'mini'});
    if(out.length===1&&out[0].kind==='mini'&&m-1<=1){out[0].lo=0;out[0].hi=m-1;}
    return out.sort((a,b)=>b.lo-a.lo);}
  plan(){
    const n=this.n,L=this.L,R=this.R,F=this.fire,c=[F],all=[],qa=this.tagR[0],tmp=this.tagR[1];
    let K=-1,BASE=-1;
    const blk=(fn,rev=false)=>({fn,rev,k:K,base:BASE});
    const one=fn=>all.push(blk(fn));
    // full-register helpers (low/mini sectors, exactly as TstFree)
    const rot=(ar,w,controls,dir,base,tg)=>{if(base)ar.push(blk(()=>this.rot(controls,w,dir*base)));
      for(let j=0;j<tg.length;j++){const s=1<<j;if(s>=w.length)break;ar.push(blk(()=>this.rot(controls.concat(tg[j]),w,dir*s)));}};
    const norm=(ar,w,controls,base,tg)=>{if(base)ar.push(blk(()=>this.rot(controls,w,base)));
      for(let j=tg.length;j--;){const s=1<<j;if(s>=w.length)continue;ar.push(blk(()=>{this.zer(controls,w.slice(w.length-s),tg[j]);this.rot(controls.concat(tg[j]),w,s);}));}};
    // relay (high) sectors: coarse on the full register, fine on w.slice(base)
    const normH=(ar,w,controls,base,tg)=>{ar.push(blk(()=>this.rot(controls,w,base)));const ws=w.slice(base);
      for(let j=tg.length;j--;){const s=1<<j;if(s>=ws.length)continue;ar.push(blk(()=>{this.zer(controls,ws.slice(ws.length-s),tg[j]);this.rot(controls.concat(tg[j]),ws,s);}));}};
    const unrotH=(ar,w,controls,base,tg)=>{const ws=w.slice(base);
      for(let j=0;j<tg.length;j++){const s=1<<j;if(s>=ws.length)break;ar.push(blk(()=>this.rot(controls.concat(tg[j]),ws,-s)));}
      ar.push(blk(()=>this.rot(controls,w,-base)));};
    const co=(a,t)=>Array.from({length:t},(_,i)=>a[n-i]);
    const W=L.slice(0,n),S=R.slice(0,n);
    one(()=>{const high=S[n-1];this.op([high],this.sign);this.raw(-1,-1,high);this.lt([high],S.slice(0,-1),W.slice(1),this.sign);this.raw(-1,-1,high);});
    one(()=>{const cc=[this.sign];for(const z of W)this.raw(-1,-1,z);this.add(cc,W,S,0,null);for(const z of W)this.raw(-1,-1,z);for(const z of S)this.op(cc,z);});
    one(()=>this.raw(-1,-1,R[n]));
    for(let k=0;k<n;k++){K=k;BASE=-1;
      const t=k+1,m=n-k,A=L.slice(0,m),r=R.slice(0,m),u=co(L,t),v=co(R,t);
      const select=z=>{const large=()=>{this.zer([],this.reduced?r:A.slice(1),tmp);this.raw(-1,-1,tmp);};large();this.lt([tmp],A,r,z);this.reverse(large);};
      if(k>0&&k<n-1&&!this.noBalance){const cp=[tmp];
        one(()=>select(F));
        one(()=>{const qcond=()=>{this.op([r[m-1]],qa);this.raw(-1,-1,r[m-1]);this.lt([r[m-1]],r.slice(0,-1),A.slice(1),qa);this.raw(-1,-1,r[m-1]);};
          qcond();this.op([F,qa],tmp);for(const z of u)this.raw(-1,-1,z);this.lt([F,qa],v,u,tmp);for(const z of u)this.raw(-1,-1,z);this.reverse(qcond);});
        one(()=>{this.reverse(()=>this.add(cp,r,A,null,null));for(let j=0;j<m;j++)this.swap(cp,A[j],r[j]);this.add(cp,v,u,null,null);for(let j=0;j<t;j++)this.swap(cp,u[j],v[j]);this.op(cp,this.sign);});
        one(()=>this.op(this.reduced?[F,L[n-k]]:[L[n-k]],tmp));
        one(()=>select(F));
      }
      for(const sp of this.sectors(m)){const {base,lo,hi,kind}=sp;BASE=base;
        const single=lo===0&&hi===m-1;
        const match=(controls,word,out)=>{this.zer(controls,word.slice(m-lo),out);if(hi+1<m)this.zer(controls,word.slice(m-hi-1),out);};
        const dd=(Alow,B,h,e)=>{for(const z of (this.ddFn||P.dirtyDigit)(Alow,B,h,e,this.y[0]))this.raw(z.length===1?-1:z[0],z.length===3?z[1]:-1,z[z.length-1]);};
        const X=w=>this.raw(-1,-1,w);
        if(single)one(()=>select(F));
        else one(()=>{select(F);match(c,r,qa);select(F);this.op([qa],F);this.op(c,qa);});
        one(()=>this.op(c,R[m]));
        if(kind==='high'){
          const tgN=[R[m],r[1],...this.tagR],tgS=[R[m],r[0],...this.tagR];
          const eq=(i,tg)=>{if(i>=lo&&i<=hi){const q=i-base,neg=tg.filter((_,j)=>!(q>>j&1));for(const w of neg)X(w);this.mcx(tg,F);for(const w of neg)X(w);}};
          normH(all,r,c,base,tgN);
          one(()=>{this.op(c,r[m-1]);X(r[0]);dd(r.slice(base,m-1).concat(r[0]),A.slice(base),r[m-1],F);X(r[0]);});
          for(let i=0;i<hi;i++){
            if(i===1)one(()=>this.swap([F],r[1],r[0]));
            one(()=>{eq(i,i===0?tgN:tgS);const en=[F],carry=r[i];for(const z of A.slice(i))this.swap(en,carry,z);
              const st=Math.max(i+1,base),top=i<=1?r[2]:r[1];
              X(top);dd(r.slice(st,m-1).concat(top),A.slice(st),carry,F);X(top);
              this.op(en.concat(carry),A[i]);this.op(en.concat(A[i]),carry);});}
          if(hi<=1)throw Error('TstRelay high sector too short');
          one(()=>eq(hi,tgS));
          for(let i=hi-1;i>=0;i--)one(()=>{eq(i+1,tgS);const en=[F];X(r[1]);this.reverse(()=>this.restore(en,v.slice(0,-1).concat(r[1]),u,0,A[i]));X(r[1]);
            for(let j=t;j--;)this.swap(en,A[i],u[j]);});
          one(()=>{const carry=r[m-1];X(r[1]);this.reverse(()=>dd(v.slice(0,-1).concat(r[1]),u,carry,F));X(r[1]);for(let j=t;j--;)this.swap(c,carry,u[j]);this.swap(c,carry,L[m]);this.op(c,carry);});
          // Tail. The donor order is [unrotate r, rotate L, re-normalize r, normalize^-1 r]; the first and third are
          // inverse rotations of r and the L rotations commute with them (they read only tags/F), so both are dropped:
          // the relayed bit never rides a full-register (coarse) rotation, and normalize^-1 clears it on r[1].
          one(()=>this.swap([F],r[0],r[1]));
          one(()=>this.rot(c,L.slice(m,n+1),-1));
          rot(all,L.slice(0,n+1),c,-1,base,tgN);
          const vv=[];normH(vv,r,c,base,tgN);for(let i=vv.length;i--;)all.push({fn:vv[i].fn,rev:!vv[i].rev,k:K,base:BASE});
        }else{
          const tagged=kind==='low',tg=tagged?[R[m]].concat(this.tagR):[];
          const eq=i=>{if(tagged&&i>=lo&&i<=hi){const q=i-base,neg=tg.filter((_,j)=>!(q>>j&1));for(const w of neg)X(w);this.mcx(tg,F);for(const w of neg)X(w);}};
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
            const tst=tmp;
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
        one(()=>{this.op(c,R[m]);for(let j=0;j<n+1;j++)this.swap(c,L[j],R[j]);this.op(c,this.sign);if(this.reduced){const non=()=>{this.zer([],R.slice(0,m+1),tmp);this.raw(-1,-1,tmp);};non();if(single)this.op([tmp,L[n-k]],F);else match([tmp,L[n-k]],L.slice(0,m),F);this.reverse(non);}
          else if(single)this.op([L[n-k]],F);else match([L[n-k]],L.slice(0,m),F);});
      }
    }
    one(()=>this.raw(-1,-1,this.sign));
    return all;
  }
}
// Drop-in for D2Canonical(n,T) / SectorCanonical(n,T) under emitWalk: same port layout (w.tag = T entries, the last one
// the row-top placeholder; T-1 real tags), fire on the walk's fire id; tst/aux are not used (their ports may be -1).
// D2Canonical(n,T) + tst  ->  TstFreeD(n,T) frees the tst wire;  ->  TstFreeD(n,T+1) with tst's wire as the extra
// real tag (ws.tag=[...realTags, tstWire, -1]) keeps the wire count and gains a tag.
class TstFreeD extends TstFree{
  constructor(n,T,opts={}){const b=new Base(n);if(T<3||T>b.tag.length)throw Error('TstFreeD tags');
    super(n,b.tag.slice(0,T-1),b.fire,Object.assign({mini0:false},opts));this.tag=b.tag.slice(0,T);this.tst=b.tst;this.aux=b.aux;this.flatOff=opts.flat===false;}
  // D2Canonical is FlatUnit (D2Flat's source returns FlatUnit): the unit-walk plan plus FlatUnit's final block,
  // copied verbatim (it uses sign/L/R only; add ignores cin). flat:false gives the plain UnitWalk plan.
  plan(){const a=super.plan();if(this.flatOff)return a;const n=this.n,u=Array.from({length:n},(_,i)=>this.L[n-i]),v=Array.from({length:n},(_,i)=>this.R[n-i]);
    a.push({rev:false,k:-1,base:-1,fn:()=>{this.zer([],v.slice(1),this.sign);const ctl=[this.sign];for(const z of v)this.raw(-1,-1,z);this.add(ctl,v,u,0,null);
      for(const z of v)this.raw(-1,-1,z);for(const z of u)this.op(ctl,z);const high=u[n-1];this.op([high],this.sign);this.raw(-1,-1,high);
      this.lt([high],u.slice(0,-1),v.slice(1),this.sign);this.raw(-1,-1,high);this.raw(-1,-1,this.L[0]);for(let j=0;j<n+1;j++)this.swap([],this.L[j],this.R[n-j]);}});
    return a;}
  op(c,z){if(c.length<=2){this.raw(c.length?c[0]:-1,c.length===2?c[1]:-1,z);return;}const b=this.y.filter(w=>w!==z&&!c.includes(w)),k=c.length;
    if(k-2>b.length)throw Error('borrow');
    for(let s=0;s<2;s++){if(s===0)this.raw(c[0],c[1],b[0]);for(let i=1;i<k-2;i++)this.raw(c[i+1],b[i-1],b[i]);this.raw(c[k-1],b[k-3],z);for(let i=k-3;i>=1;i--)this.raw(c[i+1],b[i-1],b[i]);if(s===0)this.raw(c[0],c[1],b[0]);}}
}
// Drop-in for D2ReducedImpl(n,T) (the divide's reverse walk, D2Reduced(n,-4) = D2ReducedImpl(n,4)): the Reduced
// ("generic") edits of the split source -- select on r, fire-controlled tst reset, nonempty-guarded fire uncompute,
// all hosted on a zero real tag -- and D2ReducedImpl's mark/shift tail. Not FlatUnit.
class TstFreeR extends TstFreeD{
  constructor(n,T,opts={}){super(n,T,Object.assign({},opts,{flat:false}));this.reduced=true;}
  plan(){const all=super.plan(),n=this.n,L=this.L,R=this.R,c=[this.fire],push=fn=>all.push({fn,rev:false,k:-1,base:-1});
    for(let bits=1;bits<=n;bits++){const gap=n+1-bits,mark=()=>this.zer([R[n-bits+1]],R.slice(1,n-bits+1),this.fire);push(mark);push(()=>{for(let j=n;j>=gap;j--)this.swap(c,L[j],L[j+1]);});push(mark);}
    push(()=>{for(let j=n;j>=1;j--)this.swap([],R[j],R[j+1]);});return all;}
}
// TstRelayD: TstRelay + D2Canonical's FlatUnit tail (drop-in for D2Canonical(n,T)/HostedWalk-style multiply walks).
class TstRelayD extends TstRelay{
  plan(){const a=super.plan();const n=this.n,u=Array.from({length:n},(_,i)=>this.L[n-i]),v=Array.from({length:n},(_,i)=>this.R[n-i]);
    a.push({rev:false,k:-1,base:-1,fn:()=>{this.zer([],v.slice(1),this.sign);const ctl=[this.sign];for(const z of v)this.raw(-1,-1,z);this.add(ctl,v,u,0,null);
      for(const z of v)this.raw(-1,-1,z);for(const z of u)this.op(ctl,z);const high=u[n-1];this.op([high],this.sign);this.raw(-1,-1,high);
      this.lt([high],u.slice(0,-1),v.slice(1),this.sign);this.raw(-1,-1,high);this.raw(-1,-1,this.L[0]);for(let j=0;j<n+1;j++)this.swap([],this.L[j],this.R[n-j]);}});
    return a;}
}
// TstRelayE(n,T,opts): emitWalk drop-in with D2Canonical(n,T)'s PORT LAYOUT (T-1 entries of w.tag bound by ws.tag:
// T-2 real tags + one top placeholder that is never emitted; fire bound by ws.fire; tst/aux never emitted). TstRelayD
// semantics (T logical tags: row top, relayed bit on r[1]/r[0], T-2 real). opts.dirtyDigit as TstFree; opts.flat=false
// drops the FlatUnit tail (plain unit walk).
class TstRelayE extends TstRelayD{
  constructor(n,T,opts={}){const b=new Base(n);if(T<4||T>b.tag.length)throw Error('TstRelayE tags');
    super(n,b.tag.slice(0,T-2),b.fire,opts);this.tag=b.tag.slice(0,T-1);this.tst=b.tst;this.aux=b.aux;this.flatOff=opts.flat===false;}
  plan(){return this.flatOff?TstRelay.prototype.plan.call(this):super.plan();}
}
// TstRelayRE(n,T,opts): emitWalk drop-in with D2ReducedImpl(n,T)'s port layout: TstRelay in reduced mode (select on r,
// fire-controlled reset, nonempty-guarded fire uncompute, on zero real tags) + D2ReducedImpl's mark/shift tail.
// L[n+1] may be passed as a real tag (zero over the row plan; the tail uses it as data only after the tags are clear).
class TstRelayRE extends TstRelay{
  constructor(n,T,opts={}){const b=new Base(n);if(T<4||T>b.tag.length)throw Error('TstRelayRE tags');
    super(n,b.tag.slice(0,T-2),b.fire,opts);this.tag=b.tag.slice(0,T-1);this.tst=b.tst;this.aux=b.aux;this.reduced=true;}
  plan(){const all=super.plan(),n=this.n,L=this.L,R=this.R,c=[this.fire],push=fn=>all.push({fn,rev:false,k:-1,base:-1});
    for(let bits=1;bits<=n;bits++){const gap=n+1-bits,mark=()=>this.zer([R[n-bits+1]],R.slice(1,n-bits+1),this.fire);push(mark);push(()=>{for(let j=n;j>=gap;j--)this.swap(c,L[j],L[j+1]);});push(mark);}
    push(()=>{for(let j=n;j>=1;j--)this.swap([],R[j],R[j+1]);});return all;}
}
module.exports={TstFree,TstFreeD,TstFreeR,TstRelay,TstRelayD,TstRelayE,TstRelayRE,Base};
