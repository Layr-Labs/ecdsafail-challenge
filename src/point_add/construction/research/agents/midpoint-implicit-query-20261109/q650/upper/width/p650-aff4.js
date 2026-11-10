'use strict';
// papers: affine rows U4MIN..63 (u3 layout) without tags[1]. tags[1] is replaced by carry for the rank lifetime
// [normalizeA, guardedBarrel(r)] (normalizeA^-1 moved up; v[k] restored before every v reader, so no withV swaps).
// carry's former roles there are removed:
//  - guardedBarrel guards and parkAffine marks: V^d.(d^=P).V^d.(d^=P) = V^P for an involution V and a dirty y wire d
//    (a rotation = two reflections; parkAffine's swap is one);
//  - mixedHeld inside affineProduct: dirty digits (same map as the clean digit) under the single control take;
//  - affineProduct tail mark: the rank and take form an 8-bit counter E (bit 7 = take wire). On untaken lanes the
//    helper-hosted bits (weights 8..64) are forced to 1 and the three untaken-data hosts sit at weights 1,2,4, so
//    E<=127 and E>=120; on taken lanes E=rank+128. E is decremented before each tail step, so bit 7 equals
//    take & [rank > j] at step j (taken: rank+127-j >= 128 iff rank > j; untaken: E-j-1 >= 120-L >= 0 for k>=7).
//    E is restored by adding L and undoing the forcing. normalizeA's toggles are take-gated, so helper rank bits are
//    0 on untaken lanes; every rank reader is take-gated or is normalizeA itself.
const U4MIN=+(process.env.U4MIN||7);
const body=String.raw`
    u4Inv(word,origins){
      const at=word.slice(),where=new Map(at.map((w,i)=>[w,i]));
      for(let to=0;to<at.length;to++){const from=where.get(origins[to]);if(from===undefined)throw Error('u4 origin');if(from===to)continue;const tk=at[from],mv=at[to];at[to]=tk;at[from]=mv;where.set(tk,to);where.set(mv,from);}
      const idx=new Map(word.map((w,i)=>[w,i])),src=at.map(w=>idx.get(w)),seen=new Uint8Array(word.length),R1=[],R2=[];
      for(let s=0;s<word.length;s++){if(seen[s])continue;const cyc=[];let p=s;while(!seen[p]){seen[p]=1;cyc.push(p);p=src[p];}
        const m=cyc.length;if(m<2)continue;
        for(let i=0;i<m;i++){const j=(m-i)%m;if(i<j)R1.push([word[cyc[i]],word[cyc[j]]]);}
        for(let i=0;i<m;i++){const j=((1-i)%m+m)%m;if(i<j)R2.push([word[cyc[i]],word[cyc[j]]]);}}
      const test=(A,B)=>{const lab=new Map(word.map(w=>[w,w])),sw=([x,y])=>{const t=lab.get(x);lab.set(x,lab.get(y));lab.set(y,t);};A.forEach(sw);B.forEach(sw);return word.every((w,p)=>lab.get(w)===at[p]);};
      if(test(R1,R2))return [R1,R2];if(test(R2,R1))return [R2,R1];throw Error('u4 involution split');
    }
    u4Guarded(tape,word,origins,extra,back){
      const cs=[...this.ctrl,...extra],d=this.u4d,[V1,V2]=this.u4Inv(word,origins);
      const one=V=>{const half=()=>{for(const [x,y] of V)this.gatedSwap(tape,x,y,[d],[]);};half();this.toggle(tape,cs,[],d);half();this.toggle(tape,cs,[],d);};
      stepList([()=>one(V1),()=>one(V2)],back,fn=>fn());
    }
    u4Park(tape,D,back){
      const base=this.half+1,off=base-this.h,d=this.u4d;
      stepList(split(this.h,this.half),back,i=>{
        const sw=()=>this.gatedSwap(tape,D[i],this.r[off+i],[d],[]),mark=()=>this.indicator(tape,i-this.h,"le",this.ctrl,d);
        sw();mark();sw();mark();
      });
    }
    u4Product(tape,a,d,back){
      const base=this.half+1,take=this.take,E=[...this.tag,take],L=this.r.length-base;
      if(E.length!==8||!(120>=L))throw Error('u4 counter headroom '+[E.length,L]);
      const init=()=>{tape.out(NONE,NONE,take);for(const i of [3,4,5,6])tape.out(NONE,take,E[i]);tape.out(NONE,NONE,take);};
      const mh=rv=>{const layer=Object.create(this);layer.digit=this.digitDirty;layer.mixed(tape,this.r.slice(0,base),a,d,[take],rv);};
      const addL=rv=>{const bs=[];for(let b=0;(L>>b)>0;b++)if((L>>b)&1)bs.push(b);stepList(bs,rv,b=>this.inc(tape,E.slice(b),[],rv));};
      const tail=rv=>stepList(split(base,this.r.length),rv,i=>{
        const z=[...d,this.r[i]],orig=z.slice(1).concat(z[0]);
        const seq=[rr=>this.inc(tape,E,[],!rr),rr=>this.digit(tape,z,a,[take],!rr),rr=>this.permute(tape,z,orig,[take],rr)];
        stepList(seq,rv,fn=>fn(rv));
      });
      stepList([mh,()=>init(),tail,addL,()=>init()],back,fn=>fn(back));
    }
    u4AffineBody(tape,back){
        const a=this.A.slice(0,this.half),r=this.r,v=this.v,D=this.zword.slice(0,this.half),d=D.slice(0,this.h);
        const base=this.half+1,word=[...r.slice(0,base),...D],tail=r.slice(base),g=this.ctrl,host=v.at(-1);
        if(this.tag[0]!==host||this.tag[5]!==this.carry||this.tag.includes(this.tags[1])||this.tag.length!==7)throw Error('U4 affine ports');
        if(process.env.U4DBG&&!globalThis.__u4p){globalThis.__u4p=1;console.error('U4 k',this.k,'tag',JSON.stringify(this.tag),'take',this.take,'carry',this.carry,'pick',this.pick,'d',this.u4d);}
        const canon=rv=>this.digit(tape,[...d,this.dv[0]],v,[],rv);
        const leading=()=>tape.out(NONE,this.take,host);
        const normT=rv=>stepList(split(0,this.tag.length).reverse(),rv,j=>{
            const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=this.tag[j];
            stepList([()=>this.toggle(tape,[this.take],a.slice(-k),bit),rr=>this.permute(tape,a,orig,[bit],rr)],rv,fn=>fn(rv));
        });
        const barrel=(w,left,rv)=>stepList(split(0,this.tag.length),rv,j=>{
            const k=(1<<j)%w.length;if(!k)return;
            const origin=left?w.slice(-k).concat(w.slice(0,-k)):w.slice(k).concat(w.slice(0,k));
            this.u4Guarded(tape,w,origin,[this.tag[j]],rv);
        });
        const mixedV=rv=>{const layer=Object.create(this);layer.digit=this.digitDirty;layer.mixed(tape,r,v,d,[this.take],!rv);};
        const seq=[canon,leading,normT,rv=>barrel(D,true,rv),rv=>this.u4Park(tape,D,rv),rv=>this.u4Product(tape,a,D,rv),
            rv=>barrel(r,false,rv),rv=>normT(!rv),leading,
            rv=>this.reflect(tape,word,g,rv),rv=>this.inc(tape,word,g,!rv),
            rv=>this.guardedPermutation(tape,[...tail,...D],[...D,...tail],[],rv),
            mixedV,()=>this.cnotList(tape,g,d),rv=>tape.add(v,d,g,this.carry,rv),rv=>this.inc(tape,r,g,rv),rv=>canon(!rv)];
        stepList(seq,back,fn=>fn(back));
    }
    affine(tape,back){
        if(this.u4Affine){this.u4AffineBody(tape,back);return;}
`;
module.exports=[
 ['    affine(tape,back){\n        if(this.v1Affine){this.v1AffineBody(tape,back);return;}', body+'        if(this.v1Affine){this.v1AffineBody(tape,back);return;}'],
 ['const layer=Object.create(H);layer.tag=H.tag.slice();layer.tag[4]=this.A[this.half];super.affine.call(layer,tape,back);',
  'const layer=Object.create(H);layer.tag=H.tag.slice();layer.tag[4]=this.A[this.half];'+
  'if(this.k>='+U4MIN+'&&this.k<64){const T=layer.tag;layer.tag=[T[2],T[4],T[5],T[0],T[3],this.carry,T[6]];layer.u4Affine=true;layer.u4d=this.zword[this.m-1];}'+
  'super.affine.call(layer,tape,back);'],
];
