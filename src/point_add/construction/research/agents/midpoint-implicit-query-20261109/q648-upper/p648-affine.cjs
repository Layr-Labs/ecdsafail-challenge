'use strict';
// ringhole (q648): U15 early affine (rows 0..63, u12 code) without logical 647 (f2 = rank bit 6). Apply after U15 (UEXTRA overlay).
// Rank bit 6 moves into the normalized coefficient's bit A2, extending the u12 code by one wire:
//  - during normalization rank6 sits on r's top wire (zero on taken lanes at the general step, invariant I(k)); every write is take-gated;
//  - after u12's recode (counts 0/1 -> extra=1 codes), count 2 is recoded too: (extra,pick,A127) 0,0,1 -> 1,1,0 (pick = rank3 marker);
//  - code lanes (extra=1) move the real B2 from A2 to A128 (their rank4 is 0); then rank6 moves from r-top into A2 on extra=0 lanes
//    (counts >= 3 have B2 = 0). So A2 = rank6 on every lane;
//  - A2 joins the virtual hosts of the implicit-top digits: B2 = extra & A128;
//  - rank compares and barrels decode: extra=1 & pick=0 & v=0 -> 0, extra=1 & v=1 -> 1, extra=1 & pick=1 -> 2; extra=0 -> binary with A2 = bit 6.
// At the affine exit r's top is zero again (z < R < 2^(255-k)), so the inverse moves rank6 back for norm^-1.
const LO=+(process.env.A648_LO||0),HI=+(process.env.A648_HI||63),POOL=process.env.A648_NOPOOL?0:1;
// Rows 64..111: their tag there is [A127, v[k], A128, pick, 256, f2] (64..95) or [v[k], A128, 256, pick, f2] (96..111). The u12 code of rows
// 0..63 hosts one more rank bit on the normalized low zero A0 (A1 = code flag for counts 0/1), so switching these rows to u12 with
// tag [A0, A127, v[k], pick, A128, 256].slice(0, bits) drops f2 (and 256 at 96..111) without new machinery.
const BLO=+(process.env.B648_LO||64),BHI=+(process.env.B648_HI||123);
// Rows 120..123 (original body, tag [A128, 256, f2], M <= 7) take the same u12 switch with tag [A0, A127, v[k]].
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('a648 anchor '+a.slice(0,70));s=s.replace(a,()=>b);};
 one("layer.tag[4]=this.A[this.half];super.affine.call(layer,tape,back);",
  "layer.tag[4]=this.A[this.half];if(this.k>="+LO+"&&this.k<="+HI+"&&this.k<64&&layer.u12){if(layer.tag.length!==7||layer.tag[6]!==647)throw Error('a648 tag '+this.k+' '+JSON.stringify(layer.tag));layer.tag[6]=this.A[2];layer.u648=true;}super.affine.call(layer,tape,back);");
 one("    u12Normalize(tape,a,back){\n",String.raw`    u648Normalize(tape,a,back){
      const H=Object.create(this),carry=this.carry,top=a.at(-1),low=a[0],extra=a[1],a2=a[2],rtop=this.r.at(-1),take=this.take,T=this.tag;
      if(T[6]!==a2||T[0]!==low||T[1]!==top||T.length!==7)throw Error('u648 ports '+this.k);
      H.tag=T.slice();H.tag[1]=carry;H.tag[6]=rtop;
      const norm=rv=>stepList(split(1,H.tag.length).reverse(),rv,j=>{
        const k=1<<j,orig=a.slice(-k).concat(a.slice(0,-k)),bit=H.tag[j];
        const seq=[()=>H.toggle(tape,[H.take],a.slice(-k),bit),rr=>H.permute(tape,a,orig,[H.take,bit],rr)];stepList(seq,rv,fn=>fn(rv));
      });
      const last=rv=>{
        const lower=a.slice(0,-1),orig=lower.slice(-1).concat(lower.slice(0,-1));
        const seq=[rr=>this.permute(tape,[top,carry],[carry,top],[take],rr),()=>tape.out(NONE,take,carry),
          rr=>this.permute(tape,lower,orig,[take,carry],rr),()=>this.toggle(tape,[take,carry],[],low),
          rr=>this.permute(tape,[carry,low],[low,carry],[take],rr)];stepList(seq,rv,fn=>fn(rv));
      };
      const recode=rv=>{
        const map=new Map();
        for(let x=0;x<2;x++)for(let y=0;y<2;y++)map.set(x+16*y,16+2*x+4*y);
        for(let y=0;y<2;y++)map.set(2+16*y,16+8+2*y);
        for(let c=2;c<8;c++)map.set(2*c,2*c);
        const incoming=new Set(map.values());
        for(const start of [...map.keys()])if(!incoming.has(start)){let at=start;while(map.has(at))at=map.get(at);map.set(at,start);}
        const seen=new Set(),swaps=[];
        for(const start of map.keys())if(!seen.has(start)){const cycle=[];let at=start;while(!seen.has(at)){seen.add(at);cycle.push(at);at=map.get(at);}
          for(let i=1;i<cycle.length;i++)swaps.push([cycle[0],cycle[i]]);}
        const ports=[carry,low,top,T[2],extra],no=[T[3],T[4],T[5],rtop];
        stepList(swaps,rv,([x,y])=>this.u6Transpose(tape,ports,x,y,[take],no,false));
      };
      const pick=T[3],rest=[T[4],T[5],rtop];
      const c2=rv=>{
        const before=()=>this.toggle(tape,[take,top],[low,T[2],pick,...rest,extra],carry);
        const after=()=>this.toggle(tape,[take,extra,pick],[low,top,T[2],...rest],carry);
        const flip=()=>{tape.out(NONE,carry,extra);tape.out(NONE,carry,pick);tape.out(NONE,carry,top);};
        stepList([before,flip,after],rv,fn=>fn());
      };
      const mv=()=>{this.toggle(tape,[take,rtop],[extra],a2);this.toggle(tape,[take,a2],[extra],rtop);this.toggle(tape,[take,rtop],[extra],a2);};
      // code lanes (extra=1, counts 0..2): rank4 = 0, so the real B2 moves from A2 to A128 (weight 16 instead of 64 in the physical rank).
      const b2=rv=>this.permute(tape,[a2,T[4]],[T[4],a2],[take,extra],rv);
      stepList([norm,last,recode,c2,b2,()=>mv()],back,fn=>fn(back));
    }
    u12Normalize(tape,a,back){
      if(this.u648){this.u648Normalize(tape,a,back);return;}
`);
 one("      if(!this.u12){super.indicator(tape,j,kind,controls,target);return;}\n",
 String.raw`      if(!this.u12){super.indicator(tape,j,kind,controls,target);return;}
      if(this.u648){
        super.indicator(tape,j,kind,controls,target);
        const pred=c=>kind==='eq'?c===j:kind==='gt'?c>j:c<=j,T=this.tag,extra=this.A[1];
        // [true rank, fixed tag bits, free tag bits]; on code lanes tag bit 4 (A128) is the real B2, bits 5 and 6 are zero.
        for(const [rank,fixed,free] of [[0,{2:0,3:0},[0,1,4]],[1,{0:null,1:0,2:1,3:0},[0,4]],[2,{0:0,1:0,2:0,3:1},[4]]]){
          for(let y=0;y<(1<<free.length);y++){
            const bit=i=>{const f=free.indexOf(i);if(f>=0)return (y>>f)&1;if(i in fixed&&fixed[i]!==null)return fixed[i];return 0;};
            let phys=0;for(let i=0;i<7;i++)phys+=bit(i)<<i;
            if(pred(phys)===pred(rank))continue;
            const yes=[...controls,extra],no=[];for(let i=0;i<7;i++)(bit(i)?yes:no).push(T[i]);
            this.toggle(tape,yes,no,target);
          }
        }
        return;
      }
`);
 one("      if(!this.u12){super.guardedBarrel(tape,word,left,back);return;}\n",
 String.raw`      if(!this.u12){super.guardedBarrel(tape,word,left,back);return;}
      if(this.u648){
        const T=this.tag,extra=this.A[1],c=this.ctrl,cy=this.carry;
        stepList(split(0,T.length),back,j=>{
          const k=(1<<j)%word.length;if(!k)return;
          const origin=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));
          const mark=()=>{
            if(j===5||j===6)this.toggle(tape,[...c,T[j]],[],cy);else this.toggle(tape,[...c,T[j]],[extra],cy);
            if(j===0)this.toggle(tape,[...c,extra,T[2]],[],cy);
            if(j===1)this.toggle(tape,[...c,extra,T[3]],[],cy);
          };
          mark();this.permute(tape,word,origin,[cy],back);mark();
        });
        return;
      }
`);
 one("const H=this,tag=this.tag,extra=this.A[1],host=this.A.slice(0,2),tp=Object.create(tape);",
     "const H=this,tag=this.tag,extra=this.A[1],host=this.A.slice(0,this.u648?3:2),tp=Object.create(tape);");
 one("const base=[[cube([extra,tag[0]],[tag[2]])],[cube([extra,tag[1]],[tag[2]]),cube([extra,tag[2],tag[0]])]];",
     "const base=[[cube([extra,tag[0]],[tag[2]])],[cube([extra,tag[1]],[tag[2]]),cube([extra,tag[2],tag[0]])]];if(H.u648)base.push([cube([extra,tag[4]])]);");
 one("tp.u12Check=()=>{for(let i=0;i<2;i++)","tp.u12Check=()=>{for(let i=0;i<base.length;i++)");
 one("      if(!this.deep){super.affine.call(H,tape,back);return;}",
  "      if(this.k>="+BLO+"&&this.k<="+BHI+"&&((this.k>=64&&this.k<=111)||(this.k>=120&&this.k<=123))){const n=H.tag.length;if(n<3||n>6||(n<5&&this.k<120))throw Error('b648 tag '+this.k);"+
  "H.tag=[this.A[0],this.A[this.half-1],this.v[this.k],this.pick,this.A[this.half],256].slice(0,n);H.u3Affine=true;H.u38Implicit=true;H.u12=true;H.u37Slot=undefined;H.u6TopSlot=undefined;if(this.k>=120){H.rankHost=this.pick;H.digit=this.digitDirty;}}\n"+
  "      if(!this.deep){super.affine.call(H,tape,back);return;}");
 if(POOL)one("this.ids=this.ids.filter(q=>q!==650&&q!==651);","this.ids=this.ids.filter(q=>q!==650&&q!==651&&q!==647);");
 return s;
};
