'use strict';
// ringhole (q648): U15 quotient trial + witness, rows 64..111, without logical 647 (f2 = top rank bit: t=5 in 64..95, t=4 in 96..111).
// Uses the deep rows' short packing: N = R*V+U is packed over [r without its top wire, u] (R < 2^(255-k) by I(k) at the general step),
// so r's top wire stays zero on taken lanes and hosts rank bit 4 (as their deep rows host rank 5 there). The packed top (u's top = 256)
// is the other short-packing host; lanes with it set are parked on r-top with take cleared (their 'choose'), exactly as in rows 0..63.
const LO=+(process.env.T648_LO||64),HI=+(process.env.T648_HI||111);
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('t648 anchor '+a.slice(0,70));s=s.replace(a,()=>b);};
 const anchor="      if(this.deep){\n        const short=this.r.slice(0,-1),free=this.r.at(-1),packed=short.concat(this.u),hi=packed.at(-1),H=this.uTrialRank(witness),low=Object.create(H),work=Object.create(H);";
 const R112=process.env.T648_R112==='1'; // OFF by default: the short-packing row-112 path computes a wrong quotient on rare lanes (fasteval shot 6596, biased rank 8 at row 112).
 // Row 112: its trial normally takes the non-coefficient-direction path (tag [n-top, v[k], f1|carry, pick], direction bit on dv[1] = 647).
 // Run it on the coefficient-direction path instead: direction -> carry -> v[k] ('moved'), short packing, rank bit 1 moves from v[k] to the packed top
 // (256, zero on active lanes; hi lanes are parked on r-top with take cleared), and the bands read dv[1] = v[k].
 if(R112)one("      if(!this.useCoefficientDirection){super.trial(tape,witness,back);return;}",
   "      if(!this.useCoefficientDirection&&this.k!==112){super.trial(tape,witness,back);return;}");
 one(anchor,String.raw`      if(!this.deep&&((this.k>=${LO}&&this.k<=${HI}&&this.k>=64&&this.k<=111)||(${R112?'true':'false'}&&this.k===112))){
        const short=this.r.slice(0,-1),free=this.r.at(-1),packed=short.concat(this.u),hi=packed.at(-1),H=this.uTrialRank(witness),low=Object.create(H),work=Object.create(H);
        const rank=H.tag.slice(),top=rank.length-1;
        if(this.k===112){if(rank.length!==4||rank[1]!==this.v[this.k])throw Error('t648 rank112 '+JSON.stringify(rank));rank[1]=hi;const dv=[this.dv[0],this.v[this.k]];low.dv=dv;work.dv=dv;
          // band [0,8] needs one more free wire than row 112's 17-wire quotient leaves: r's top (zero on active lanes; the parked hi lanes are
          // take-cleared, so every band write is identity for them and the band's inverses restore their marker).
          low.layouts=function(){const out=[];for(const [lo,hi] of [[0,8],[9,this.maxShift]]){const w=hi+6,W=w+1,spare=lo===0?[free]:this.n.slice(1,lo);
            const T=[...this.q,...spare.splice(0,Math.max(0,W+1-this.q.length))].slice(0,W+1),fr=[...this.q.slice(W+1),...spare];
            if(T.length!==W+1||fr.length<2)throw Error('t648 112 unfunded');const Hh=[...this.n.slice(this.m-w+1),fr[1]],Dd=[fr[0],...Hh];
            if(new Set([...T,...Dd]).size!==T.length+Dd.length)throw Error('t648 112 overlap');out.push({lo,hi,w,W,T,D:Dd,H:Hh,d0:fr[0]});}return out;};}
        else{if(!((rank.length===5&&rank[1]===hi)||(rank.length===6&&rank[4]===hi))||rank[top]!==647)throw Error('t648 rank '+this.k+' '+JSON.stringify(rank));rank[top]=free;}
        low.tag=rank;work.tag=rank;
        low.packedShort=true;low.n=[-23,...packed.slice(0,-1)];work.n=packed.slice(0,-1);if(H.u39Trial){rank[H.u6TrialSlot??1]=work.n.at(-1);}
        const choose=rv=>{const ops=[()=>this.toggle(tape,[this.g,this.take,hi],[],free),()=>this.toggle(tape,[this.g,free],[],this.take)];stepList(ops,rv,fn=>fn());};
        const setOne=()=>{if(!witness)this.toggle(tape,[this.g,this.take,hi],[],this.q[0]);};
        const pack=rv=>this.mixed(tape,short,this.v,this.u,[],rv);
        const norm=rv=>work.normalize(tape,rv),bias=rv=>this.inc(tape,rank,[],rv);
        const steps=[dirs,pack,moved,setOne,choose,norm,bias];
        for(const band of low.layouts())steps.push(rv=>witness?low.oddWitness(tape,band,rv):low.oddQuotient(tape,band,rv));
        steps.push(rv=>bias(!rv),rv=>norm(!rv),rv=>choose(!rv),rv=>moved(!rv),rv=>pack(!rv),dirs);
        stepList(steps,back,fn=>fn(back));return;
      }
`+anchor);
 return s;
};
