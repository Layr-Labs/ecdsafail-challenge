'use strict';
// q650 upper: quotient trial and witness of rows 0..111 without rank bit 1 (logical tags[1]=651). Apply after p650-probe3.js.
// Each trial runs passes in which bit 1 of the normalization rank (s, or s+1 in deep rows) is a compile-time constant.
// The rank register receives G(s) via the telescoped prefix ladder over the top maxShift bits of the normalized word
// (compressed rank for members of the pass, sentinel S1 otherwise), and the word is rotated by a barrel over the mixed tag.
// Gating: lanes on S1 that are taken are moved to S2 (one register bit, controlled by take) and take is cleared there,
// so every band write (all are take-controlled) is identity for them; undone exactly after the bands.
// Constant tag entries: -301 = 0, -302 = 1; mc/toggle/indicator handle them.
module.exports=[
 // constant controls in the multi-controlled gate
 ['    mc(cs,t,dirty) {\n        const n=cs.length;',
  '    mc(cs,t,dirty) {\n        if(cs.includes(-301))return;if(cs.includes(-302))cs=cs.filter(q=>q!==-302);\n        const n=cs.length;'],
 // constant / duplicate / contradictory literals in toggle
 ['    toggle(tape,positive,negative,target) {\n        const controls=[...positive,...negative];',
  `    toggle(tape,positive,negative,target) {
        if(positive.includes(-301)||negative.includes(-302))return;
        if(positive.includes(-302)||negative.includes(-301)||new Set(positive).size!==positive.length||new Set(negative).size!==negative.length){
            positive=[...new Set(positive.filter(q=>q!==-302))];negative=[...new Set(negative.filter(q=>q!==-301))];}
        if(positive.some(q=>negative.includes(q)))return;
        const controls=[...positive,...negative];`],
 // rank comparisons over tags with constant entries
 ['            this.constBelow(tape,this.tag,BigInt(j+1),controls,[target]);',
  '            this.cmpTag(tape,this.tag,BigInt(j+1),controls,[target]);'],
 // helpers
 ['    rankG(tape,wires,G){',
`    rankGH(tape,high,wires,G,ctl){
        if(!high.length){for(let k=0;k<wires.length;k++)if((G[0]>>k)&1)tape.out(NONE,ctl===undefined?NONE:ctl,wires[k]);return;}
        const n=high.length,d=tape.loan([...high,...wires,...(ctl===undefined?[]:[ctl])],n+1),coeff=Array.from({length:n+1},(_,i)=>i<n?G[i]^G[i+1]:G[n]);
        for(const x of high)tape.out(NONE,NONE,x);
        for(let rep=0;rep<2;rep++){
            tape.out(NONE,NONE,d[n]);
            for(let i=n-1;i>=0;i--)tape.out(high[i],d[i+1],d[i]);
            for(let i=0;i<=n;i++)for(let k=0;k<wires.length;k++)if((coeff[i]>>k)&1)tape.out(ctl===undefined?NONE:ctl,d[i],wires[k]);
            for(let i=0;i<n;i++)tape.out(high[i],d[i+1],d[i]);
        }
        for(const x of high)tape.out(NONE,NONE,x);
    }
    q650PassesS(tag,M,valueOf){
        const lg=tag.length,out=[],classes=[],vals=[];for(let s=0;s<=M;s++)vals.push(valueOf(s));
        if(new Set(vals).size!==vals.length)throw Error('q650 trial rank values collide '+[this.k,M]);
        const posB=[];tag.forEach((q,i)=>{if(i!==1)posB.push(i);});
        const encB=s=>{let y=0;posB.forEach((p,b)=>{if((vals[s]>>p)&1)y|=1<<b;});return y;};
        const hmB=posB.reduce((m,p,i)=>this.q650Helper(tag[p])?m|(1<<i):m,0);
        const adj=S=>{const u=new Set(S.map(encB)),W=posB.length;for(let y=0;y<(1<<W);y++){if(u.has(y))continue;for(let bb=0;bb<W;bb++){const z=y^(1<<bb);if(!u.has(z)&&(z&hmB))return true;}}return false;};
        for(const j of [0,1]){const S=[];for(let s=0;s<=M;s++)if(((vals[s]>>1)&1)===j)S.push(s);
            const extra=[];while(S.length&&!adj(S))extra.push(S.pop());
            classes.push({S,j});
            // overflow values share bit 1 = j: one extra class (few members leave free patterns), singletons only as fallback
            if(extra.length){if(adj(extra))classes.push({S:extra,j});else for(const m of extra)classes.push({S:[m],single:true});}}
        for(const c of classes){
            if(!c.S.length)continue;
            let tg,wires,enc;
            if(c.single){const v=vals[c.S[0]];tg=tag.map((q,i)=>((v>>i)&1)?-302:-301);wires=tag.filter((q,i)=>i!==1&&this.q650Helper(q)).slice(0,2);if(wires.length<2)throw Error('q650 singleton helpers '+this.k);enc=()=>0;}
            else{const pos=[];tg=tag.map((q,i)=>i===1?(c.j?-302:-301):q);wires=[];
                tag.forEach((q,i)=>{if(i!==1){wires.push(q);pos.push(i);}});
                enc=s=>{let y=0;pos.forEach((p,b)=>{if((vals[s]>>p)&1)y|=1<<b;});return y;};}
            const used=new Set(c.S.map(enc)),hm=wires.reduce((m,q,i)=>this.q650Helper(q)?m|(1<<i):m,0);let S1=-1,S2=-1,b=-1;
            for(let y=(1<<wires.length)-1;y>=0&&S1<0;y--){if(used.has(y))continue;
                for(let bb=0;bb<wires.length;bb++){const z=y^(1<<bb);if(!used.has(z)&&(z&hm)){S1=y;S2=z;b=bb;break;}}}
            if(S1<0)throw Error('q650 trial pass without two free patterns '+[this.k,M,lg]);
            const mem=new Set(c.S),G=[];for(let s=0;s<=M;s++)G.push(mem.has(s)?enc(s):S1);
            out.push({tag:tg,wires,G,S1,S2,b});
        }
        return out;
    }
    q650Helper(q){return q>=642&&q<=656&&q!==648&&q!==649;}
    q650Fold(tape,ps,back){
        const W=ps.wires,cube=(pat,skip)=>{const y=[],n=[];W.forEach((q,b)=>{if(b===skip)return;((pat>>b)&1?y:n).push(q);});return {y,n};};
        const a=cube(ps.S1,ps.b),c=cube(ps.S2,-1);
        const A=()=>this.toggle(tape,[this.g,this.take,...a.y],a.n,W[ps.b]),B=()=>this.toggle(tape,[this.g,...c.y],c.n,this.take);
        if(!back){A();B();}else{B();A();}
    }
    rankG(tape,wires,G){`],
 // pass-split trial (UnguardedGeneral, rows with the coefficient-direction lease)
 [`      const dirs=()=>temp.direction(tape);
      if(this.deep){`,
`      const dirs=()=>temp.direction(tape);
      const passes=(Hb,nWord,valueOf,shiftBack)=>{
        const M=this.maxShift,high=nWord.slice(nWord.length-M),out=[];
        for(const ps of this.q650PassesS(Hb.tag,M,valueOf)){
          const L=Object.create(Hb);L.tag=ps.tag;
          const Gbl=Array.from({length:M+1},(_,bl)=>ps.G[M-bl]),rot=[...nWord.slice(1),nWord[0]];
          const N=rv=>{
            if(!rv){this.rankGH(tape,high,ps.wires,Gbl,this.take);this.barrel(tape,nWord,ps.tag,true,false);
              if(shiftBack)this.permute(tape,nWord,rot,[],false);this.q650Fold(tape,ps,false);}
            else{this.q650Fold(tape,ps,true);if(shiftBack)this.permute(tape,nWord,rot,[],true);
              this.barrel(tape,nWord,ps.tag,true,true);this.rankGH(tape,high,ps.wires,Gbl,this.take);}
          };
          out.push(rv=>N(rv));
          for(const band of L.layouts())out.push(rv=>witness?L.oddWitness(tape,band,rv):L.oddQuotient(tape,band,rv));
          out.push(rv=>N(!rv));
        }
        return out;
      };
      if(this.deep&&this.tag.length>=2&&this.uTrialRank(witness).tag[1]===651){
        const short=this.r.slice(0,-1),free=this.r.at(-1),packed=short.concat(this.u),hi=packed.at(-1),H=this.uTrialRank(witness),low=Object.create(H),work=Object.create(H);
        const rank=H.tag.slice();rank[4]=hi;rank[5]=free;low.tag=rank;work.tag=rank;
        low.packedShort=true;low.n=[-23,...packed.slice(0,-1)];work.n=packed.slice(0,-1);
        const choose=rv=>{const ops=[()=>this.toggle(tape,[this.g,this.take,hi],[],free),()=>this.toggle(tape,[this.g,free],[],this.take)];stepList(ops,rv,fn=>fn());};
        const setOne=()=>{if(!witness)this.toggle(tape,[this.g,this.take,hi],[],this.q[0]);};
        const pack=rv=>this.mixed(tape,short,this.v,this.u,[],rv);
        const mask=(1<<rank.length)-1;
        const steps=[dirs,pack,moved,setOne,choose,...passes(low,work.n,s=>(s+1)&mask,true),
          rv=>choose(!rv),rv=>moved(!rv),rv=>pack(!rv),dirs];
        stepList(steps,back,fn=>fn(back));return;
      }
      if(!this.deep&&this.uTrialRank(witness).tag[1]===651){
        const H=this.uTrialRank(witness);
        const steps=[dirs,rv=>this.packNumber(tape,rv),moved,...passes(H,H.n,s=>s,false),
          rv=>moved(!rv),rv=>this.packNumber(tape,!rv),dirs];
        stepList(steps,back,fn=>fn(back));return;
      }
      if(this.deep){`],
];
