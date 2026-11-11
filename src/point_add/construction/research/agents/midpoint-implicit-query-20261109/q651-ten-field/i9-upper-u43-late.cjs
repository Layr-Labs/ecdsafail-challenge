'use strict';
exports.select=w=>w.kind==='trial'&&w.args[0]===true&&w.k>=96&&w.k<=111?{evict:642,reason:'U43 split-band retained rank code'}:null;
exports.upper=s=>{
 if(!s.includes('    u35Direction(tape){')) s=require('./i9-upper-u35-direction.cjs').upper(s);
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U43 anchor '+a);s=s.replace(a,()=>b);};
 one('      if(!witness&&this.k<=112&&!this.u30Trial){',`      if(witness&&this.k>=96&&this.k<=111&&!this.u43Late){
        const H=Object.create(this),tp=Object.create(tape);H.u43Late=true;H.u35DirectionOnly=true;
        tp.ids=tape.ids.filter(q=>q!==642);tp.loan=(used,n)=>tape.loan([...used,642],n);
        tp.out=(a,b,t)=>{if([a,b,t].includes(642))throw Error('U43 pick operand '+[this.k,a,b,t]);tape.out(a,b,t);};
        H.trial(tp,witness,back);return;
      }
      if(!witness&&this.k<=112&&!this.u30Trial){`);
 one('    u17Normalize(tape,back){',`    u17Normalize(tape,back){
      if(this.u43Late){this.u43Normalize(tape,back);return;}`);
 one('    u11Band(tape,B,back){',`    u11Band(tape,B,back){
      if(this.u43Late){this.u43Witness(tape,B,back);return;}`);
 one('        const K=this.maxShift,out=[];',`
        const K=this.maxShift,out=[];`);
 one('      let deposit=true;',`      if(this.u43Band){guards.length=0;for(const p of this.u43Guards())guards.push({yes:[this.g,this.take,...p.yes],no:p.no});}
      let deposit=true;`);
 one('      if(this.inUpperHalf==null)throw Error(\'unresolved band\');',`      if(this.u43Band){const base=yes.filter(q=>q!==-19);for(const p of this.u43Guards()){
        const yy=[...new Set([...base,...p.yes])],nn=[...new Set([...no,...p.no])];
        if(!yy.some(q=>nn.includes(q)))super.toggle(tape,yy,nn,target);
      }return;}
      if(this.inUpperHalf==null)throw Error('unresolved band');`);
 one('class UnguardedGeneral extends OddEstimateGeneral {',`class UnguardedGeneral extends OddEstimateGeneral {
    u43Layouts(){
      const K=this.maxShift,out=[],protectedCells=this.n.slice(6,8);
      for(const [lo,hi]of [[0,7],[8,K-2],[K-1,K]]){
        const w=hi+6,W=w+1,spare=this.n.slice(0,lo).filter(q=>!protectedCells.includes(q));
        const T=[...this.q,...spare.splice(0,Math.max(0,W+1-this.q.length))].slice(0,W+1);
        const free=[...this.q.slice(W+1),...spare];
        if(T.length!==W+1||free.length<2)throw Error('U43 unfunded band '+[this.k,lo,hi]);
        const H=[...this.n.slice(this.m-w+1),free[1]],D=[free[0],...H];
        if(new Set([...T,...D]).size!==T.length+D.length)throw Error('U43 band aliases');
        out.push({lo,hi,w,W,T,D,H,d0:free[0]});
      }return out;
    }
    u43Guards(){return this.uLess(this.u43Band.hi+1).concat(this.uLess(this.u43Band.lo));}
    u43Normalize(tape,back){
      const H=this,n=this.n,top=n.at(-1),C={c:this.qtop,x:n[6],y:n[7]},tag=this.tag.slice();
      tag[4]=this.carry;tag[3]=C.c;
      const each=(a,rv,fn)=>(rv?a.slice().reverse():a).forEach(fn);
      const high=rv=>each([4,3],rv,j=>{
        const d=1<<j,t=tag[j],seq=[()=>H.toggle(tape,[H.take],n.slice(-d),t),rr=>H.permute(tape,n,n.slice(-d).concat(n.slice(0,-d)),[H.take,t],rr)];each(seq,rv,f=>f(rv));
      });
      const code=rv=>each([[1,6],[3,10]],rv,([a,b])=>H.u6Transpose(tape,[H.carry,C.c,C.x,C.y],a,b,[H.take],[],rv));
      const rotate=(word,d,t,rv)=>{
        const short=word.filter(q=>q!==C.x&&q!==C.y);
        const seq=[()=>tape.out(NONE,NONE,C.c),rr=>H.permute(tape,word,word.slice(-d).concat(word.slice(0,-d)),[H.take,t,C.c],rr),()=>tape.out(NONE,NONE,C.c),rr=>H.permute(tape,short,short.slice(-d).concat(short.slice(0,-d)),[H.take,t,C.c],rr)];each(seq,rv,f=>f(rv));
      };
      const lower=rv=>each([2,1],rv,j=>{const d=1<<j,t=tag[j];each([()=>H.toggle(tape,[H.take],n.slice(-d),t),rr=>rotate(n,d,t,rr)],rv,f=>f(rv));});
      const last=rv=>each([()=>tape.out(NONE,H.take,top),rr=>rotate(n.slice(0,-1),1,top,rr),()=>H.toggle(tape,[H.take,top],[],n[0])],rv,f=>f(rv));
      each([high,code,lower,last],back,f=>f(back));
    }
    u43Witness(tape,B,back){
      if(B.lo){this.u43HighWitness(tape,B,back);return;}
      const H=Object.create(this),host=B.T.at(-1),x=this.n[6],y=this.n[7],frames=new Set(),tp=Object.create(tape),virtual=[-4303,-4304],code=[host,x,y];
      H.tag=this.tag.slice();H.tag[3]=virtual[0];H.tag[4]=virtual[1];H.u11Witness=false;
      const expr=q=>{
        if(!virtual.includes(q))return [{yes:q===NONE?[]:[q],no:[]}];
        const terms=q===virtual[0]?[{yes:[host],no:[x]}]:[{yes:[host,x],no:[]},{yes:[host,y],no:[]}];
        if(frames.has(q))terms.push({yes:[],no:[]});return terms;
      };
      tp.loan=(used,n)=>tape.loan([...used,...code,642],n);
      tp.out=(a,b,t)=>{
        if(virtual.includes(t)){if(a!==NONE||b!==NONE)throw Error('U43 nonlinear rank write');if(frames.has(t))frames.delete(t);else frames.add(t);return;}
        if(code.includes(t))throw Error('U43 protected code '+[this.k,a,b,t]);
        if(!virtual.includes(a)&&!virtual.includes(b)){tape.out(a,b,t);return;}
        for(const A of expr(a))for(const B of expr(b)){const yes=[...new Set([...A.yes,...B.yes])],no=[...new Set([...A.no,...B.no])];if(!yes.some(q=>no.includes(q)))H.toggle(tape,yes,no,t);}
      };
      const swap=rv=>this.permute(tape,[this.qtop,host],[host,this.qtop],[],rv);
      swap(false);H.u39Divisor(tp,B,(J,rv)=>J.u11Predicate(tp,B),back);swap(true);
      if(frames.size)throw Error('U43 unclosed rank frames');
    }
    u43HighWitness(tape,B,back){
      const H=this,host=B.T.at(-1),x=this.n[6],y=this.n[7],top=this.n.at(-1),vtop=-4310,vhigh=-4311,topT=-1101;
      const T=B.T.slice(0,-1).concat(topT),D=B.D.map(q=>q===top?vtop:q===y?vhigh:q),word=D.slice(1);
      const flag=this.dv[0],phase=this.measureTarget===flag,target=phase?this.zword.at(-1):flag;
      const swap=rv=>this.permute(tape,[this.qtop,host],[host,this.qtop],[],rv);
      swap(false);
      const nodes=[null,null],unique=new Map(),cache=new Map();
      const mk=(v,l,h)=>{if(l===h)return l;const k=v+':'+l+':'+h;let id=unique.get(k);if(id===undefined){id=nodes.length;nodes.push({v,l,h});unique.set(k,id);}if(nodes.length>1000000)throw Error('U43 BDD node cap');return id;};
      const V=q=>mk(q,0,1),op=(kind,a,b)=>{
        if(a>b)[a,b]=[b,a];if(kind==='x'){if(a===0)return b;if(a===b)return 0;}else{if(a===0||a===b)return a;if(a===1)return b;}
        if(a<2&&b<2)return kind==='x'?a^b:a&b;
        const k=kind+':'+a+':'+b;if(cache.has(k))return cache.get(k);
        const av=a<2?Infinity:nodes[a].v,bv=b<2?Infinity:nodes[b].v,v=Math.min(av,bv);
        const r=mk(v,op(kind,av===v?nodes[a].l:a,bv===v?nodes[b].l:b),op(kind,av===v?nodes[a].h:a,bv===v?nodes[b].h:b));cache.set(k,r);return r;
      };
      const xor=(a,b)=>op('x',a,b),and=(a,b)=>op('a',a,b),coCache=new Map();
      const co=(a,q,b)=>{if(a<2||nodes[a].v>q)return a;const n=nodes[a];if(n.v===q)return b?n.h:n.l;const k=a+':'+q+':'+b;if(coCache.has(k))return coCache.get(k);const r=mk(n.v,co(n.l,q,b),co(n.h,q,b));coCache.set(k,r);return r;};
      const support=a=>{const out=new Set(),seen=new Set(),walk=id=>{if(id<2||seen.has(id))return;seen.add(id);const n=nodes[id];out.add(n.v);walk(n.l);walk(n.h);};walk(a);return [...out];};
      const cubes=a=>{const out=[],walk=(id,yes,no)=>{if(id===0)return;if(id===1){out.push({yes,no});return;}const n=nodes[id];walk(n.l,yes,no.concat(n.v));walk(n.h,yes.concat(n.v),no);};walk(a,[],[]);if(out.length>10000)throw Error('U43 BDD cube cap');return out;};
      const vals=new Map([[vtop,1],[vhigh,0]]);
      const expr=q=>vals.has(q)?vals.get(q):q===NONE?1:V(q);
      const raw=Object.create(tape);raw.loan=(used,n)=>tape.loan([...used,host,x,y,top,flag,target,642,...Array.from(vals.values()).flatMap(support)],n);
      let deposit=true;
      const apply=(yes,no,t)=>{
        let term=1;for(const q of yes)term=and(term,expr(q));for(const q of no)term=and(term,xor(1,expr(q)));
        if(t===topT){if(!deposit)return;term=and(term,and(V(this.g),and(V(this.take),V(host))));t=target;}
        if(vals.has(t)){vals.set(t,xor(vals.get(t),term));return;}
        if([host,x,y,top].includes(t))throw Error('U43 code write '+t);
        if(support(term).includes(t))throw Error('U43 high self-target '+t);
        for(const [q,e]of vals)vals.set(q,xor(e,and(xor(co(e,t,0),co(e,t,1)),term)));
        for(const c of cubes(term))H.toggle(raw,c.yes,c.no,t);
      };
      const incOps=(a,cs=[],negative=[])=>a.map((t,i)=>({yes:cs.concat(a.slice(0,i)),no:negative,t})).reverse();
      const run=(ops,rv)=>stepList(ops,rv,o=>apply(o.yes,o.no,o.t));
      const round=[];
      round.push(...incOps(word).reverse());round.push(...incOps(word.slice(1),[this.dv[1]]));
      run(round,false);
      const pre=incOps(T);
      for(let i=T.length-2;i>=0;i--){
        const src=D.slice(1,T.length-i),dst=T.slice(i+1);
        for(let j=0;j<src.length;j++)pre.push(...incOps(dst.slice(j),[T[i],src[j]]));
      }
      for(const t of T)pre.push({yes:[],no:[],t});
      for(let j=0;j<T.length-B.w;j++){
        const yes=[],no=[];[top,this.borrow,this.carry].forEach((q,i)=>((j>>i)&1?yes:no).push(q));
        // In the high band count>=8, so count=0 or1 cannot deposit; nevertheless
        // preserve the full lower-register donor compute/inverse by decoded controls.
        const rank3=-4303,rank4=-4304;
        // Both increments have width <=2: direct rank-zero guard means marker=0.
        no.push(host);pre.push(...incOps(T.slice(B.w+j),yes,no));
      }
      const enable=()=>H.toggle(raw,[H.g,H.take,host],[],target);
      enable();run(pre,false);if(phase)tape.z(target);deposit=phase;run(pre,true);
      if(phase){enable();tape.z(target);tape.z(flag);}
      run(round,true);
      if(vals.get(vtop)!==1||vals.get(vhigh)!==0)throw Error('U43 virtual divisor not restored');
      swap(true);
    }

`);
 return s;
};
