'use strict';
exports.upper=s=>{
 const one=(a,b)=>{if(s.split(a).length!==2)throw Error('U4 anchor '+a);s=s.replace(a,()=>b);};
 one('this.ids=this.ids.filter(q=>q<652||q>656);','this.ids=this.ids.filter(q=>q<651||q>656);');
 one('if(!this.r)return undefined;const wide=', 'if(!this.r)return undefined;if(this.u40Probe&&(this.k===62||this.k===95))return this.half+1;const wide=');
 one('layer.tags=this.tags.slice();layer.tags[this.tag.length-2]=q;', 'layer.u40Probe=this.k<=95&&this.k!==63;layer.tags=this.tags.slice();layer.tags[this.tag.length-2]=q;');
 one('        const base=this.ab,w=this.half+1;\n', '        if(this.u40Probe){this.u40Sign(tape,target);return;}\n        const base=this.ab,w=this.half+1;\n');
 one('class UnguardedGeneral extends OddEstimateGeneral {', `class UnguardedGeneral extends OddEstimateGeneral {
    u40Tape(tape){
      if(!this.u40Tag)return tape;
      const H=this,low=this.u40Low,tag=this.u40Tag,tp=Object.create(tape);
      tp.ids=tape.ids.filter(q=>!tag.includes(q));
      tp.out=(a,b,t)=>{
        if(t===low)throw Error('U4 coefficient low written');
        const cs=[a,b].filter(q=>q!==NONE);
        if(!cs.includes(low)){tape.out(a,b,t);return;}
        if(H.u40NoCode)return;
        const controls=[...tag,...cs.filter(q=>q!==low)];
        tape.mc(controls,t,tape.loan([...controls,t],Math.max(1,controls.length-2)));
      };
      return tp;
    }
    mixed(tape,q,v,rem,controls,back){
      super.mixed(this.u40Tag&&v[0]===this.u40Low?this.u40Tape(tape):tape,q,v,rem,controls,back);
    }
    constBelow(tape,word,limit,controls,targets){
      if(this.u40FixedRank!==undefined&&word.length===0){if(BigInt(this.u40FixedRank)<limit)this.cnotList(tape,controls,targets);return;}
      super.constBelow(tape,word,limit,controls,targets);
      if(this.u40Tag&&!this.u40NoCode&&word.length===this.u40Tag.length&&word.every((q,i)=>q===this.u40Tag[i])&&limit>0n&&limit<=BigInt((1<<word.length)-1))
        for(const t of targets)this.toggle(tape,[...controls,...word],[],t);
    }
    barrel(tape,word,tag,left,back){
      if(this.u40FixedRank!==undefined){const k=this.u40FixedRank%word.length,src=left?word.slice(-k).concat(word.slice(0,-k)):word.slice(k).concat(word.slice(0,k));this.permute(tape,word,src,[],back);return;}
      if(!this.u40Tag||this.u40NoCode){super.barrel(tape,word,tag,left,back);return;}
      const k=((1<<tag.length)-1)%word.length;
      const src=left?word.slice(k).concat(word.slice(0,k)):word.slice(-k).concat(word.slice(0,-k));
      const ops=[rv=>super.barrel(tape,word,tag,left,rv),rv=>this.permute(tape,word,src,tag,rv)];
      stepList(ops,back,fn=>fn(back));
    }
    u40Sign(tape,target){
      if(this.k===64&&!this.u40Split){this.u40SplitSign(tape,target);return;}
      const base=this.ab,w=this.half+1,free=this.r.length-base;
      const tag=this.probeTag(base,this.tags.slice(0,Math.floor(Math.log2(free))+1),target).map((q,i)=>i===2?this.carry:i===1?this.pick:q);
      if(!this.u40NoCode&&free===(1<<tag.length)-1)throw Error('U4 no reserved rank '+this.k);
      const S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const H=Object.create(this);H.u40Low=S[0];H.u40Tag=tag.slice();H.u40Tag[1]=S[0];
      const swap=()=>{tape.out(NONE,this.pick,S[0]);tape.out(NONE,S[0],this.pick);tape.out(NONE,this.pick,S[0]);};
      // Exact transposition (rank=0,low=1) <-> (rank=all-ones,low=0).
      const recode=()=>{
        const ports=[...tag,S[0]],values=ports.map((q,i)=>i===tag.length?1:0),edges=[];
        for(let i=0;i<ports.length;i++){
          const yes=[],no=[];for(let j=0;j<ports.length;j++)if(j!==i)(values[j]?yes:no).push(ports[j]);
          edges.push(()=>this.toggle(tape,yes,no,ports[i]));values[i]^=1;
        }
        for(const fn of edges)fn();for(let i=edges.length-2;i>=0;i--)edges[i]();
      };
      const lease=rv=>stepList(this.u40NoCode?[swap]:[recode,swap],rv,fn=>fn());
      const seq=[()=>this.rank(tape,tag),rv=>super.barrel(tape,S,tag,true,rv),lease,
        rv=>this.inc(tape,this.r,[],!rv),rv=>H.parkTail(tape,D,H.u40Tag,rv),()=>this.cnotList(tape,[],D),
        rv=>H.u40Tape(tape).add(a,D,[],this.carry,rv),rv=>H.alignedMix(tape,a,D,H.u40Tag,rv),rv=>H.barrel(tape,this.r,H.u40Tag,false,rv)];
      stepList(seq,false,fn=>fn(false));
      (this.u40NoCode?H:this).u40Deposit(tape,target,S,word);
      stepList(seq,true,fn=>fn(true));
    }
    u40Deposit(tape,target,S,word){
      const high=this.u40ExcludedTop,c=high===undefined?this.ctrl:[...this.ctrl,high];
      const write=cs=>{
        if(high!==undefined)tape.out(NONE,NONE,high);
        this.toggle(tape,cs,[],target);tape.out(NONE,NONE,S.at(-1));this.constBelow(tape,word,this.centeredFree?this.p-(1n<<BigInt(this.k)):this.p,[...cs,S.at(-1)],[target]);tape.out(NONE,NONE,S.at(-1));
        if(high!==undefined)tape.out(NONE,NONE,high);
      };
      phaseDeposit(this,tape,target,()=>{
        write(c);
        if(this.u40NoCode){
          for(const q of this.u40Tag)tape.out(NONE,NONE,q);
          write([...c,...this.u40Tag]);
          for(const q of this.u40Tag)tape.out(NONE,NONE,q);
        }
      });
    }
    u40SplitSign(tape,target){
      const H=Object.create(this);H.u40Split=true;H.u40NoCode=true;
      H.u40Sign(tape,target);
      const F=Object.create(this);F.u40FixedRank=0;F.take=this.tags[0];F.ctrl=[this.g,F.take];
      const select=()=>this.toggle(tape,this.ctrl,this.r.slice(this.ab),F.take);
      select();F.u40FixedSign(tape,target);select();
      // Two phaseDeposit calls each include incoming target phase; retain exactly one.
      if(this.measureTarget===target)tape.z(target);
    }
    u40FixedSign(tape,target){
      const base=this.ab,w=this.half+1,tag=[],S=this.A.slice(0,w),a=S.slice(0,-1),D=this.zword.slice(0,w-1),word=[...this.r.slice(0,base),...D];
      const seq=[rv=>this.barrel(tape,S,tag,true,rv),rv=>this.inc(tape,this.r,[],!rv),
        rv=>this.parkTail(tape,D,tag,rv),()=>this.cnotList(tape,[],D),rv=>tape.add(a,D,[],this.carry,rv),
        rv=>this.alignedMix(tape,a,D,tag,rv),rv=>this.barrel(tape,this.r,tag,false,rv)];
      stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));
    }
`);
 one('      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);', '      const ops=dirtyDigit(S,z.slice(0,-1),z.at(-1),this.take,loan);\n      if(this.u40Tag)tape=this.u40Tape(tape);');
 return s;
};
