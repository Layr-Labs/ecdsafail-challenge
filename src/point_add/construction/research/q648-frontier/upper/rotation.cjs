'use strict';

// Compute the activation cutoff from the actual rank representation. The
// ordinary inequality and its exceptional rank cubes are both observable in
// the lowerer's public primitives. Test every code, including unused codes.
function tailCutoffPlan(owner,tape,tag,n,kind,flag){
    const wires=[],slots=new Map(),column=[];
    function slot(w){if(!slots.has(w)){slots.set(w,wires.length);wires.push(w);}return slots.get(w);}
    const probe=Object.create(owner),grab=Object.create(tape);
    let expr;
    const term=(pos,neg)=>{
        let yes=0,no=0;
        for(const w of pos)yes|=1<<slot(w);
        for(const w of neg)no|=1<<slot(w);
        expr.push(x=>(x&yes)===yes&&!(x&no));
    };
    probe.toggle=(t,yes,no,dest)=>{if(t!==grab||dest!==flag)throw Error('tail cutoff toggle');term(yes,no);};
    probe.cnotList=(t,cs,word)=>{if(t!==grab||word.length!==1||word[0]!==flag)throw Error('tail cutoff list');term(cs,[]);};
    grab.frontierThreshold=(word,limit,cs,dest)=>{
        if(cs.length||dest.length!==1||dest[0]!==flag)throw Error('tail cutoff predicate');
        const positions=word.map(slot);
        expr.push(x=>{
            let rank=0;for(let b=0;b<positions.length;b++)rank|=((x>>positions[b])&1)<<b;
            return rank<Number(limit);
        });
    };
    for(let j=1;j<=n;j++){
        expr=[];
        if(kind==='sign'){
            term([],[]);probe.constBelow(grab,tag,BigInt(j),[],[flag]);
        }else probe.indicator(grab,j-1,'gt',[],flag);
        column.push(expr);
    }
    if(wires.length>10||wires.some(q=>q<0||q===flag||q===tape.one))return null;
    const size=1<<wires.length,values=new Uint16Array(size);
    for(let x=0;x<size;x++){
        let count=0,closed=false;
        for(const tests of column){
            let on=false;for(const test of tests)if(test(x))on=!on;
            if(on&&closed)return null;
            if(on)count++;else closed=true;
        }
        values[x]=count;
    }
    const masks=[];
    for(let b=0;1<<b&&1<<b<=n;b++){
        const input=Array.from(values,c=>(c>>>b)&1);
        const cubes=tailBooleanCubes(input,wires.length);
        for(let x=0;x<size;x++){
            let actual=0;for(const [pos,neg] of cubes)if((x&pos)===pos&&!(x&neg))actual^=1;
            if(actual!==input[x])throw Error('cutoff-bit truth table');
        }
        masks.push(cubes);
    }
    return {wires,masks};
}

// Shannon and the two Davio expansions all give an exclusive sum of cubes.
// The bit ordering stays fixed within each candidate. Prefer fewer controls
// after charging for the external enable shared by these cube gates.
function tailBooleanCubes(bits,k){
    function synth(order){
        const memo=new Map();
        function solve(v,level){
            if(v.every(b=>!b))return [];
            if(v.every(b=>b))return [[0,0]];
            const id=level+':'+v.join('');if(memo.has(id))return memo.get(id);
            const mask=1<<order[level],left=v.slice(0,v.length/2),right=v.slice(v.length/2);
            const a=solve(left,level+1),b=solve(right,level+1),d=solve(left.map((v,i)=>v^right[i]),level+1);
            const on=x=>x.map(([y,n])=>[y|mask,n]),off=x=>x.map(([y,n])=>[y,n|mask]);
            const options=[a.concat(on(d)),b.concat(off(d)),off(a).concat(on(b))];
            let best=options[0],cost=Infinity;
            for(const cubes of options){
                let c=0;for(const [p,n] of cubes){let v=p|n,m=0;while(v){v&=v-1;m++;}c+=1+3*m;}
                if(c<cost){best=cubes;cost=c;}
            }
            memo.set(id,best);return best;
        }
        const flat=bits.map((_,x)=>{let y=0;for(let i=0;i<k;i++)y|=((x>>(k-1-i))&1)<<order[i];return bits[y];});
        return solve(flat,0);
    }
    // The physical variables enter in the same order as the raw rank word.
    return synth(Array.from({length:k},(_,i)=>k-1-i));
}

// For a dirty spectator d and Boolean mark G, L(d) mark L(d) applies an
// involution L exactly when G is true. Two reflection layers make any rotation.
function tailConditionalRotate(owner,tape,word,shift,back,controls,negative,plan,b){
    const sets=plan.masks[b],m=word.length;
    if(!sets.length||!(shift%=m))return;
    const work=owner.zword.at(-1);
    if([...word,...plan.wires,...controls,...negative].includes(work))throw Error('rotation spectator collision');
    const mark=()=>{
        for(const [pos,neg] of sets){
            const yes=controls.slice(),no=negative.slice();
            plan.wires.forEach((w,i)=>{if(pos>>i&1)yes.push(w);if(neg>>i&1)no.push(w);});
            if(yes.some(q=>no.includes(q)))continue;
            owner.toggle(tape,[...new Set(yes)],[...new Set(no)],work);
        }
    };
    const fixed=new Uint8Array(m),a=[],bLayer=[];
    for(let i=0;i<m;i++)if(!fixed[i]){
        const cycle=[];for(let j=i;!fixed[j];j=(j+shift)%m){fixed[j]=1;cycle.push(word[j]);}
        for(let j=1;j<cycle.length-j;j++)a.push([cycle[j],cycle[cycle.length-j]]);
        for(let j=0;j<cycle.length-1-j;j++)bLayer.push([cycle[j],cycle[cycle.length-1-j]]);
    }
    function apply(pairs){for(const [x,y] of pairs){tape.out(NONE,x,y);tape.out(work,y,x);tape.out(NONE,x,y);}}
    const first=back?bLayer:a,second=back?a:bLayer;
    apply(first);mark();apply(first);apply(second);mark();apply(second);
}

// Active digits form either a prefix, or its complementary suffix when the
// incoming selector is one. In the suffix case align the physical window
// before its first active digit. Each digit can then replace one word slot
// with its arriving bit, and one final rotation puts the word back in order.
function rollingTail(owner,tape,word,tag,base,flag,kind,back,digit,fallback){
    const n=owner.r.length-base,m=word.length;
    if(n<35||n>m||!m)return fallback();
    const plan=tailCutoffPlan(owner,tape,tag,n,kind,flag);
    const active=kind==='sign'?[]:owner.ctrl.filter(q=>q!==tape.one);
    if(!plan||[...plan.wires,...active,flag].some(q=>word.includes(q)||owner.r.slice(base).includes(q))||active.includes(flag))return fallback();
    const rotate=(positive,rv)=>{
        const pos=active.concat(positive?[flag]:[]),neg=positive?[]:[flag];
        stepList(split(0,plan.masks.length),rv,b=>tailConditionalRotate(owner,tape,word,1<<b,rv,pos,neg,plan,b));
    };
    const fixed=rv=>{const shift=n%m;if(shift)owner.permute(tape,word,word.slice(shift).concat(word.slice(0,shift)),[flag],rv);};
    const sweep=rv=>{
        const body=i=>{
            const j=(i-base)%m,arrive=owner.r[i],z=word.slice(j).concat(word.slice(0,j),arrive);
            const swap=()=>{const old=word[j];tape.out(NONE,old,arrive);tape.out(flag,arrive,old);tape.out(NONE,old,arrive);};
            if(rv)swap();digit(z,i,rv);if(!rv)swap();
        };
        if(kind==='sign')rankSweep(owner,tape,tag,base,owner.r.length,flag,true,rv,body);
        else affineRankSweep(owner,tape,base,owner.r.length,'gt',owner.ctrl,flag,rv,body);
    };
    const sequence=[rv=>rotate(true,!rv),sweep,rv=>rotate(false,rv),fixed];
    stepList(sequence,back,fn=>fn(back));
}

function patch(source,mode='both'){
    let s=source;
    function once(before,after){if(s.split(before).length!==2)throw Error('rolling tail anchor: '+before.slice(0,70));s=s.replace(before,()=>after);}
    once('class Tape {',[tailBooleanCubes,tailCutoffPlan,tailConditionalRotate,rollingTail].map(f=>f.toString()).join('\n')+'\nclass Tape {');
    if(mode!=='affine'){
        const start=s.indexOf('const extra=rv=>rankSweep(this,tape,tag,base,this.r.length,this.take,true');
        if(start<0)throw Error('rank sweep source');const end=s.indexOf('\n        const lease=',start),old=s.slice(start,end);
        once(old,old.replace('const extra=rv=>','const saved=rv=>')+`
        const extra=rv=>rollingTail(this,tape,D,tag,base,this.take,'sign',rv,(z,i,rr)=>this.tailDigit(tape,layer,z,S,!rr),()=>saved(rv));`);
    }
    if(mode!=='sign'){
        const start=s.indexOf('    affineProduct(tape,a,d,back) {'),end=s.indexOf('\n    affine(tape,back)',start);
        const was=s.slice(start,end);let sub=was;
        const reg=/const tail=rv=>affineRankSweep\(this,tape,base,this.r.length,'gt',ctrl,t,rv,i=>\{([\s\S]*?)\n\s*\}\);/g;
        let n=0;
        sub=sub.replace(reg,(old,body)=>{
            const p=body.indexOf('const seq=[rr=>'),q=body.indexOf(',rr=>this.permute(tape,z,orig,[t],rr)]',p);
            if(p<0||q<p)throw Error('affine digit lift');
            n++;const fn=body.slice(p+'const seq=['.length,q);
            return old.replace('const tail=','const saved=')+`\n        const tail=rv=>rollingTail(this,tape,d,this.tag,base,t,'affine',rv,(z,i,rr)=>(${fn})(rr),()=>saved(rv));`;
        });
        if(n!==2)throw Error('affine tail bodies '+n);once(was,sub);
    }
    return s;
}
module.exports={patch,tailBooleanCubes,tailCutoffPlan,tailConditionalRotate,rollingTail};
