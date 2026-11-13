'use strict';
function denseSwap(owner,tape,back){
    const q=owner.u40Tag.slice(0,5),perm=[15,31];
    for(let r=0;r<4;r++){
        const count=1<<(4-r),start=1<<(4-r);
        for(let low=0;low<count;low++)perm[start+low]=(1<<r)-1+(low<<(r+1));
    }
    if(new Set(perm).size!==32)throw Error('Q647 dense rank map');
    const visited=new Set(),swaps=[];
    for(let j=0;j<32;j++)if(!visited.has(j)){
        let i=j;while(!visited.has(i)){visited.add(i);i=perm[i];if(i!==j)swaps.push([j,i]);}
    }
    for(const [u,v] of back?swaps.reverse():swaps)owner.u6Transpose(tape,q,u,v,[],[],false);
}
function denseVisit(owner,tape,fn){
    const H=Object.create(owner);H.u34Low=4;H.u34Unary=false;
    denseSwap(owner,tape,false);fn(H);denseSwap(owner,tape,true);
}
function denseMixed(owner,tape,q,v,rem,rv){denseVisit(owner,tape,H=>prefixMixed(H,tape,q,v,rem,rv));}
function denseAdd(owner,tape,a,d,rv){denseVisit(owner,tape,H=>prefixAdd(H,tape,a,d,rv));}
function extend(s){
    const marker='class Tape {';s=s.replace(marker,()=>[denseSwap,denseVisit,denseMixed,denseAdd].map(f=>f.toString()).join('\n')+'\n'+marker);
    const a=s.indexOf('    u29DenseSign(inputTape,target){'),b=s.indexOf('\n    u32',a);if(a<0||b<a)throw Error('Q647 dense source');
    let core=s.slice(a,b);
    const edit=(old,v)=>{if(core.split(old).length!==2)throw Error('Q647 dense anchor '+old);core=core.replace(old,()=>v);};
    edit('rv=>H.u6VirtualTape(tape).add(a,D,[],this.carry,rv)','rv=>denseAdd(H,tape,a,D,rv)');
    edit('stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);stepList(seq,true,fn=>fn(true));',`const known=this.u5PhaseHost!==target&&target===this.dv[0]&&(this.measureTarget===target||!this.probeBack)&&!tag.includes(target);H.q647Loan=known?target:null;stepList(seq,false,fn=>fn(false));this.u40Deposit(tape,target,S,word);H.q647Loan=known&&this.measureTarget===target?target:null;stepList(seq,true,fn=>fn(true));`);
    s=s.slice(0,a)+core+s.slice(b);
    const entry='if(this.u34Low&&v[0]===this.u40Low&&!controls.length)';
    if(s.split(entry).length!==2)throw Error('Q647 dense mixed');
    return s.replace(entry,()=>`if(this.u29Dense&&v[0]===this.u40Low&&!controls.length){denseMixed(this,tape,q,v,rem,back);return;}\n      `+entry);
}
module.exports={extend};
