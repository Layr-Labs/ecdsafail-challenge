'use strict';

function windowSquare(tape,back,limb=8,window=64) {
  const n=this.m,p=this.p,Y=this.y,D=this.d;
  const chunk=Math.min(n,window);
  if(n%limb||chunk%limb)throw Error('Unsupported square tiling');
  const base=(1n<<BigInt(limb))-1n;
  const parts=Array.from({length:n/limb},(_,i)=>Y.slice(i*limb,(i+1)*limb));
  const groups=[];
  for(let i=0;i<parts.length;i++)for(let j=i;j<parts.length;j++){
    const pos=(i+j)*limb+(i!==j?1:0),group=Math.floor(pos/chunk);
    (groups[group]??=[]).push({i,j,bits:pos%chunk});
  }
  const take=(length,start)=>Array.from({length},(_,i)=>start+i);
  const bitlen=v=>v===0n?0:v.toString(2).length;
  let max=0;
  for(const rows of groups){
    rows.sort((a,b)=>a.bits-b.bits||a.i-b.i);
    let sum=0n;
    for(const row of rows){sum+=base*base<<BigInt(row.bits);row.end=bitlen(sum);}
    max=Math.max(max,bitlen(sum));
  }
  const start=Math.max(...this.bounds,...this.local,this.carry,this.top,this.flag,this.sel)+1;
  const total=take(max,start),product=take(2*limb,start+max);
  if(product.at(-1)>=tape.n)throw Error('Insufficient coordinate workspace: '+(product.at(-1)+1));
  const order=(items,rev)=>rev?items.slice().reverse():items;
  const reverse=!!back;
  const X=q=>tape.out(1023,1023,q);
  function multiply(owner,row,rv) {
    const a=parts[row.i],b=parts[row.j];
    if(row.i!==row.j){
      for(const j of order(take(limb,0),rv))tape.add(a,product.slice(j,j+limb+1),[b[j]],owner.carry,rv);
    }else{
      const terms=[];
      for(let i=0;i<a.length;i++){
        terms.push([2*i,[a[i]]]);
        for(let j=i+1;j<a.length;j++)terms.push([i+j+1,[a[i],a[j]]]);
      }
      for(const [shift,controls] of order(terms,rv))owner.inc(tape,product.slice(shift),controls,rv);
    }
  }
  const tile=(rows,rv)=>{
    for(const row of order(rows,rv)){
      multiply(this,row,false);
      tape.add(product,total.slice(row.bits,row.end),[],this.carry,rv);
      multiply(this,row,true);
    }
  };
  const sparse=(src,shift,rv)=>{
    if((((1n<<BigInt(src.length))-1n)<<BigInt(shift))>=p)throw Error('Noncanonical sparse addend');
    const flag=this.flag,guard=this.top,high=D.slice(shift+src.length);
    const cmp=()=>{
      if(high.length)this.toggle(tape,[],high,guard);
      PayloadDigit.prototype.lt.call(this,tape,D.slice(shift,shift+src.length),src,high.length?[guard]:[],flag);
      if(high.length)this.toggle(tape,[],high,guard);
    };
    const ops=[r=>this.bias(tape,D,[],r),r=>tape.add(src,D.slice(shift).concat(flag),[],this.carry,r),
      ()=>X(flag),r=>this.bias(tape,D,[flag],!r),()=>X(flag),cmp];
    for(const op of order(ops,rv))op(rv);
  };
  for(const index of order(take(groups.length,0),reverse)){
    const rows=groups[index],length=rows.at(-1).end,adds=[];
    const fold=(src,shift,negative)=>{
      if(shift>=n){for(const [j,sign]of this.terms)fold(src,shift-n+j,negative!==(sign<0));return;}
      const cut=n-shift;
      adds.push([src.slice(0,cut),shift,negative]);
      if(src.length>cut)fold(src.slice(cut),n,negative);
    };
    fold(total.slice(0,length),chunk*index,false);
    tile(rows,false);
    for(const [src,shift,negative] of order(adds,reverse))sparse(src,shift,negative!==reverse);
    tile(rows,true);
  }
}

function patch(s,{limb=8,window=64}={}) {
  if(!Number.isInteger(limb)||!Number.isInteger(window))throw Error('Invalid static window');
  const anchor='class CoordinateArithmetic extends BlockConstant{';
  if(s.split(anchor).length!==2)throw Error('Coordinate source anchor');
  return s.replace(anchor,()=>windowSquare.toString()+'\n'+anchor+`\n    emit(tape,back){return windowSquare.call(this,tape,back,${limb},${window});}`);
}
module.exports={windowSquare,patch};
