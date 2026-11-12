'use strict';
const old=require('../../../q647-trim/hybrid/index.cjs');

function sevenWitness(k){
  const H=new UnguardedGeneral(256,(1n<<32n)+977n,k,657),t=new FoldTape(657,[],H.g),P=639,D=640,F=644;
  const N=1023,emitted=[],rest=[],known=new Int8Array(N+1).fill(-1);known[P]=0;known[N]=1;
  t.ids=t.ids.filter(q=>q<=649&&q!==647&&q!==P&&q!==D&&q!==F);
  t.out=(x,y,z)=>{
    if(x===F||y===F||[x,y,z].some(w=>w===P||w===D||w===647))throw Error('Q648 witness donor needs protected input '+[k,x,y,z]);
    const wire=w=>w===642?P:w===F?D:w;
    x=wire(x);y=wire(y);z=wire(z);
    // On the bit-setting path the donor rank helper starts at zero. The
    // surrounding involutions cancel the other path for every basis state.
    if(known[x]===0||known[y]===0)return;
    if(known[x]===1)x=N;if(known[y]===1){y=x;x=N;}
    if(x===N&&y===N){if(known[z]>=0)known[z]^=1;}else known[z]=-1;
    emitted.push((x<<20)|(y<<10)|z);
  };
  H.trial(t,true,true);
  // Only the terminal D value is observed. A gate on any other dead wire
  // can be omitted. All literals name controls before that gate executes.
  const live=new Uint8Array(N+1),a=[];live[D]=1;
  for(let i=emitted.length-1;i>=0;i--){
    const op=emitted[i],z=op&N;if(!live[z])continue;
    const x=op>>>20,y=(op>>>10)&N;
    if(x!==N)live[x]=1;if(y!==N)live[y]=1;a.push(op);
  }
  a.reverse();if(!a.length)throw Error('No donor witness deposits for row '+k);
  // Without the write-only D gates this is exactly the action on all
  // other wires, including P when it starts in the wrong state. Erase
  // adjacent identical self-inverse gates before attaching its inverse.
  for(const op of a){if((op&1023)===D)continue;if(rest.length&&rest[rest.length-1]===op)rest.pop();else rest.push(op);}
  return {a,rest};
}

function dirtyWitness(t,k){
  const N=1023,P=639,D=640,F=644,{a,rest}=q647DirtyWitnessOps(k);
  const X=i=>t.out(N,N,i),C=(x,y,z)=>t.out(x,y,z);
  function run(rows,back){
    for(let j=0;j<rows.length;j++){const op=rows[back?rows.length-1-j:j];t.out(op>>>20,op>>>10&N,op&N);}
  }
  function oracle(back){if(back){run(rest,false);run(a,true);}else{run(a,false);run(rest,true);}}
  for(let flip=0;flip<2;flip++){
    if(flip)X(P);
    X(P);C(P,D,F);X(P);oracle(false);X(P);C(P,D,F);X(P);oracle(true);
    if(flip)X(P);
  }
}
function patch(s,first=96,last=106){
  if(!(Number.isInteger(first)&&Number.isInteger(last)&&64<=first&&first<=last&&last<=111))throw Error('Q647 witness interval');
  const src=Buffer.from(old.kernelText(false),'base64').toString('utf8');
  const tail='return '+old.phaseSign.toString()+';';if(!src.endsWith(tail))throw Error('Q648 witness source boundary');
  const witness=src.slice(0,-tail.length)+'return '+sevenWitness.toString()+';';
  const kernel=Buffer.from(witness).toString('base64'),marker='function u37Select(w){';
  if(s.split(marker).length!==2||!s.includes('const q647SevenPhase=')||s.includes('const q647DirtyWitnessOps='))throw Error('Expected the frozen Q647 hybrid');
  return s.replace(marker,()=>`const q647DirtyWitnessOps=Function(Buffer.from(${JSON.stringify(kernel)},'base64').toString('utf8'))();\n`+
    dirtyWitness.toString()+`\nconst q647OriginalWitness=UnguardedGeneral.prototype.trial;
    UnguardedGeneral.prototype.trial=function(t,w,back){
      if(w&&back&&this.m===256&&this.k>=${first}&&this.k<=${last}&&t.u37Control?.frame===642)return dirtyWitness(t,this.k);
      return q647OriginalWitness.call(this,t,w,back);
    };\n`+marker);
}
module.exports={patch,sevenWitness,dirtyWitness};
