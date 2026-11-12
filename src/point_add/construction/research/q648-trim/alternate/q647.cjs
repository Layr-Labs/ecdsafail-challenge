'use strict';

const path=require('node:path'),fs=require('node:fs'),crypto=require('node:crypto');
const {cleanTop}=require('../../q649-record/upper/main.cjs');
function source() {
  const snapshot=path.resolve(__dirname,'../../q647-trim/upper/donor.generated.cjs');
  if(!process.env.ALTERNATE_Q647_ROOT&&fs.existsSync(snapshot)){
    const s=fs.readFileSync(snapshot,'utf8');
    if(crypto.createHash('sha256').update(s).digest('hex')!=='af11e7ffdaed9afbf0b2b37ddbd3cd44288902083ac484f614ec2358d30f60c8')throw Error('Unexpected frozen Q647 source');
    return s;
  }
  const publicRoot=process.env.ALTERNATE_Q647_ROOT||'/tmp/q641-500m-q647-src/src/point_add/construction';
  const api=require(path.join(publicRoot,'q647/point.cjs'));
  if(api.config.width!==647)throw Error('Expected the six-helper profile');
  const f=path.join(publicRoot,'research/agents/midpoint-implicit-query-20261109/q651-ten-field/stage-map.cjs');
  const sm=require(f),old=sm.upper;let captured;
  sm.upper=(...args)=>{captured=old(...args);return captured;};
  try{api.arithmetic(null);}finally{sm.upper=old;}
  if(!captured)throw Error('Missing U45 source');
  return captured;
}

function nestedDigit(t,z,a,e,payload,levels,reserved,carry,back) {
  const h=payload.length,none=1023,ns=payload.map((p,i)=>-1200-i);
  if(h<2||a.length<h+2)throw Error('Nested ripple dimensions');
  const low=q=>ns.indexOf(q),real=q=>low(q)<0?q:payload[low(q)];
  const dirty=t.loan([...a,...z,e,carry,...payload,...reserved],5);
  const proxy=Object.create(t);proxy.ids=t.ids.filter(q=>!reserved.includes(q));
  proxy.out=(a0,b0,t0)=>{
    const x=low(a0),y=low(b0),out=low(t0);
    if(x<0&&y<0&&out<0){t.out(a0,b0,t0);return;}
    let guards=[];
    if(out>=0||t0===a[h]){
      const cross=out>=0?out:h;
      if(x<0&&y<0)throw Error('Unrecognized write to a numerical low bit');
      guards=levels.filter(g=>g.cut===cross).map(g=>g.bit);
    }else{
      const which=z.indexOf(t0);
      if(which<0||which>=h||(x!==which&&y!==which))throw Error('Unrecognized nested prefix output '+[a0,b0,t0]);
      if(a0!==none)guards=levels.filter(g=>g.cut>which).map(g=>g.bit);
    }
    if(!guards.length){t.out(real(a0),real(b0),real(t0));return;}
    const cs=guards.concat([real(a0),real(b0)].filter(q=>q!==none));
    t.mc(cs,real(t0),dirty);
  };
  cleanTop(proxy,z,ns.concat(a.slice(h)),[e],carry,back);
}

function sixHelperMain(owner,t,layer,r,a,d,back) {
  if(!owner.u36)return layer.mixed(t,r,a,d,[owner.take],back);
  const h=1+owner.u36Bits,tag=owner.tag,extra=a[1],marker=owner.u22Marker;
  const payload=[tag[0],tag[1],...a.slice(2,h)];
  const levels=[{cut:h,bit:marker},{cut:2,bit:extra},{cut:1,bit:tag[2]}];
  const reserved=[...new Set([...tag,extra,marker,...payload,owner.u36High,owner.carry,owner.take,owner.pick,owner.qtop])];
  if(new Set([...payload,marker,extra,tag[2]]).size!==h+3)throw Error('Six-helper alias');
  const swap=()=>owner.permute(t,[tag[0],tag[1]],[tag[1],tag[0]],[tag[2]],false);
  const invert=()=>{t.out(1023,1023,marker);t.out(1023,1023,tag[2]);};
  const local=Object.create(layer);
  local.digit=(tp,z,mod,on,rev)=>{
    if(on.length!==1)throw Error('Single active input expected');
    nestedDigit(tp,z,mod,on[0],payload,levels,reserved,owner.carry,rev);
  };
  swap();invert();local.mixed(t,r,a,d,[owner.take],back);invert();swap();
}

function patch(s) {
  const hit='rv=>layer.mixed(tape,this.r.slice(0,base),a,d,[this.take],rv),tail',anchor='class Tape {';
  if(s.split(hit).length!==2||s.split(anchor).length!==2)throw Error('Six-helper source anchors');
  return s.replace(anchor,()=>[cleanTop,nestedDigit,sixHelperMain].map(f=>f.toString()).join('\n')+'\n'+anchor)
    .replace(hit,'rv=>sixHelperMain(this,tape,layer,this.r.slice(0,base),a,d,rv),tail');
}
module.exports={source,patch,nestedDigit,sixHelperMain};
