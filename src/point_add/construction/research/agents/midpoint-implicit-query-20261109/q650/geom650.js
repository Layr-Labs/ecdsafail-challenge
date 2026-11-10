'use strict';
// q650 geometry (hole). [from,to] edits on the FINAL upper source (after q651/upper651.cjs), which also holds the
// field and history native maps. geom({width,tight,cfg}):
//   width 650: tape wires 0..649, 9 clean sites. Every stage must be tight.
//   width 651: tape keeps 651 wires (10 clean, the last is physical 650), but stages in `tight` get only the first 9.
//              Their uses of physical 650 become removed ports and throw. This validates stages one at a time at 651.
// Removed ports fail closed: nativeSink throws "backend target/control", PointFoldTape throws "upper used removed physical site".
module.exports=({width,tight,cfg})=>{
  if(width!==650&&width!==651)throw Error('geom650 width');
  const T=s=>width===650||tight.has(s),K=width===650?9:10,out=[];
  if(width===650)out.push(['2*m+m/2+4+Math.ceil(Math.log2(m/2))','2*m+m/2+3+Math.ceil(Math.log2(m/2))']);
  if(T('field')){
    const ff=[651,...cfg.fieldFree];
    out.push(['ids[i]=i===651?undefined:(i===648||i>=652)?-2:clean[z++];if(clean.length!==10||z!==10)throw Error("Q655 field geometry");',
      'ids[i]=('+JSON.stringify(ff)+').includes(i)?undefined:(i===648||i>=652)?-2:clean[z++];if(clean.length!=='+K+'||z!==9)throw Error("Q650 field geometry");']);
  }
  if(T('history')){
    const z=cfg.histFree;
    out.push(['for(let i=0;i<ids.length;i++)if(ids[i]===undefined&&i!==654)ids[i]=clean[j++];',
      'for(let i=0;i<ids.length;i++)if(ids[i]===undefined&&i!==654'+(z==null?'':'&&i!=='+z)+')ids[i]=clean[j++];']);
    out.push(['if(j!==10||clean.length!==10)throw Error("Q651 history geometry");',
      'if(j!==9||clean.length!=='+K+')throw Error("Q650 history geometry: regen must free one history logical (histFree='+z+')");']);
  }
  if(T('upper')){
    if(width===650){
      out.push(['this.ids=this.ids.slice(0,-5);this.ids=this.ids.filter(q=>q<652||q>656);','this.ids=this.ids.slice(0,-6);this.ids=this.ids.filter(q=>q<651||q>656);']);
      out.push(['...split(2*m+b+1,logical-6)];','...split(2*m+b+1,logical-7)];']);
      out.push(['new Set(map).size!==logical-6||map.length!==logical-6','new Set(map).size!==logical-7||map.length!==logical-7']);
    }else{ // keep physical 650 on the tape but unmap it for the upper: upper logical 651 (map[650]) becomes removed
      out.push(['this.ids=this.ids.slice(0,-5);this.ids=this.ids.filter(q=>q<652||q>656);','this.ids=this.ids.slice(0,-5);this.ids=this.ids.filter(q=>q<651||q>656);']);
      out.push(['this.map=map;const wire=','map.length=logical-7;this.map=map;const wire=']);
    }
  }
  return out;
};
