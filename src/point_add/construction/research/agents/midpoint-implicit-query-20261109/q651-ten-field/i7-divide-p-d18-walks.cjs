'use strict';
// Accept D16's 2-tag inner / 3-tag reverse interface; change only nominal widths.
module.exports=s=>{for(const [a,b] of [['new SectorCanonical(n,2)','new SectorCanonical(n,3)'],['w.tag=w.tag.slice(0,3)','w.tag=w.tag.slice(0,4)']]){if(s.split(a).length!==2)throw Error('D18 interface anchor '+a);s=s.replace(a,b);}return s;};
