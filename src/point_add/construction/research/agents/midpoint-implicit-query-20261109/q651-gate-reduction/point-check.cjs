'use strict';
const path=require('node:path'),Module=require('node:module');
const {checkedSource}=require('../field128-height-experiment/pinned.cjs');
const {replace}=require('../q653-next/parts.cjs');
const base=require.resolve('../q651-ten-field/point-check.cjs');
const s=replace(checkedSource(base,'2952c0ac8a0c37ccbca6ca64514fb9e5dab01c7c5fce2c07f45f889eab72dbe4'),"m.binding=require('./point.cjs')",'m.binding=module.binding');
const m=new Module(base,module);m.filename=base;m.paths=Module._nodeModulePaths(path.dirname(base));
m.binding=require('./point.cjs');m._compile(s,base);
