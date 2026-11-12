'use strict';
const path=require('node:path');
require('./routing.cjs').install(process.env.Q647_POINT_ADD||path.resolve(__dirname,'../../q647-trim/donor'),647);
