'use strict';

const path = require('node:path');
const research = path.resolve(__dirname, '../..');
const donor = path.join(research, 'q647-trim/donor');
const field = path.join(research, 'q648-trim/field');
const six = path.join(research, 'q648-next/field');
const family = require(path.join(field, 'q647/stages.cjs')).family;

require(path.join(six, 'six.cjs')).install(field, donor);
require(path.join(six, 'winding.cjs')).install(path.join(donor, family));
require(path.join(research, 'q648-next/unit/six/preload.cjs'));
