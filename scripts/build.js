'use strict';
const fs = require('node:fs');
const path = require('node:path');
const root = path.resolve(__dirname, '..');
const {version,repository} = require('../package.json');
const read = file => fs.readFileSync(path.join(root,file),'utf8').replace(/\r\n/g,'\n');
const raw = repository.replace('https://github.com/','https://raw.githubusercontent.com/')+'/main/outputs/pcol-rules-patch.user.js';
const header = `// ==UserScript==
// @name         PCOL Snooker Rules Patch
// @namespace    local.pcol.rules
// @version      ${version}
// @description  Local hot-seat snooker with touching-ball rulings, automatic colour nomination and foul replay.
// @match        http://www.heyzxz.me/pcol/*
// @match        https://www.heyzxz.me/pcol/*
// @run-at       document-start
// @grant        none
// @noframes
// @updateURL    ${raw}
// @downloadURL  ${raw}
// ==/UserScript==
`;
const core = read('src/rules-core.js').replace(/\nmodule\.exports = PCOLCore;\s*$/,'\n');
const integration = read('src/integration.js').replaceAll('__PCOL_VERSION__',JSON.stringify(version));
fs.mkdirSync(path.join(root,'outputs'),{recursive:true});
fs.writeFileSync(path.join(root,'outputs/pcol-rules-patch.user.js'),header+'(() => {\n'+core+'\n'+integration+'\n})();\n','utf8');
console.log(`Built PCOL ${version}`);
