'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),vm=require('node:vm'),{EventEmitter}=require('node:events');
const core=require('../src/rules-core');
const practice=require('../src/practice-editor');
const modelSource=require('./fixtures/pcol-model');
const {version}=require('../package.json');
// Execute the original game model; stub only rendering and stationary physics.
const Model=vm.runInNewContext('('+modelSource+')',{f:EventEmitter,Te:{a:{NO_GAME:1,PENDING:2,READY:4,SIMULATING:8,JUDGING:16,ERROR:32}},o:{a:{makeGContext:()=>({ballOn:2,inHand:0,nRounds:0,playerIndex:1}),makeRefResult:()=>({score:0,foulCode:0})}}});
class Element{
  constructor(tag='div'){this.tag=tag;this.children=[];this.style={};this.hidden=false;}
  set innerHTML(value){this.children=[];for(const name of ['bar','drag','status','hotseat','practice','edit','retry','choose','concede','modal']){const e=new Element(name==='status'?'span':['bar','modal'].includes(name)?'div':'button');e.className=name;this.append(e);}}
  append(...es){this.children.push(...es);}appendChild(e){this.append(e);return e;}replaceChildren(...es){this.children=es;}
  setAttribute(name,value){this[name]=value;}addEventListener(){}removeEventListener(){}focus(){}remove(){this.removed=true;}
  attachShadow(){return this.shadow=new Element();}
  querySelector(selector){const match=e=>selector.startsWith('.')?e.className===selector.slice(1):e.tag===selector;for(const e of this.children){if(match(e))return e;const nested=e.querySelector(selector);if(nested)return nested;}return null;}
}
function setup(score=55){
  const model=new Model(),players=[0,1].map(i=>({pts:i?score:0,penalty:0,brk:0,scoreCount:0,shootingCount:0,clearScores(){this.pts=this.penalty=this.brk=this.scoreCount=this.shootingCount=0;}}));model._players=players;model._gState=4;
  const bs=[0,1,2,3,4,5,6,7].map((n,i)=>({index:i,number:n,active:true,radius:.02625,v:{x:0,y:0,z:0},position:{x:n===0?-.8:n===1?.8:(i-4)*.1,y:.90625,z:n<=1?0:.5},syncStates(){this.states={position:{...this.position}};}}));
  for(const b of bs)b.spot={...b.position};
  const world={nAwakened:0,evolution:1,serialize(){return {balls:bs.map(b=>({index:b.index,active:b.active,position:{...b.position}}))};},restore(serial){for(const b of serial.balls){Object.assign(bs[b.index],{active:b.active,position:{...b.position}});}},internalStep(){},__internalStep__(){},predict(){},touchPresolveHandler(){}};
  world.solver={solveContact(c){for(const [b,delta]of [[c.bi,c.deltaI],[c.bj,c.deltaJ]])if(delta)for(const axis of ['x','y','z'])b.v[axis]+=delta[axis]||0;}};
  const sim={_world:world,_nPhxAwakened:0,nAwakened:0,evolution:1,ballRadius:.02625,result:{pottedIndices:[],outOfBoundsIndices:[]},getBalls:()=>bs,getBallAtIndex:i=>bs[i],getCueBallPosition:()=>bs[0].position,stroke(velocity){if(velocity)Object.assign(bs[0].v,velocity);},clearResult(){this.result.pottedIndices=[];this.result.outOfBoundsIndices=[];},save(){},reset(){this.clearResult();return this;}};
  Object.assign(sim,{spotY:.90625,ground:{edges:[{va:{x:-1.7969,z:-.8966}},{va:{x:1.7969,z:.8966}}]},sidePolyGroups:{polys:[]},
    respotIndexXYZ(i,x,y,z){bs[i].active=true;bs[i].position={x,y,z};},resetBallPosition(b,p){b.active=Boolean(p);if(p)b.position={...p};},touchBalls(i,p){return bs.some(b=>b.active&&b.index!==i&&Math.hypot(p.x-b.position.x,p.z-b.position.z)<2*b.radius);}});
  model._locRef={_liveRespot(){},_liveRespotCueBall(){},resetGContext(ctx){ctx.ballOn=2;ctx.inHand=0;}};
  Object.assign(model._locRef,{_dArea:{_center:{x:-1.04},_radius:.29},intersectionRayValidRegionPlane(origin,dir,out){Object.assign(out,origin);return true;},projectionInSideValidRegion(x){return x<=-1;}});
  let endings=0;model.on('response',()=>{if(model._gContext.ballOn===0)endings++;});
  const fpc={_gPlayerIndex:0,get gPlayerIndex(){return this._gPlayerIndex;},gotoState0(){},markForceUpdate(){}},g={_model:model,_simulator:sim,_fpc:fpc,_playerCtls:[fpc,{gPlayerIndex:1,deactivate(){},release(){}}],_paused:false,_gView:{canvas:{focus(){}},syncBalls(){}},_movieClip:{erase(){}},_uiLayer:{closeMessage(){}}};
  Object.assign(g._gView,{showRespotIcons(){},requireRender(){},_respotIcon0:{alpha:0}});
  Object.assign(g._gView.canvas,{addEventListener(){},removeEventListener(){}});
  g._subControl={inHand:{name:'inHand',_closeTip(){},_showTip(){},_onActvate(){}},gaming:{name:'gaming'}};
  g._activateSubControl=function(name){this._activeSubControl=this._subControl[name];this._activeSubControl._onActvate?.();};
  g._onModelResponse=function(){this._activateSubControl('gaming');};model.on('response',()=>g._onModelResponse());
  const app={constructor:{VERSION:'0.1.0.03152018'},_controllers:{game:g},_currentController:g,onCurrentControllerStateChanged(){}};
  const window={addEventListener(){},removeEventListener(){}},document={documentElement:new Element(),createElement:tag=>new Element(tag)};
  const integration=fs.readFileSync(require.resolve('../src/integration.js'),'utf8').replaceAll('__PCOL_VERSION__',JSON.stringify(version));
  const celebrations=[];
  let editorOptions;
  vm.runInNewContext(integration,{window,document,PCOLCore:core,PCOLPractice:{...practice,createEditor:options=>{editorOptions=options;return{update(){},destroy(){}};}},PCOLCelebration:{create:()=>({show:data=>celebrations.push(data),clear(){},destroy(){}})},console});
  const s=window.PCOLPatch.attach(app,{c:{}}),api=window.PCOLPatch;
  function stroke({player=1,pot=false,miss=false}={}){
    model._gContext.playerIndex=player;if(s.hotseat)model._response(sim);assert.equal(model.reportPlayerStroke(player),true);
    const q=bs[0].position;s.shot.trace=[{t:0,...q},{t:1,...q}];
    if(!miss)s.shot.contacts=[{t:0,ballIndex:1,evolution:1,...q,legal:true}];
    if(pot){bs[1].active=false;sim.result.pottedIndices.push(1);}
    assert.equal(model.reqRoundResult(sim),model);
  }
  const buttons=()=>{const panel=s.shadow.querySelector('.panel');return panel?.querySelector('.choices')?.children||[];};
  return {s,api,g,model,sim,players,stroke,buttons,celebrations,editor:()=>editorOptions,endings:()=>endings};
}

test('3D practice placement moves the selected colour across the table, rejects overlaps and cancels cleanly',()=>{
  const t=setup(0);t.players.splice(1);t.s.practice='custom';Object.assign(t.model._gContext,{ballOn:65535,playerIndex:0});
  const before=t.sim._world.serialize();assert.equal(t.api.editPractice(),true);assert.equal(t.g._paused,false);
  t.editor().onSelect(5);const pos={x:1.2,y:.90625,z:0};
  assert.equal(t.model.isValidInHandPositionUnderRay(pos,{},t.sim,{}),true);
  assert.equal(t.model.reqRespotCueball(pos,t.sim),true);assert.deepEqual(t.sim.getBallAtIndex(5).position,pos);
  assert.deepEqual(t.sim.getBallAtIndex(0).position,before.balls[0].position);assert.equal(t.g._activeSubControl.name,'inHand');
  assert.equal(t.model.reqRespotCueball(t.sim.getBallAtIndex(0).position,t.sim),false);assert.equal(t.model.reportPlayerStroke(0),false);
  t.editor().onCancel();assert.equal(t.s.placement,null);assert.deepEqual(t.sim._world.serialize(),before);assert.equal(t.g._activeSubControl.name,'gaming');
  assert.equal(t.model.isValidInHandPositionUnderRay(pos,{},t.sim,{}),false);
});

test('3D practice placement commits a new layout and clears prior shot retry statistics',()=>{
  const t=setup(0);t.players.splice(1);t.s.practice='custom';Object.assign(t.model._gContext,{ballOn:65535,playerIndex:0});
  t.players[0].pts=20;t.s.practiceBefore={};t.api.editPractice();t.editor().onSelect(7);
  t.model.reqRespotCueball({x:1.3,y:.90625,z:.2},t.sim);t.editor().onDone();
  assert.equal(t.s.placement,null);assert.equal(t.s.practiceBefore,null);assert.equal(t.players[0].pts,0);
  assert.equal(t.s.practiceLayout.find(b=>b.n===7).x,1.3);assert.equal(t.g._activeSubControl.name,'gaming');
});

test('a century is celebrated on the scoring stroke once, never on response or foul',()=>{
  const t=setup(0);t.players[1].brk=99;t.stroke({pot:true});
  assert.equal(t.celebrations.length,1);assert.equal(t.celebrations[0].breakScore,100);
  t.model._response(t.sim);assert.equal(t.celebrations.length,1);
  t.model._gContext.ballOn=2;t.sim.getBallAtIndex(1).active=true;t.sim.clearResult();t.stroke({pot:true});
  assert.equal(t.players[1].brk,101);assert.equal(t.celebrations.length,1);
  const foul=setup(0);foul.players[1].brk=99;foul.stroke({miss:true});assert.equal(foul.celebrations.length,0);
});

test('standard practice retries a pot or foul with the entire table and score counters restored',()=>{
  for(const miss of [false,true]){
    const t=setup(0);t.players.splice(1);t.s.practice='standard';t.model._gContext.playerIndex=0;t.model._gContext.inHand=0;
    Object.defineProperty(t.players[0],'maxbrk',{get(){return this._maxBrk;}});t.players[0]._maxBrk=99;t.players[0].brk=99;
    const context={...t.model._gContext},cue={...t.sim.getBallAtIndex(0).position};
    t.stroke({player:0,pot:!miss,miss});t.sim.getBallAtIndex(0).position.x+=.2;
    assert.equal(t.api.getStatus().canRetryPractice,true);assert.equal(t.s.shadow.querySelector('.retry').disabled,false);
    assert.equal(t.api.retryPractice(),true);assert.deepEqual(t.model._gContext,context);assert.deepEqual(t.sim.getBallAtIndex(0).position,cue);
    assert.equal(t.sim.getBallAtIndex(1).active,true);assert.equal(t.players[0].pts,0);assert.equal(t.players[0].penalty,0);assert.equal(t.players[0].brk,99);assert.equal(t.players[0].maxbrk,99);assert.equal(t.players[0].shootingCount,0);
    assert.equal(t.api.retryPractice(),false);assert.equal(t.model.reportPlayerStroke(0),true);assert.equal(t.api.retryPractice(),false);
  }
});

test('free practice leaves potted targets off the table and can retry consecutive shots',()=>{
  const t=setup(0);t.players.splice(1);t.s.practice='custom';t.model._gContext.playerIndex=0;t.model._gContext.ballOn=65535;
  for(let attempt=0;attempt<2;attempt++){
    t.stroke({player:0,pot:true});assert.equal(t.sim.getBallAtIndex(1).active,false);assert.equal(t.s.shot,null);
    assert.equal(t.api.getStatus().lastResult.pottedCount,1);assert.equal(t.players[0].pts,0);assert.equal(t.model._gContext.ballOn,65535);
    assert.equal(t.api.retryPractice(),true);assert.equal(t.sim.getBallAtIndex(1).active,true);assert.equal(t.model._gContext.nRounds,0);
  }
});

test('the final black in solo practice remains retryable after frame completion',()=>{
  const t=setup(0);t.players.splice(1);t.s.practice='standard';Object.assign(t.model._gContext,{playerIndex:0,ballOn:128,inHand:0});
  for(const b of t.sim.getBalls())if(b.number>0&&b.number!==7)b.active=false;
  assert.equal(t.model.reportPlayerStroke(0),true);const q=t.sim.getBallAtIndex(0).position;
  t.s.shot.trace=[{t:0,...q},{t:1,...q}];t.s.shot.contacts=[{ballIndex:7,evolution:1,...q}];
  t.sim.getBallAtIndex(7).active=false;t.sim.result.pottedIndices=[7];t.model.reqRoundResult(t.sim);
  assert.equal(t.model._gContext.ballOn,0);assert.equal(t.model.reportPlayerStroke(0),false);assert.equal(t.api.retryPractice(),true);
  assert.equal(t.model._gContext.ballOn,128);assert.equal(t.sim.getBallAtIndex(7).active,true);assert.equal(t.players[0].pts,0);
});

test('practice placement permits touching but rejects overlap, rail and pocket positions',()=>{
  const b={i:0,n:0,active:true,x:0,z:0,r:.02625},red={...b,i:1,n:1,x:.0525};
  const bounds={minX:-1.8,maxX:1.8,minZ:-.9,maxZ:.9,pockets:[{x:0,z:.9,r:.075}]};
  assert.equal(practice.placementError([b],red,bounds),'');
  assert.match(practice.placementError([b],{...red,x:.04},bounds),/重叠/);
  assert.match(practice.placementError([b],{...red,x:1.79},bounds),/库边/);
  assert.match(practice.placementError([b],{...red,x:0,z:.82},bounds),/袋口/);
});
test('twenty over at handover pauses and blocks the next stroke until a choice',()=>{
  const t=setup();t.stroke();assert.equal(t.api.getStatus().concession.excess,20);assert.equal(t.s.modal,true);assert.equal(t.g._paused,true);assert.equal(t.model.reportPlayerStroke(0),false);
  assert.deepEqual(t.buttons().map(b=>b.textContent),['继续本局','认输本局']);
  t.buttons()[0].onclick();assert.equal(t.s.modal,false);assert.equal(t.g._paused,false);assert.equal(t.s.shadow.querySelector('.concede').hidden,false);assert.equal(t.players[1].pts,55);
  assert.equal(t.model.reportPlayerStroke(0),true);assert.equal(t.api.getStatus().concession.available,false);
});
test('nineteen over and an uninterrupted scoring break never prompt concession',()=>{
  const t=setup(54);t.stroke();assert.equal(t.s.modal,false);assert.equal(t.api.getStatus().concession.available,false);
  const scoring=setup(55);scoring.stroke({pot:true});assert.equal(scoring.model._gContext.playerIndex,1);assert.equal(scoring.s.modal,false);assert.equal(scoring.api.getStatus().concession.available,false);
});
test('a foul is decided before offering concession to the incoming player',()=>{
  const t=setup(59);t.stroke({miss:true});assert.ok(t.s.pending);assert.equal(t.api.getStatus().concession.available,false);assert.equal(t.api.concede(),false);
  t.api.resolveFoul('continue');assert.equal(t.s.pending,null);assert.equal(t.api.getStatus().concession.excess,20);assert.equal(t.s.modal,true);assert.equal(t.buttons()[1].textContent,'认输本局');
});
test('asking the offender to play again never offers the non-acting human concession',()=>{
  const t=setup(59);t.stroke({miss:true});t.api.resolveFoul('again');assert.equal(t.model._gContext.playerIndex,1);assert.equal(t.s.modal,false);assert.equal(t.api.getStatus().concession.available,false);
});
test('concession ends this frame with unchanged scores; a reset permits normal play',()=>{
  const t=setup();t.stroke();t.buttons()[1].onclick();assert.equal(t.model._gContext.ballOn,0);assert.equal(t.endings(),1);assert.equal(t.players[0].pts,0);assert.equal(t.players[1].pts,55);assert.equal(t.api.getStatus().conceded.winnerIndex,1);assert.equal(t.g._paused,false);
  assert.equal(t.model.reportPlayerStroke(0),false);assert.equal(t.api.concede(),false);t.model._onResetResponse(t.sim,false,0,0);assert.equal(t.api.getStatus().conceded,null);assert.equal(t.s.modal,false);assert.equal(t.model.reportPlayerStroke(0),true);
});
test('repeated model responses for placing the cue do not repeat a declined prompt',()=>{
  const t=setup();t.stroke();t.buttons()[0].onclick();t.model._response(t.sim);assert.equal(t.s.modal,false);assert.equal(t.api.getStatus().concession.available,true);
});
test('a lagging AI does not show the human a concession dialog for the AI',()=>{
  const t=setup(0);t.players[0].pts=55;t.stroke({player:0});assert.equal(t.model._gContext.playerIndex,1);assert.equal(t.s.modal,false);assert.equal(t.s.shadow.querySelector('.concede').hidden,true);
});

test('hot-seat hands both turns to the same controller before response listeners run',()=>{
  const t=setup(0);t.s.hotseat=true;
  const shared=t.g._playerCtls;t.g._playerCtls.push(t.g._fpc);
  t.model.on('response',()=>{assert.equal(t.g._fpc.gPlayerIndex,t.model._gContext.playerIndex);assert.equal(shared.length,1);assert.equal(shared[0],t.g._fpc);});
  t.stroke({player:0});assert.equal(t.model._gContext.playerIndex,1);
  t.stroke({player:1});assert.equal(t.model._gContext.playerIndex,0);
  assert.deepEqual(t.players.map(p=>p.shootingCount),[1,1]);assert.equal(t.g._playerCtls,shared);
});

test('hot-seat keeps a scoring player at the table and asks either player to nominate colour',()=>{
  for(const player of [0,1]){
    const t=setup(0);t.s.hotseat=true;t.stroke({player,pot:true});
    assert.equal(t.model._gContext.playerIndex,player);assert.equal(t.g._fpc.gPlayerIndex,player);assert.equal(t.players[player].pts,1);
    assert.equal(t.model.reportPlayerStroke(player),false);assert.equal(t.s.modal,true);
    const black=t.buttons().find(b=>b.textContent==='黑球');assert.ok(black);black.onclick();
    assert.equal(t.model.reportPlayerStroke(player),true);assert.equal(t.s.shot.before.nominatedColour,7);
  }
});

test('hot-seat lets either incoming player decide a foul and rebinds to the restored offender',()=>{
  for(const player of [0,1]){
    const t=setup(0);t.s.hotseat=true;t.stroke({player,miss:true});
    assert.ok(t.s.pending);assert.equal(t.g._fpc.gPlayerIndex,1-player);assert.equal(t.s.modal,true);
    assert.equal(t.buttons()[0].textContent,`玩家 ${2-player}接手（打红球）`);
    assert.equal(t.api.resolveFoul('restore'),true);assert.equal(t.g._fpc.gPlayerIndex,player);assert.equal(t.players[player].penalty,-4);
    assert.equal(t.model.reportPlayerStroke(player),true);
  }
});

test('hot-seat player 2 can nominate a free ball and place the cue without losing control',()=>{
  const t=setup(0);t.s.hotseat=true;t.model._gContext.playerIndex=1;t.model._gContext.inHand=2;t.model._response(t.sim);
  assert.equal(t.g._fpc.gPlayerIndex,1);t.s.freeBallAvailable=true;t.api.chooseBall();
  const blue=t.buttons().find(b=>b.textContent==='蓝球');assert.ok(blue);blue.onclick();
  t.model._gContext.inHand=1;t.model._response(t.sim);assert.equal(t.g._fpc.gPlayerIndex,1);
  assert.equal(t.model.reportPlayerStroke(1),true);assert.equal(t.s.shot.before.freeBallNominee,5);
});

test('hot-seat offers the twenty-over concession to player 2 and clears it on restart',()=>{
  const t=setup(0);t.s.hotseat=true;t.players[0].pts=55;t.stroke({player:0});
  assert.equal(t.g._fpc.gPlayerIndex,1);assert.equal(t.s.modal,true);assert.match(t.s.shadow.querySelector('p').textContent,/玩家 2落后/);
  t.buttons()[1].onclick();assert.equal(t.api.getStatus().conceded.winnerIndex,0);assert.deepEqual(t.api.getStatus().score,[55,0]);
  t.model._onResetResponse(t.sim,false,1,0);assert.equal(t.s.hotseat,true);assert.equal(t.g._fpc.gPlayerIndex,1);assert.equal(t.model.reportPlayerStroke(1),true);
});

function autoColourFixture(){
  const t=setup(0);t.s.hotseat=true;Object.assign(t.model._gContext,{playerIndex:0,ballOn:252});
  Object.assign(t.sim.getBallAtIndex(5).position,{x:0,z:0});
  t.g._fpc.getKissDir=()=>({x:1,y:0,z:0});t.model._response(t.sim);
  return t;
}
function finishWithContacts(t,indices){
  const q=t.sim.getBallAtIndex(0).position;t.s.shot.trace=[{t:0,...q},{t:1,...q},{t:2,...q}];
  t.s.shot.contacts=indices.map((index,i)=>({t:i,evolution:i,...q,...(index==='cushion'?{kind:'cushion'}:{ballIndex:index,legal:index===5})}));
  t.model.reqRoundResult(t.sim);
}

test('auto colour is locked before the stroke; a later lucky different colour is a foul',()=>{
  const t=autoColourFixture();assert.equal(t.model.reportPlayerStroke(0),true);assert.equal(t.s.modal,false);
  assert.equal(t.s.shot.before.nominatedColour,5);assert.equal(t.s.shot.before.nominationSource,'auto');
  finishWithContacts(t,[6]);assert.equal(t.s.lastResult.score,-6);assert.ok(t.s.lastResult.foulCode&core.FOUL.FIRST_HIT);
  assert.equal(t.s.lastBefore.nominatedColour,5);
});

test('a cushion before the automatically nominated colour is not itself a foul',()=>{
  const t=autoColourFixture();assert.equal(t.model.reportPlayerStroke(0),true);
  finishWithContacts(t,['cushion',5]);assert.equal(t.s.lastResult.foulCode,0);assert.equal(t.s.lastResult.score,0);
  assert.equal(t.model._gContext.ballOn,2);assert.equal(t.model._gContext.playerIndex,1);
});

test('an uncertain aim waits for nomination without starting a stroke; manual choice overrides aim',()=>{
  const t=autoColourFixture();t.g._fpc.getKissDir=()=>({x:-1,z:0});
  assert.equal(t.model.reportPlayerStroke(0),false);assert.equal(t.s.shot,null);assert.equal(t.players[0].shootingCount,0);
  t.buttons().find(b=>b.textContent==='黑球').onclick();assert.equal(t.s.shot,null);assert.equal(t.model._gState,4);
  assert.equal(t.model.reportPlayerStroke(0),true);assert.equal(t.s.shot.before.nominatedColour,7);assert.equal(t.s.shot.before.nominationSource,'manual');
});

test('no-contact penalty uses the auto nomination fixed before play',()=>{
  const t=autoColourFixture();assert.equal(t.model.reportPlayerStroke(0),true);finishWithContacts(t,[]);
  assert.equal(t.s.lastResult.score,-5);assert.equal(t.s.lastResult.ballOnUsed,5);
});

test('jump foul followed by taking over commits red, yellow, or the current clearance colour',()=>{
  for(const [on,reds,target,expected] of [[252,true,7,2],[252,false,7,4],[8,false,3,8]]){
    const t=setup(0);t.s.hotseat=true;Object.assign(t.model._gContext,{playerIndex:0,ballOn:on});
    const bs=t.sim.getBalls();bs[1].active=reds;Object.assign(bs[1].position,{x:.5,z:.5});
    Object.assign(bs[5].position,{x:0,z:0});Object.assign(bs[target].position,{x:.8,z:0});
    t.s.nominatedColour=on===252?target:null;t.model._response(t.sim);assert.equal(t.model.reportPlayerStroke(0),true);
    const snapshot=t.s.shot.before.balls;
    t.s.shot.trace=[{t:0,x:-.8,y:.90625,z:0,balls:snapshot},{t:1,x:0,y:1.1,z:0,balls:snapshot},{t:2,x:.4,y:.90625,z:0,balls:snapshot},{t:3,x:.7,y:.90625,z:0,balls:snapshot}];
    t.s.shot.contacts=[{t:3,ballIndex:target,evolution:3,x:.7,y:.90625,z:0,legal:true}];
    t.model.reqRoundResult(t.sim);assert.ok(t.s.lastResult.foulCode&core.FOUL.JUMP);assert.equal(t.s.lastResult.nextBallOn,expected);
    // The decision itself must also restore the canonical target if another
    // response or UI operation has changed context while the dialog is open.
    t.model._gContext.ballOn=252;
    t.api.resolveFoul('continue');assert.equal(t.model._gContext.playerIndex,1);assert.equal(t.g._fpc.gPlayerIndex,1);
    assert.equal(t.model._gContext.ballOn,expected);assert.equal(t.model.getContext('ballOn'),expected);assert.equal(t.s.nominatedColour,null);
  }
});

function touchingFixture(n=1,on=2){
  const t=setup(0);t.s.hotseat=true;const q=t.sim.getBallAtIndex(0),obj=t.sim.getBallAtIndex(n);
  Object.assign(obj.position,{x:q.position.x+2*q.radius,z:q.position.z});
  Object.assign(t.model._gContext,{ballOn:on,playerIndex:0});t.model._response(t.sim);return t;
}
function solved(t,i,j,closeSpeed,deltaJ,deltaI){
  t.sim._world.solver.solveContact({isSS:true,bi:t.sim.getBallAtIndex(i),bj:t.sim.getBallAtIndex(j),getCloseSpeed:()=>closeSpeed,deltaJ,deltaI});
}
test('touching red play-away is displayed and does not become an empty-stroke foul',()=>{
  const t=touchingFixture();assert.match(t.s.shadow.querySelector('.status').textContent,/贴球：红球/);
  assert.equal(t.model.reportPlayerStroke(0),true);t.sim.stroke({x:-1,y:0,z:0});
  const q=t.sim.getBallAtIndex(0);q.position.x-=.1;t.sim._world.internalStep();t.model.reqRoundResult(t.sim);
  assert.equal(t.s.lastResult.foulCode,0);assert.equal(t.s.lastResult.touching.deemedHit,true);
});
test('initial solver impulse into a touching red is a push stroke',()=>{
  const t=touchingFixture();assert.equal(t.model.reportPlayerStroke(0),true);t.sim.stroke({x:1,y:0,z:0});
  solved(t,0,1,-1,{x:.5});t.model.reqRoundResult(t.sim);
  assert.equal(t.s.lastResult.score,-4);assert.ok(t.s.lastResult.foulCode&core.FOUL.PUSH);assert.deepEqual(t.s.lastResult.touching.pushedIndices,[1]);
});
test('static and separating presolve contacts are not counted as physical first hits',()=>{
  const t=touchingFixture();t.model.reportPlayerStroke(0);t.sim.stroke({x:-1,y:0,z:0});
  t.sim._world.touchPresolveHandler({isSS:true,bi:t.sim.getBallAtIndex(0),bj:t.sim.getBallAtIndex(1)});
  solved(t,0,1,0);solved(t,0,1,1);assert.equal(t.s.shot.contacts.length,0);
});
test('playing away then returning to a touching red is not an initial push',()=>{
  const t=touchingFixture();t.model.reportPlayerStroke(0);t.sim.stroke({x:-1,y:0,z:0});
  solved(t,0,1,-1,{x:.5});t.model.reqRoundResult(t.sim);
  assert.equal(t.s.lastResult.foulCode,0);assert.deepEqual(t.s.lastResult.touching.pushedIndices,[]);
});
test('another ball moving the touching object is not mistaken for a push',()=>{
  const t=touchingFixture();t.model.reportPlayerStroke(0);t.sim.stroke({x:0,y:0,z:1});
  solved(t,7,1,-1,{x:.3});solved(t,0,1,-1,{x:.2});t.model.reqRoundResult(t.sim);
  assert.equal(t.s.lastResult.foulCode,0);assert.deepEqual(t.s.lastResult.touching.pushedIndices,[]);
});
test('an actual resting cushion rebound releases the initial touching watch',()=>{
  const t=touchingFixture();t.model.reportPlayerStroke(0);t.sim.stroke({x:0,y:0,z:1});
  t.sim._world.solver.solveContact({isSS:false,bi:t.sim.getBallAtIndex(0),bj:{normal:{x:1,y:0,z:0}},normal:{x:1,y:0,z:0},getCloseSpeed:()=>-1,deltaI:{x:.5}});
  solved(t,0,1,-1,{x:.5});t.model.reqRoundResult(t.sim);
  assert.equal(t.s.lastResult.foulCode,0);assert.deepEqual(t.s.lastResult.touching.pushedIndices,[]);assert.equal(t.s.lastContacts[0].kind,'cushion');
});
test('touching a colour forces an explicit choice even if the aim looks obvious',()=>{
  const t=touchingFixture(3,252);t.g._fpc.getKissDir=()=>({x:-1,z:0});
  assert.equal(t.model.reportPlayerStroke(0),false);assert.match(t.s.shadow.querySelector('p').textContent,/白球贴着彩球/);
  t.buttons().find(b=>b.textContent==='绿球').onclick();assert.equal(t.model.reportPlayerStroke(0),true);
  assert.equal(t.s.shot.before.touching.deemedHit,true);
});
test('touching a non-target still requires a real target contact after playing away',()=>{
  const t=touchingFixture(7);t.model.reportPlayerStroke(0);t.sim.stroke({x:-1,y:0,z:0});
  t.sim.getBallAtIndex(0).position.x-=.1;t.sim._world.internalStep();t.model.reqRoundResult(t.sim);
  assert.equal(t.s.lastResult.score,-4);assert.ok(t.s.lastResult.foulCode&core.FOUL.MISS);
});
