'use strict';
const test=require('node:test');
const assert=require('node:assert/strict');
const C=require('../src/rules-core.js');
const b=(i,n,x,z=0,extra={})=>({i,n,active:true,x,y:C.RADIUS,z,...extra});
const cue=b(0,0,0);
const set=[cue,b(1,1,1),b(2,1,1.1,.1),b(3,2,-1,-.3),b(4,3,-1,.3),b(5,4,-1),b(6,5,0,.7),b(7,6,.8,.5),b(8,7,1.3,.5)];
const shot=overrides=>C.adjudicate({ballOn:2,balls:set,firstHits:[1],...overrides});

test('pink respot prefers the top side even when the Baulk side is closer',()=>{
  const pink=b(20,6,.86,0,{active:false}),blocker=b(1,1,.885);
  const x=C.pinkRespotX([pink,blocker],pink,-1.77,1.77);
  assert.ok(Math.abs(x-(blocker.x+2*C.RADIUS+2*C.TOUCH_EPS))<1e-10);
  assert.ok(x-blocker.x>2*C.RADIUS+C.TOUCH_EPS);
});
test('pink respot uses the nearest Baulk-side gap only when the top side is full',()=>{
  const pink=b(20,6,.86,0,{active:false});
  const blockers=Array.from({length:13},(_,i)=>b(i+1,1,.89+i*.07));
  const x=C.pinkRespotX([pink,...blockers],pink,-1.77,1.77);
  assert.ok(Math.abs(x-(.89-2*C.RADIUS-2*C.TOUCH_EPS))<1e-10);
});

test('remaining maximum includes final colour after the last red',()=>{
  const colours=[cue,...[2,3,4,5,6,7].map((n,i)=>b(16+i,n,i))];
  assert.equal(C.remainingPoints([...colours,...Array.from({length:15},(_,i)=>b(i+1,1,i))],2),147);
  assert.equal(C.remainingPoints(colours,252),34);
  assert.equal(C.remainingPoints(colours,4),27);
  assert.equal(C.remainingPoints(colours.filter(v=>v.n===0||v.n>=6),64),13);
});
test('free ball adds possible points before deciding a frame is twenty over',()=>{
  const colours=[cue,...[2,3,4,5,6,7].map((n,i)=>b(16+i,n,i))];
  assert.equal(C.remainingPoints([...colours,b(1,1,1)],2,{freeBall:true}),43);
  assert.equal(C.remainingPoints(colours,4,{freeBall:true}),29);
  assert.equal(C.concessionStatus({balls:colours,ballOn:4,scores:[0,47],playerIndex:0,freeBall:true}).eligible,false);
});
test('concession is available at twenty over, not merely twenty behind',()=>{
  const colours=[cue,...[2,3,4,5,6,7].map((n,i)=>b(16+i,n,i))];
  const status=score=>C.concessionStatus({balls:colours,ballOn:4,scores:[0,score],playerIndex:0});
  assert.equal(status(20).eligible,false);assert.equal(status(46).eligible,false);
  assert.deepEqual(status(47),{eligible:true,playerIndex:0,remaining:27,deficit:47,excess:20,threshold:20});
  assert.equal(status(48).eligible,true);
});
test('leader, practice and an already-ended frame cannot concede through this option',()=>{
  const args={balls:[cue,b(21,7,1)],ballOn:128,scores:[0,30],playerIndex:0};
  assert.equal(C.concessionStatus({...args,playerIndex:1}).eligible,false);
  assert.equal(C.concessionStatus({...args,ballOn:0}).eligible,false);
  assert.equal(C.concessionStatus({...args,ballOn:65535}).eligible,false);
  assert.equal(C.concessionStatus({...args,scores:[0]}).eligible,false);
});

test('bitmasks enumerate red, optional colours, and final colour',()=>{
  assert.deepEqual(C.ballOnNumbers(2),[1]);assert.deepEqual(C.ballOnNumbers(252),[2,3,4,5,6,7]);assert.deepEqual(C.ballOnNumbers(128),[7]);
});
test('cushion alone cannot cause a snooker',()=>{
  const r=C.isSnookered([cue,b(1,1,1)],2,undefined,{cushions:[{x:.5,z:0}]});
  assert.equal(r.snookered,false);assert.deepEqual(r.clearTargets,[1]);
});
test('blocking only one extreme edge is a snooker but still a direct hit',()=>{
  const balls=[cue,b(1,1,1),b(2,7,.5,.045)];
  const r=C.isSnookered(balls,2);assert.equal(r.snookered,true);
  assert.notEqual(r.details[0].leftBlockedBy.length,r.details[0].rightBlockedBy.length);
  assert.equal(C.hasDirectHit(balls,2).hasDirectHit,true);
});
test('another visible red suffices, and reds do not snooker reds',()=>{
  assert.equal(C.isSnookered([cue,b(1,1,1),b(2,7,.5),b(3,1,1,.5)],2).snookered,false);
  assert.equal(C.isSnookered([cue,b(1,1,1),b(2,1,.5)],2).snookered,false);
  assert.equal(C.hasDirectHit([cue,b(1,1,1),b(2,1,.5)],2).target,2);
});
test('ball behind target cannot cause a snooker',()=>assert.equal(C.isSnookered([cue,b(1,1,1),b(2,7,1.2)],2).snookered,false));
test('central blocker has no direct contact route',()=>assert.equal(C.hasDirectHit([cue,b(1,1,1),b(2,7,.5)],2).hasDirectHit,false));
test('direct-hit witness first touches target and permits narrow visible edge',()=>{
  const balls=[cue,b(1,1,2),b(2,7,1,.0266)];
  assert.equal(C.isSnookered(balls,2).snookered,true);
  const r=C.hasDirectHit(balls,2);assert.equal(r.hasDirectHit,true);assert.equal(r.target,1);assert.ok(r.direction.z<0);
});
test('D sampling cannot prove an in-hand snooker',()=>{
  for(const f of [C.isSnookered,C.hasDirectHit]){
    const r=f([cue,b(1,1,1),b(2,7,.5)],2,undefined,{inHand:true,positions:[cue]});
    assert.equal(r.indeterminate,true);assert.equal('snookered' in r?r.snookered:r.hasDirectHit,null);
  }
});
test('touching cue-target geometry is referred for a touching-ball ruling',()=>{
  assert.equal(C.isSnookered([cue,b(1,1,2*C.RADIUS)],2).snookered,null);
  assert.equal(C.hasDirectHit([cue,b(1,1,2*C.RADIUS)],2).hasDirectHit,null);
});

test('automatic colour nomination uses the first reachable ball, not colours behind it',()=>{
  const bs=[cue,b(19,5,1),b(20,6,2),b(21,7,3)];
  assert.deepEqual(C.inferColour(bs,{x:8,z:0}),{colour:5,ballIndex:19,reason:'direct'});
  assert.equal(C.inferColour(bs,{x:-1,z:0}).colour,null);
});

test('automatic nomination accepts a thin visible edge but asks about exact tangency',()=>{
  assert.equal(C.inferColour([cue,b(19,5,1,2*C.RADIUS-1e-6)],{x:1,z:0}).colour,5);
  assert.equal(C.inferColour([cue,b(19,5,1,2*C.RADIUS)],{x:1,z:0}).reason,'ambiguous');
});

test('a red blocker or a cushion-first aim cannot nominate an unrelated visible colour',()=>{
  assert.equal(C.inferColour([cue,b(1,1,.5),b(19,5,1),b(20,6,0,1)],{x:1,z:0}).reason,'blocked-by-red');
  assert.equal(C.inferColour([cue,b(19,5,0,1)],{x:1,z:0}).reason,'no-direct-target');
});

test('simultaneous first candidates and touching balls require a declaration',()=>{
  assert.equal(C.inferColour([cue,b(19,5,1,.03),b(20,6,1,-.03)],{x:1,z:0}).reason,'ambiguous');
  assert.equal(C.inferColour([cue,b(19,5,2*C.RADIUS)],{x:1,z:0}).reason,'touching');
  assert.equal(C.inferColour([cue,b(19,5,1)],{x:0,z:0}).reason,'invalid-aim');
});

const touchingSet=[cue,b(1,1,2*C.RADIUS),b(13,1,1.5),b(21,7,-1)];
const touchingShot=args=>C.adjudicate({ballOn:2,balls:touchingSet,touchingAtStart:[1],...args});
test('touching detection uses contact distance rather than visibly nearby balls',()=>{
  const info=C.touchingStatus({balls:touchingSet,ballOn:2});assert.deepEqual(info.indices,[1]);assert.equal(info.deemedHit,true);
  assert.equal(C.touchingStatus({balls:[cue,b(1,1,2*C.RADIUS+.001)],ballOn:2}).deemedHit,false);
});
test('playing away from a touching red satisfies first contact even with no later hit',()=>{
  const result=touchingShot({});assert.equal(result.foulCode,0);assert.equal(result.score,0);assert.equal(result.touching.deemedHit,true);
});
test('a touching red permits the black-red plant; pocketing the black remains illegal',()=>{
  const result=touchingShot({firstHits:[21],potted:[13]});assert.equal(result.foulCode,0);assert.equal(result.score,1);assert.equal(result.nextBallOn,252);
  assert.equal(touchingShot({firstHits:[21],potted:[21,13]}).score,-7);
});
test('touching a non-target does not exempt missing or hitting the wrong ball',()=>{
  assert.equal(touchingShot({touchingAtStart:[21]}).score,-4);
  const result=touchingShot({touchingAtStart:[21],firstHits:[21]});assert.equal(result.score,-7);assert.ok(result.foulCode&C.FOUL.FIRST_HIT);
});
test('a touching colour requires declaration; only the chosen touching colour is deemed hit',()=>{
  const bs=[cue,b(17,3,2*C.RADIUS),b(21,7,-1)];
  const args={balls:bs,ballOn:252,touchingAtStart:[17]};
  assert.equal(C.touchingStatus({...args,nominatedColour:7}).requiresColourDeclaration,true);
  assert.equal(C.adjudicate({...args,nominatedColour:3}).score,0);
  assert.equal(C.adjudicate({...args,nominatedColour:7}).score,-7);
  assert.equal(C.adjudicate({...args,nominatedColour:7,firstHits:[21],potted:[21]}).score,7);
});
test('touching the nominated free ball counts; touching only the original target does not',()=>{
  const args={balls:[...touchingSet,b(19,5,.5)],ballOn:2,freeBallNominee:19};
  assert.equal(C.adjudicate({...args,touchingAtStart:[19],firstHits:[21],potted:[13]}).score,1);
  const result=C.adjudicate({...args,touchingAtStart:[1]});assert.equal(result.score,-4);assert.equal(result.touching.deemedHit,false);
});
test('initially pushing touching balls incurs the highest relevant penalty',()=>{
  const red=touchingShot({firstHits:[1],pushedTouching:[1]});assert.equal(red.score,-4);assert.ok(red.foulCode&C.FOUL.PUSH);
  const black=touchingShot({touchingAtStart:[1,21],firstHits:[21],pushedTouching:[1,21]});assert.equal(black.score,-7);assert.ok(black.foulCode&C.FOUL.PUSH);
});

const jb=(i,n,x,z=0)=>b(i,n,x,z,{r:.1,y:.1});
const jumpBalls=[jb(0,0,0),jb(1,7,1)];
const tr=points=>points.map(([x,y,z=0],t)=>({t,x,y,z,balls:jumpBalls.map(v=>({...v}))}));
const over=tr([[0,.1],[.6,.1],[.8,.5],[1,.5],[1.2,.5],[1.5,.1]]);
test('legal airborne stroke without passing over any ball is not a jump foul',()=>{
  const trace=tr([[0,.1],[.5,.5,1],[1,.5,1],[1.5,.1,1]]);
  assert.equal(C.evaluateJump(trace,jumpBalls,[],.1).foul,false);
});
test('cue passing above an obstacle without contact is a jump foul',()=>{
  const r=C.evaluateJump(over,jumpBalls,[],.1);assert.equal(r.foul,true);assert.deepEqual(r.offendingBalls,[1]);
});
test('swept geometry catches crossing between samples',()=>{
  const r=C.evaluateJump(tr([[0,.1],[.6,.5],[1.4,.5],[1.5,.1]]),jumpBalls,[],.1);assert.equal(r.foul,true);
});
test('jump over a different ball after first contact is excepted',()=>{
  const balls=[...jumpBalls,jb(2,1,-.5)];
  const r=C.evaluateJump(over,balls,[{t:.2,ballIndex:2,legal:true}],.1);assert.equal(r.foul,false);assert.ok(r.details.some(d=>d.exception.startsWith('20(a)')));
});
test('a touching ball cannot be used as contact-first jump exception',()=>{
  const balls=[...jumpBalls,jb(2,1,-.2)];assert.equal(C.evaluateJump(over,balls,[{t:.2,ballIndex:2,legal:true}],.1).foul,true);
});
test('airborne contact and near-side landing is legal',()=>{
  const trace=tr([[0,.1],[.7,.5],[.9,.35],[.7,.35],[.5,.1]]);
  const r=C.evaluateJump(trace,jumpBalls,[{t:2,ballIndex:1}],.1);assert.equal(r.foul,false);assert.ok(r.details.some(d=>d.exception.startsWith('20(b)')));
});
test('airborne contact and definite far-side landing is illegal',()=>assert.equal(C.evaluateJump(over,jumpBalls,[{t:3,ballIndex:1}],.1).foul,true));
test('moving object current landing position is used for exception 20(b)',()=>{
  const trace=over.map(s=>({...s,balls:s.balls.map(v=>v.i===1?{...v,x:s.t>=3?1+(s.t-3)*.5:1}:v)}));
  const r=C.evaluateJump(trace,jumpBalls,[{t:2.5,ballIndex:1}],.1);assert.equal(r.foul,false);assert.ok(r.details.some(d=>d.exception && d.exception.startsWith('20(b)')));
});
test('no moving ball position at landing yields review instead of a false foul',()=>{
  const r=C.evaluateJump(over.map(({balls,...s})=>s),jumpBalls,[{t:3,ballIndex:1}],.1);assert.equal(r.foul,false);assert.equal(r.indeterminate,true);
});
test('legal hit then cushion then jump over same ball is excepted',()=>{
  const r=C.evaluateJump(over,jumpBalls,[{t:.2,ballIndex:1,legal:true},{t:.4,kind:'cushion'}],.1);assert.equal(r.foul,false);assert.ok(r.details.some(d=>d.exception.startsWith('20(c)')));
});
test('object that moves away from the projected path is not falsely jumped',()=>{
  const trace=over.map(s=>({...s,balls:s.balls.map(v=>v.i===1?{...v,z:s.t>=1?1:0}:v)}));assert.equal(C.evaluateJump(trace,jumpBalls,[],.1).foul,false);
});

test('red pot, colour pot, then red selection use game bitmasks',()=>{
  assert.deepEqual([shot({potted:[1]}).score,shot({potted:[1]}).nextBallOn],[1,252]);
  const colour=shot({ballOn:252,nominatedColour:7,firstHits:[8],potted:[8]});assert.equal(colour.score,7);assert.equal(colour.nextBallOn,2);assert.deepEqual(colour.respots,[8]);
});
test('last red still permits a colour before final yellow',()=>{
  const balls=set.filter(v=>v.i!==2);const red=shot({balls,potted:[1]});assert.equal(red.nextBallOn,252);
  const colour=shot({balls:balls.map(v=>v.i===1?{...v,active:false}:v),ballOn:252,nominatedColour:7,firstHits:[8],potted:[8]});assert.equal(colour.nextBallOn,4);
});
test('nominated no-contact colour gets its correct foul value',()=>{
  assert.equal(shot({ballOn:252,nominatedColour:5,firstHits:[]}).score,-5);
  assert.equal(shot({ballOn:252,nominatedColour:7,firstHits:[]}).score,-7);
  assert.equal(shot({ballOn:252,firstHits:[]}).score,-7);
});
test('multiple fouls award the highest penalty, not their sum',()=>{
  const r=shot({firstHits:[6],potted:[0],outOfBounds:[8],jumpFoul:true});assert.equal(r.score,-7);assert.equal(r.foulCode,2|8|16|32);assert.equal(r.requiresInHand,true);assert.deepEqual(r.respots,[8]);
});
test('ordinary miss, wrong pot and legal safety are distinguished',()=>{
  assert.equal(shot({firstHits:[]}).foulCode,1);assert.equal(shot({potted:[8]}).score,-7);assert.equal(shot({}).score,0);assert.equal(shot({}).nextBallOn,2);
});
test('simultaneous reds are legal; red and colour are not',()=>{
  assert.equal(shot({firstHits:[1,2]}).foulCode,0);assert.equal(shot({firstHits:[1,8]}).score,-7);
});
test('free ball and real red score separately, nominee respots',()=>{
  const r=shot({freeBallNominee:8,firstHits:[8],potted:[1,8]});assert.equal(r.score,2);assert.equal(r.nextBallOn,252);assert.deepEqual(r.respots,[8]);
});
test('free ball can cannon a real red in; real red first alone is a foul',()=>{
  assert.equal(shot({freeBallNominee:8,firstHits:[8],potted:[1]}).score,1);
  assert.equal(shot({freeBallNominee:8,firstHits:[1],potted:[1]}).score,-4);
  assert.equal(shot({freeBallNominee:8,firstHits:[1,8],potted:[1]}).score,1);
});
test('nominated free ball acquires canonical value for penalties',()=>{
  const r=shot({freeBallNominee:8,firstHits:[8],outOfBounds:[8]});assert.equal(r.score,-4);assert.deepEqual(r.respots,[8]);
});
test('free ball plus real final colour count only once and advance',()=>{
  const r=shot({ballOn:4,freeBallNominee:8,firstHits:[8],potted:[3,8]});assert.equal(r.score,2);assert.equal(r.nextBallOn,8);assert.deepEqual(r.respots,[8]);
});
test('free ball alone does not advance the final colour sequence',()=>{
  const r=shot({ballOn:4,freeBallNominee:8,firstHits:[8],potted:[8]});assert.equal(r.score,2);assert.equal(r.nextBallOn,4);assert.deepEqual(r.respots,[8]);
});
test('real final colour only remains off-table and advances',()=>{
  const r=shot({ballOn:4,freeBallNominee:8,firstHits:[8],potted:[3]});assert.equal(r.score,2);assert.equal(r.nextBallOn,8);assert.deepEqual(r.respots,[]);
});
test('illegal final colour pot is respotted; reds pocketed on foul stay off',()=>{
  const r=shot({ballOn:4,firstHits:[3],potted:[3,0]});assert.equal(r.score,-4);assert.equal(r.nextBallOn,4);assert.deepEqual(r.respots,[3]);
  assert.deepEqual(shot({potted:[1,8]}).respots,[8]);
});
test('free-ball safety behind effective nominated ball incurs foul',()=>{
  const r=shot({balls:[cue,b(1,1,1),b(8,7,.5)],firstHits:[8],freeBallNominee:8});assert.equal(r.foulCode,64);assert.equal(r.score,-4);
});
test('different effective snookering balls do not falsely incriminate nominee',()=>{
  const r=shot({balls:[cue,b(1,1,1),b(2,1,0,1),b(8,7,.5),b(7,6,0,.5)],firstHits:[8],freeBallNominee:8});assert.equal(r.foulCode,0);assert.deepEqual(r.freeBallSafety.effectiveSnookeringBalls,[]);
});
test('two remaining colours including black permit free-ball snooker',()=>{
  const r=shot({ballOn:64,balls:[cue,b(7,6,1),b(8,7,.5)],firstHits:[8],freeBallNominee:8});assert.equal(r.foulCode,0);
});
test('all helpers leave their inputs unchanged',()=>{
  const original=JSON.stringify(set);shot({freeBallNominee:8,potted:[1,8],firstHits:[8]});C.isSnookered(set,2);C.hasDirectHit(set,2);assert.equal(JSON.stringify(set),original);
});
