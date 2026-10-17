// ==UserScript==
// @name         PCOL Snooker Rules Patch
// @namespace    local.pcol.rules
// @version      0.16.0
// @description  Snooker rules, celebrations, practice layouts, stroke retry and isolated full-shot trials.
// @match        http://www.heyzxz.me/pcol/*
// @match        https://www.heyzxz.me/pcol/*
// @run-at       document-start
// @grant        unsafeWindow
// @grant        GM_xmlhttpRequest
// @connect      127.0.0.1
// @noframes
// @updateURL    https://raw.githubusercontent.com/1034701377-web/pcol-snooker-enhancements/main/outputs/pcol-rules-patch.user.js
// @downloadURL  https://raw.githubusercontent.com/1034701377-web/pcol-snooker-enhancements/main/outputs/pcol-rules-patch.user.js
// ==/UserScript==
(() => {
const window = typeof unsafeWindow === "undefined" ? globalThis.window : unsafeWindow;
const {Math,Number,Array,Object,Set,Map,WeakMap,WeakSet,JSON,Reflect,Float32Array,Float64Array,Uint8Array,Uint32Array,ArrayBuffer,DataView,String,Boolean,Date,Promise,Error,TypeError,RangeError,Infinity,NaN,performance,structuredClone}=globalThis;
/* Per-stroke Float64 trajectory. Native ball identity/radius are immutable;
 * every physics/contact sample retains position and active state unchanged.
 * Object rows are materialized only for explicit external trace exports. */
const PCOLShotTrace = (() => {
  function create(nativeBalls, {cap = 15000, seconds = false, chunkSize = 128} = {}) {
    const metadata = nativeBalls.map(b => ({i:b.index,n:b.number,r:b.radius}));
    const slots = new Map();
    for(let i=0;i<metadata.length;i++)if(!slots.has(metadata[i].i))slots.set(metadata[i].i,i);
    const stride = 1 + 4*metadata.length, chunks = [];
    const last = {t:0,x:0,y:0,z:0};
    let length = 0;
    function sample(balls, time) {
      if(length >= cap)return null;
      const chunkIndex = Math.floor(length/chunkSize), offset = (length%chunkSize)*stride;
      let data = chunks[chunkIndex];
      if(!data)data=chunks[chunkIndex]=new Float64Array(Math.min(chunkSize,cap-chunkIndex*chunkSize)*stride);
      data[offset]=time;
      for(let i=0;i<metadata.length;i++) {
        const b=balls[i],p=b.position,k=offset+1+i*4;
        data[k]=p.x;data[k+1]=p.y;data[k+2]=p.z;data[k+3]=b.active===false?0:1;
      }
      last.t=length++;last.x=data[offset+1];last.y=data[offset+2];last.z=data[offset+3];
      return last;
    }
    function readCue(index, out = {}) {
      const data=chunks[Math.floor(index/chunkSize)],offset=(index%chunkSize)*stride;
      out.t=index;out.x=data[offset+1];out.y=data[offset+2];out.z=data[offset+3];
      if(seconds)out.seconds=data[offset];
      return out;
    }
    function readBall(index, fallback, out = {}) {
      const slot=slots.get(fallback.i);
      if(slot===undefined){Object.assign(out,fallback);out.active=false;return out;}
      const data=chunks[Math.floor(index/chunkSize)],offset=(index%chunkSize)*stride+1+slot*4;
      const m=metadata[slot];
      out.i=m.i;out.n=m.n;out.r=m.r;
      out.x=data[offset];out.y=data[offset+1];out.z=data[offset+2];out.active=data[offset+3]!==0;
      return out;
    }
    function toArray() {
      const rows=new Array(length);
      for(let i=0;i<length;i++) {
        const row=readCue(i);
        row.balls=metadata.map(b=>readBall(i,b));rows[i]=row;
      }
      return rows;
    }
    function toCueArray() {
      const rows=new Array(length),point={};
      for(let i=0;i<length;i++) {
        readCue(i,point);rows[i]={t:point.t,x:point.x,z:point.z};
      }
      return rows;
    }
    return {get length(){return length;},sample,readCue,readBall,toArray,toCueArray,toJSON:toArray};
  }
  return {create};
})();

/* PCOL rule helpers. x/z are cloth coordinates; y is height. No game mutation.
 * WPBSA 2024-25: definitions 17/20, play 3/4/7/8/11/12.
 * https://wpbsa.com/wp-content/uploads/2198_WPBSA-Rulebook-2024-25.pdf
 */
const PCOLCore = (() => {
  'use strict';
  const RADIUS = 0.02625;
  const RED = 2, COLOUR_ALL = 252;
  const FOUL = Object.freeze({MISS:1, FIRST_HIT:2, POTTING:4, CUE_POTTED:8, OFF_TABLE:16, JUMP:32, FREE_BALL_SNOOKER:64, PUSH:128, DOUBLE_HIT:256});
  // Referee tolerance: the observed 0.188 mm resting gap counts as touching.
  // Keep physical spotting clearance independent of this judgement tolerance.
  const CONTACT_EPS = 1e-5, TOUCH_EPS = 2e-4;
  const unique = a => [...new Set(a)];
  const radius = (b, fallback = RADIUS) => b.r > 0 ? b.r : fallback;
  const hypot2 = (a, b) => Math.hypot(a.x - b.x, a.z - b.z);
  const active = b => b.active !== false;
  const ballOnNumbers = mask => [1,2,3,4,5,6,7].filter(n => (mask & (1 << n)) !== 0);

  // PCOL's x axis runs from Baulk to the black end. Leave a small gap beyond
  // the touching tolerance, and only consider Baulk after the top side is full.
  function pinkRespotX(balls, pink, minX, maxX) {
    const intervals=[];
    for(const b of balls){
      if(!active(b)||b.i===pink.i)continue;
      const rr=radius(pink)+radius(b)+2*CONTACT_EPS;
      const across=(b.y-pink.y)**2+(b.z-pink.z)**2;
      if(across>=rr*rr)continue;
      const half=Math.sqrt(rr*rr-across);
      intervals.push([b.x-half,b.x+half]);
    }
    intervals.sort((a,b)=>a[0]-b[0]);
    const blocked=[];
    for(const range of intervals){
      const last=blocked[blocked.length-1];
      if(last&&range[0]<last[1])last[1]=Math.max(last[1],range[1]);
      else blocked.push(range);
    }
    let x=pink.x;
    for(const [left,right] of blocked){
      if(x<=left)break;
      if(x<right)x=right;
    }
    if(x<=maxX)return x;
    x=pink.x;
    for(let i=blocked.length-1;i>=0;i--){
      const [left,right]=blocked[i];
      if(x>=right)break;
      if(x>left)x=left;
    }
    return x>=minX?x:null;
  }

  function touchingStatus({balls,ballOn,nominatedColour=null,freeBallNominee=null}) {
    const cue=balls.find(b=>b.n===0 && active(b));
    const touched=cue?balls.filter(b=>b.n>0 && active(b) && Math.hypot(cue.x-b.x,cue.y-b.y,cue.z-b.z)<=radius(cue)+radius(b)+TOUCH_EPS):[];
    const on=ballOn===COLOUR_ALL?(nominatedColour?[nominatedColour]:[]):ballOnNumbers(ballOn);
    const eligible=freeBallNominee!=null?touched.filter(b=>b.i===freeBallNominee):touched.filter(b=>on.includes(b.n));
    return {indices:touched.map(b=>b.i),eligibleIndices:eligible.map(b=>b.i),deemedHit:eligible.length>0,requiresColourDeclaration:ballOn===COLOUR_ALL && touched.some(b=>b.n>=2),tolerance:TOUCH_EPS};
  }

  function remainingPoints(balls, ballOn, {freeBall = false} = {}) {
    if (!ballOn || ballOn === 65535) return 0;
    const live = balls.filter(b => active(b) && b.n > 0);
    const reds = live.filter(b => b.n === 1).length;
    let maximum = reds || ballOn === COLOUR_ALL ? reds * 8 + 27 + (ballOn === COLOUR_ALL ? 7 : 0) : live.filter(b => b.n >= 2).reduce((sum,b) => sum+b.n,0);
    if (freeBall) maximum += ballOn === RED ? 8 : ballOn === COLOUR_ALL ? 7 : ballOnNumbers(ballOn)[0] || 0;
    return maximum;
  }

  // User-requested optional concession threshold, not a mandatory match rule.
  function concessionStatus({balls, ballOn, scores, playerIndex, freeBall = false, threshold = 1}) {
    const maximum = remainingPoints(balls,ballOn,{freeBall});
    const valid = scores.length === 2 && (playerIndex === 0 || playerIndex === 1) && ballOn > 0 && ballOn !== 65535;
    const deficit = valid ? scores[1-playerIndex]-scores[playerIndex] : 0;
    const excess = deficit-maximum;
    return {eligible:valid && excess >= threshold,playerIndex,remaining:maximum,deficit,excess,threshold};
  }

  /** User-customised early finish, separate from the official final-black rule.
   * Supply settled post-stroke balls/scores, including foul penalties and respots.
   * A known free-ball opportunity adds its possible points; unresolved review
   * cannot establish an early finish. Omit actor/continueBreak for a stable turn.
   * At 17 over only the leader's legal scoring break may continue. The separate
   * blackLeadThreshold is a score lead (default 8), not points over the table.
   * On the last Black, playerIndex is the incoming player: the leader keeps
   * their shot, including after potting Pink; the trailing player's turn ends it.
   */
  function earlyFrameOutcome({balls,ballOn,scores,playerIndex=null,actor=null,continueBreak=false,freeBall=false,freeBallReview=false,threshold=17,blackLeadThreshold=8}) {
    if(!Array.isArray(balls)||!Array.isArray(scores)||scores.length!==2||!scores.every(Number.isFinite)||
      !ballOn||ballOn===65535||freeBallReview||freeBall==null||scores[0]===scores[1])return null;
    const winner=scores[0]>scores[1]?0:1,loser=1-winner;
    const deficit=scores[winner]-scores[loser],remaining=remainingPoints(balls,ballOn,{freeBall}),excess=deficit-remaining;
    const live=balls.filter(b=>b.n>0&&active(b));
    if(ballOn===128&&live.length===1&&live[0].n===7&&Number.isFinite(blackLeadThreshold)&&deficit>=blackLeadThreshold)
      return playerIndex===loser?{winner,loser,deficit,remaining,excess,threshold:blackLeadThreshold,reason:'black-lead'}:null;
    if(Number.isFinite(threshold)&&excess>=threshold&&!(actor===winner&&continueBreak===true))
      return {winner,loser,deficit,remaining,excess,threshold,reason:'excess-threshold'};
    return null;
  }

  // Earliest intersection of a cue-centre ray with a ball's expanded disc.
  function rayBlocker(cue, direction, length, b, cueRadius, eps) {
    const dx = b.x - cue.x, dz = b.z - cue.z;
    const projection = dx * direction.x + dz * direction.z;
    const rr = cueRadius + radius(b);
    const perpendicular2 = dx * dx + dz * dz - projection * projection;
    if (perpendicular2 >= rr * rr - eps || projection + rr < 0) return false;
    const enter = projection - Math.sqrt(Math.max(0, rr * rr - perpendicular2));
    return enter < length - eps && projection + Math.sqrt(Math.max(0, rr * rr - perpendicular2)) > eps;
  }

  /** Both extreme physical contacts must be available on at least one ball on.
   * Cushions and other balls on cannot cause a snooker under definition 17.
   * options.inHand requires an all-positions proof which this helper does not
   * attempt: it returns null, never true based on a finite sample of the D.
   * Effective blockers are returned for the free-ball safety restriction.
   */
  function isSnookered(balls, ballOn, cuePosition, options = {}) {
    if (options.inHand) return {snookered:null, indeterminate:true, clearTargets:[], details:[], effectiveSnookeringBalls:[], reason:'All legal cue positions in the D must be considered.'};
    const cue = cuePosition || balls.find(b => b.n === 0 && active(b));
    const on = ballOnNumbers(ballOn);
    const targets = balls.filter(b => active(b) && on.includes(b.n));
    if (!cue || targets.length === 0) return {snookered:null, indeterminate:true, clearTargets:[], details:[], effectiveSnookeringBalls:[], reason:'Cue position or ball on unavailable.'};
    const rc = radius(cue, options.radius || RADIUS), eps = options.epsilon || 1e-8;
    const blockers = balls.filter(b => active(b) && b.n > 0 && !on.includes(b.n));
    const details = targets.map(target => {
      const distance = hypot2(cue, target), rr = rc + radius(target);
      if (distance <= rr + eps) return {target:target.i, indeterminate:true, leftBlockedBy:[], rightBlockedBy:[], effective:[]};
      const angle = Math.atan2(target.z - cue.z, target.x - cue.x);
      const halfAngle = Math.asin(Math.min(1, rr / distance));
      const travel = Math.sqrt(distance * distance - rr * rr);
      const edge = sign => {
        const theta = angle + sign * halfAngle;
        const direction = {x:Math.cos(theta), z:Math.sin(theta)};
        return blockers.filter(b => rayBlocker(cue, direction, travel, b, rc, eps)).map(b => b.i);
      };
      const leftBlockedBy = edge(1), rightBlockedBy = edge(-1);
      const both = unique([...leftBlockedBy, ...rightBlockedBy]);
      const nearest = Math.min(...both.map(i => hypot2(cue, balls.find(b => b.i === i))));
      const effective = both.filter(i => Math.abs(hypot2(cue, balls.find(b => b.i === i)) - nearest) <= eps);
      return {target:target.i, leftBlockedBy, rightBlockedBy, effective, clear:both.length === 0};
    });
    const clearTargets = details.filter(d => d.clear).map(d => d.target);
    const indeterminate = !clearTargets.length && details.some(d => d.indeterminate);
    const snookered = clearTargets.length ? false : indeterminate ? null : true;
    let effectiveSnookeringBalls = snookered ? details[0].effective.slice() : [];
    for (const d of details) effectiveSnookeringBalls = effectiveSnookeringBalls.filter(i => d.effective.includes(i));
    return {snookered, indeterminate, clearTargets, details, effectiveSnookeringBalls};
  }

  /** Proves visibility of any part of a legal ball, not both extreme edges.
   * Ray collision order can only change at disc tangent angles or the angles
   * of expanded-disc intersections. Test each angular cell plus its boundaries.
   * This handles arbitrarily narrow positive gaps without a fixed angle grid.
   */
  function hasDirectHit(balls, ballOn, cuePosition, options = {}) {
    const unknown=reason=>({hasDirectHit:null,indeterminate:true,target:null,direction:null,reason});
    if(options.inHand) return unknown('All legal cue positions in the D must be considered.');
    const cue=cuePosition || balls.find(b=>b.n===0 && active(b));
    if(!cue) return unknown('Cue position unavailable.');
    const on=ballOnNumbers(ballOn), rc=radius(cue,options.radius || RADIUS),eps=options.epsilon || 1e-9;
    const objects=balls.filter(b=>b.n>0 && active(b));
    if(!objects.some(b=>on.includes(b.n))) return unknown('Ball on unavailable.');
    const circles=objects.map(b=>({b,x:b.x-cue.x,z:b.z-cue.z,r:rc+radius(b)}));
    const tau=2*Math.PI,normal=a=>(a%tau+tau)%tau;
    const angles=[];
    let touching=false;
    for(const c of circles) {
      const d=Math.hypot(c.x,c.z);
      if(d<=c.r+eps){touching=true;continue;}
      const angle=Math.atan2(c.z,c.x),h=Math.asin(c.r/d);
      angles.push(normal(angle-h),normal(angle+h),normal(angle));
    }
    for(let i=0;i<circles.length;i++) for(let j=i+1;j<circles.length;j++) {
      const a=circles[i],b=circles[j],dx=b.x-a.x,dz=b.z-a.z,d=Math.hypot(dx,dz);
      if(d<=eps || d>a.r+b.r+eps || d<Math.abs(a.r-b.r)-eps)continue;
      const along=(a.r*a.r-b.r*b.r+d*d)/(2*d),height=Math.sqrt(Math.max(0,a.r*a.r-along*along));
      const x=a.x+along*dx/d,z=a.z+along*dz/d;
      angles.push(normal(Math.atan2(z+height*dx/d,x-height*dz/d)),normal(Math.atan2(z-height*dx/d,x+height*dz/d)));
    }
    angles.sort((a,b)=>a-b);
    const candidates=angles.slice();
    for(let i=0;i<angles.length;i++)candidates.push(normal((angles[i]+(i+1<angles.length?angles[i+1]:angles[0]+tau))/2));
    for(const angle of candidates) {
      const direction={x:Math.cos(angle),z:Math.sin(angle)};
      const entries=[];
      for(const c of circles) {
        const projection=c.x*direction.x+c.z*direction.z;
        const discriminant=c.r*c.r-(c.x*c.x+c.z*c.z-projection*projection);
        if(discriminant < -eps) continue;
        const root=Math.sqrt(Math.max(0,discriminant)),near=projection-root,far=projection+root;
        if(far<eps)continue;
        entries.push({i:c.b.i,n:c.b.n,t:Math.max(0,near)});
      }
      if(!entries.length)continue;
      const nearest=Math.min(...entries.map(e=>e.t));
      const first=entries.filter(e=>Math.abs(e.t-nearest)<=eps);
      if(first.every(e=>on.includes(e.n)) && nearest>eps) {
        const point={x:cue.x+direction.x*nearest,y:cue.y,z:cue.z+direction.z*nearest};
        if(options.isPathClear && !options.isPathClear(cue,point))continue;
        return {hasDirectHit:true,indeterminate:false,target:first[0].i,direction,contactPoint:point,reason:'Direct first contact with a ball on is available.'};
      }
    }
    if(touching) return unknown('Cue is touching or overlapping an object; touching-ball ruling required.');
    return {hasDirectHit:false,indeterminate:false,target:null,direction:null,reason:'Every straight ray to a ball on first meets a ball not on.'};
  }

  // Nominate BEFORE the stroke from the current horizontal aim, never from its
  // eventual outcome. A farther ball on the same ray cannot obscure the intent
  // to hit the nearer ball. Touching/tangent/tied contacts need a declaration.
  function inferColour(balls, direction) {
    const unknown = reason => ({colour:null,ballIndex:null,reason});
    const cue = balls.find(b => b.n === 0 && active(b));
    const length = Math.hypot(direction?.x, direction?.z);
    if (!cue || !Number.isFinite(length) || length < 1e-9) return unknown('invalid-aim');
    const dx = direction.x / length, dz = direction.z / length, entries = [];
    for (const b of balls) {
      if (!active(b) || b.n < 1) continue;
      const x = b.x-cue.x, z = b.z-cue.z, rr = radius(cue)+radius(b);
      if (Math.hypot(x,z) <= rr+1e-8) return unknown('touching');
      const projection = x*dx+z*dz;
      const disc = rr*rr-(x*x+z*z-projection*projection);
      if (projection <= 0 || disc < -1e-12) continue;
      entries.push({b,t:projection-Math.sqrt(Math.max(0,disc)),tangent:disc <= 1e-12});
    }
    entries.sort((a,b) => a.t-b.t);
    if (!entries.length) return unknown('no-direct-target');
    const first = entries[0];
    if (first.tangent || entries[1] && entries[1].t-first.t < 1e-7) return unknown('ambiguous');
    if (first.b.n < 2) return unknown('blocked-by-red');
    return {colour:first.b.n,ballIndex:first.b.i,reason:'direct'};
  }

  function lerp(a, b, u) { return {x:a.x+(b.x-a.x)*u, y:a.y+(b.y-a.y)*u, z:a.z+(b.z-a.z)*u}; }
  function sampleBall(sample, b, indexed) {
    if (!sample.balls) return b;
    // Only rows whose IDs exactly match every array index may bypass find.
    // Other rows retain its first-match behavior, including duplicate IDs.
    const found = indexed && Number.isInteger(b.i) && b.i>=0 && b.i<sample.balls.length ? sample.balls[b.i] : sample.balls.find(v => v.i === b.i);
    return found || {...b,active:false};
  }
  function traceReader(trace) {
    if(typeof trace.readCue==='function' && typeof trace.readBall==='function')
      return {length:trace.length,cue:(k,out)=>trace.readCue(k,out),ball:(k,b,out)=>trace.readBall(k,b,out),hasBalls:()=>true};
    // Validate legacy object rows locally. Non-indexed/duplicate IDs retain
    // the original first-match lookup and missing-ball behavior.
    const indexedRows=new Uint8Array(trace.length);
    for(let k=0;k<trace.length;k++) {
      const row=trace[k].balls;
      if(!row)continue;
      let indexed=true;
      for(let i=0;i<row.length;i++)if(!row[i] || row[i].i!==i){indexed=false;break;}
      if(indexed)indexedRows[k]=1;
    }
    return {length:trace.length,cue:k=>trace[k],ball:(k,b)=>sampleBall(trace[k],b,indexedRows[k]),hasBalls:k=>!!trace[k].balls};
  }
  function ballAt(reader, b, t) {
    const a={},next={},objectA={},objectB={};
    let j = 0;
    while (j + 1 < reader.length && reader.cue(j+1,next).t < t) j++;
    if (j + 1 === reader.length) return reader.ball(j,b,objectA);
    const current=reader.cue(j,a),following=reader.cue(j+1,next);
    const u = Math.max(0, Math.min(1, (t-current.t) / (following.t-current.t || 1)));
    return lerp(reader.ball(j,b,objectA),reader.ball(j+1,b,objectB),u);
  }

  // Relative swept-disc overlap, retaining only points with the cue above
  // the object's surface. Merely lifting the cue/using masse is not a foul.
  function sweptOver(a, b, objectA, objectB, rr, eps) {
    const py=a.y-objectA.y,vy=b.y-objectB.y-py,endY=py+vy;
    // Use the same relative-height interpolation as below, including its
    // rounded endpoint. A finite linear segment cannot rise above both ends.
    // Non-finite inputs retain the original conservative geometry path.
    if(Number.isFinite(py)&&Number.isFinite(vy)&&Number.isFinite(endY)&&py<=eps&&endY<=eps)return null;
    const px=a.x-objectA.x,pz=a.z-objectA.z;
    const vx=b.x-objectB.x-px,vz=b.z-objectB.z-pz;
    const limit2=(rr-eps)*(rr-eps);
    const A = vx*vx+vz*vz, B = 2*(px*vx+pz*vz), C = px*px+pz*pz-limit2;
    let lo = 0, hi = 1;
    if (A < eps*eps) { if (C >= 0) return null; }
    else {
      const D = B*B-4*A*C;
      if (D <= 0) return null;
      lo = Math.max(0,(-B-Math.sqrt(D))/(2*A));
      hi = Math.min(1,(-B+Math.sqrt(D))/(2*A));
      if (lo > hi) return null;
    }
    // Total distance squared is convex. Endpoints and horizontal closest
    // approach catch above-surface passage without treating overlap caused
    // by the collision solver's penetration tolerance as an illegal jump.
    const near = A > 0 ? Math.max(lo,Math.min(hi,-B/(2*A))) : (lo+hi)/2;
    for (let i=0;i<4;i++) {
      const u=i===0?near:i===1?(lo+hi)/2:i===2?lo+(hi-lo)*1e-4:hi-(hi-lo)*1e-4;
      const qx=px+u*vx, qy=py+u*vy, qz=pz+u*vz;
      const horizontal2 = qx*qx+qz*qz;
      if (qy > eps && horizontal2 < limit2 && horizontal2+qy*qy >= limit2) return {u,position:lerp(a,b,u)};
    }
    return null;
  }

  /** Physics-step trace; optional trace[k].balls records moving object centres.
   * contactEvents: {t,ballIndex,legal?}; cushions: {t,kind:'cushion'}.
   * legal is only needed for exception 20(c). Missing legal metadata is treated
   * conservatively; other rule checks still reject an illegal first hit.
   * Borderline/unfinished airborne paths are indeterminate, not auto-penalised.
   */
  function evaluateJump(trace, ballsAtStart, contactEvents = [], fallbackRadius = RADIUS) {
    if (!trace || trace.length < 2) return {foul:false, offendingBalls:[], reason:'Insufficient trajectory.', indeterminate:true, details:[]};
    const reader=traceReader(trace);
    const cue = ballsAtStart.find(b => b.n === 0) || {r:fallbackRadius,...reader.cue(0,{})};
    const rc = radius(cue,fallbackRadius), eps = Math.max(1e-6,rc*0.002);
    const groundY = cue.y;
    const events = contactEvents.slice().sort((a,b) => a.t-b.t);
    const objects = ballsAtStart.filter(b => b.n > 0 && active(b));
    const touching = new Set(objects.filter(b => Math.hypot(cue.x-b.x,cue.y-b.y,cue.z-b.z) <= rc+radius(b,fallbackRadius)+eps).map(b => b.i));
    const contacts = events.filter(e => e.ballIndex != null && objects.some(b => b.i === e.ballIndex));
    const first = contacts[0];
    const offendingBalls = [], details = [];
    let indeterminate = false;
    const cueA={},cueB={},objectA={},objectB={},takeoff={},landing={};
    for (const object of objects) {
      const passages=[];
      let wasOver=false;
      let previous=reader.ball(0,object,objectA);
      for (let k=0;k<trace.length-1;k++) {
        const a=reader.cue(k,cueA),b=reader.cue(k+1,cueB),oa=previous,ob=reader.ball(k+1,object,k%2?objectA:objectB);
        previous=ob;
        if (oa.active === false || ob.active === false) {wasOver=false;continue;}
        const over=sweptOver(a,b,oa,ob,rc+radius(object,fallbackRadius),eps);
        if (over && !wasOver) passages.push({k,t:a.t+(b.t-a.t)*over.u,position:over.position});
        wasOver=!!over;
      }
      for(const passage of passages) {
      const detail = {ballIndex:object.i,t:passage.t};
      if (first && first.t <= passage.t && first.ballIndex !== object.i && !touching.has(first.ballIndex)) {
        details.push({...detail,exception:'20(a): first hit another non-touching object ball.'});
        continue;
      }
      const prior = contacts.find(e => e.ballIndex===object.i && e.t<=passage.t && !touching.has(e.ballIndex));
      if (prior && prior.legal !== false && events.some(e => e.t > prior.t && e.t < passage.t && (e.kind==='cushion' || (e.ballIndex!=null && e.ballIndex!==object.i)))) {
        details.push({...detail,exception:'20(c): returned after object/cushion contact.'});
        continue;
      }
      // Find the takeoff and landing belonging to this airborne passage.
      let start=passage.k;
      while(start>0 && reader.cue(start,takeoff).y>groundY+eps) start--;
      let land=passage.k+1;
      while(land<trace.length && reader.cue(land,landing).y>groundY+eps) land++;
      const startPoint=reader.cue(start,takeoff),landPoint=land<trace.length?reader.cue(land,landing):null;
      const hitDuringFlight = contacts.find(e => e.ballIndex===object.i && e.t>=startPoint.t && (!landPoint || e.t<=landPoint.t));
      if (hitDuringFlight && !touching.has(object.i)) {
        if (land===trace.length) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball; landing not yet recorded.'});continue;}
        if(!reader.hasBalls(land)) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball current position at landing is unavailable.'});continue;}
        const objectAtLanding=ballAt(reader,object,landPoint.t);
        const approach=ballAt(reader,object,passage.t);
        const vx=approach.x-startPoint.x,vz=approach.z-startPoint.z;
        const length=Math.hypot(vx,vz);
        const far=length ? ((landPoint.x-objectAtLanding.x)*vx+(landPoint.z-objectAtLanding.z)*vz)/length : 0;
        if (far <= eps) {details.push({...detail,exception:'20(b): hit airborne, landed on near side of the ball current position.'});continue;}
        if (far < rc+radius(object,fallbackRadius)+eps) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Landing close to dividing plane; manual decision required.'});continue;}
      }
      offendingBalls.push(object.i);
      details.push({...detail,foul:true,reason:'Cue passed above an object ball without a recorded exception.'});
      }
    }
    return {foul:offendingBalls.length>0,offendingBalls:unique(offendingBalls),reason:offendingBalls.length?'Illegal jump over an object ball.':indeterminate?'Some airborne contact needs review.':'No illegal jump found.',indeterminate,details};
  }

  // Section 3.4: assess the scores after the final Black's pot or foul.
  function blackFrameOutcome({ballOn,balls,score,scores,respottedBlack=false}) {
    if(ballOn!==128 || score===0 || scores.length!==2)return null;
    const remaining=balls.filter(b=>b.n>0 && active(b));
    if(remaining.length!==1 || remaining[0].n!==7)return null;
    return !respottedBlack && scores[0]===scores[1]?'respot':'end';
  }

  /** Indices identify firstHits (simultaneous), potted, outOfBounds and nominee.
   * nominatedColour is a number 2..7. balls contains final positions and all
   * objects including inactive entries. Removed indices are also excluded when
   * callers supply pre-stroke active flags. Colours to respot are indices.
   * This pure function does not decide discretionary Foul and a Miss, restore
   * positions, choose colour spot geometry, or decide a tied-frame re-spot.
   */
  function adjudicate({ballOn,nominatedColour=null,freeBallNominee=null,balls,firstHits=[],potted=[],outOfBounds=[],jumpFoul=false,touchingAtStart=[],pushedTouching=[],cueStrikes=1}) {
    const byIndex=new Map(balls.map(b=>[b.i,b]));
    const hits=unique(firstHits).map(i=>byIndex.get(i)).filter(b=>b && b.n>0);
    const pots=unique(potted).map(i=>byIndex.get(i)).filter(Boolean);
    const outs=unique(outOfBounds).map(i=>byIndex.get(i)).filter(Boolean);
    const removed=new Set([...potted,...outOfBounds]);
    const onNumbers=ballOnNumbers(ballOn), colourChoice=ballOn===COLOUR_ALL;
    const nominee=freeBallNominee==null?null:byIndex.get(freeBallNominee);
    let on=onNumbers.length===1?onNumbers[0]:null;
    if(colourChoice) on=nominatedColour>=2 && nominatedColour<=7?nominatedColour:(hits.length===1 && hits[0].n>=2?hits[0].n:null);
    let foulCode=0,penalty=0;
    const reasons=[];
    const penalise=(code,value,reason)=>{foulCode|=code;penalty=Math.max(penalty,4,value||0);reasons.push(reason);};
    const baseValue=on || (colourChoice?7:4);
    const validNominee=nominee && nominee.n>0 && nominee.n!==on;
    const value=b=>validNominee && b.i===nominee.i?baseValue:b.n;
    const touching=unique(touchingAtStart).map(i=>byIndex.get(i)).filter(b=>b && b.n>0);
    const deemedHit=validNominee?touching.some(b=>b.i===nominee.i):on!=null && touching.some(b=>b.n===on);
    if(freeBallNominee!=null && !validNominee) penalise(FOUL.FIRST_HIT,baseValue,'Invalid free-ball nomination.');
    if(!deemedHit && hits.length===0) penalise(FOUL.MISS,baseValue,'No object ball contacted.');
    else if(!deemedHit) {
      const firstLegal=validNominee?hits.some(b=>b.i===nominee.i) && hits.every(b=>b.i===nominee.i || b.n===on):on!=null && hits.every(b=>b.n===on);
      if(!firstLegal) penalise(FOUL.FIRST_HIT,Math.max(baseValue,...hits.map(value)),'First contact was not on.');
    }
    for(const i of unique(pushedTouching)) {
      const b=touching.find(b=>b.i===i);
      if(b) penalise(FOUL.PUSH,Math.max(baseValue,value(b)),'Striking the cue caused an initially touching ball to move before playing away.');
    }
    if(cueStrikes>1)penalise(FOUL.DOUBLE_HIT,baseValue,'The cue tip struck the cue ball more than once in this stroke.');
    for(const b of pots) {
      if(b.n===0) penalise(FOUL.CUE_POTTED,baseValue,'Cue ball pocketed.');
      else if(b.n!==on && !(validNominee && b.i===nominee.i)) penalise(FOUL.POTTING,Math.max(baseValue,value(b)),'Ball not on pocketed.');
    }
    for(const b of outs) penalise(FOUL.OFF_TABLE,Math.max(baseValue,value(b)),'Ball forced off the table.');
    if(jumpFoul===true || jumpFoul && jumpFoul.foul) penalise(FOUL.JUMP,baseValue,'Illegal jump.');
    let points=on===1?pots.filter(b=>b.n===1 || validNominee && b.i===nominee.i).length:pots.some(b=>b.n===on || validNominee && b.i===nominee.i)?(on||0):0;
    const finalBalls=balls.map(b=>removed.has(b.i)?{...b,active:false}:b);
    let freeBallSafety=null;
    if(validNominee && !foulCode && points===0) {
      const remaining=finalBalls.filter(b=>b.n>0 && active(b));
      const twoColoursWithBlack=remaining.length===2 && remaining.every(b=>b.n>=2) && remaining.some(b=>b.n===7);
      if(!twoColoursWithBlack) {
        freeBallSafety=isSnookered(finalBalls,1<<on);
        if(freeBallSafety.snookered && freeBallSafety.effectiveSnookeringBalls.includes(nominee.i)) penalise(FOUL.FREE_BALL_SNOOKER,baseValue,'Nominated free ball left an effective snooker after a non-scoring stroke.');
      }
    }
    const score=foulCode?-penalty:points;
    const redsRemain=finalBalls.some(b=>b.n===1 && active(b));
    const canonicalPotted=pots.some(b=>b.n===on && !(validNominee && b.i===nominee.i));
    let nextBallOn=ballOn;
    if(score>0) {
      if(ballOn===RED) nextBallOn=COLOUR_ALL;
      else if(colourChoice) nextBallOn=redsRemain?RED:4;
      else if(canonicalPotted) nextBallOn=on===7?0:1<<(on+1);
    } else if(ballOn===RED || colourChoice) nextBallOn=redsRemain?RED:4;
    // The host retains responsibility for tied scores and re-spotted black.
    if(on===7 && !colourChoice && score<0 && !validNominee) nextBallOn=0;
    const respots=unique([...pots,...outs].filter(b=>b.n>=2 && (foulCode || ballOn===RED || colourChoice || validNominee && b.i===nominee.i)).map(b=>b.i)).sort((a,b)=>byIndex.get(b).n-byIndex.get(a).n);
    const cueBall=balls.find(b=>b.n===0);
    const requiresInHand=!!cueBall && (removed.has(cueBall.i) || !active(cueBall));
    return {score,foulCode,nextBallOn,respots,requiresInHand,ballOnUsed:on,penalty:foulCode?penalty:0,freeBallNominee:validNominee?nominee.i:null,reasons,freeBallSafety,canonicalPotted,continueBreak:score>0,cueStrikes,touching:{indices:touching.map(b=>b.i),deemedHit,pushedIndices:unique(pushedTouching)}};
  }
  return Object.freeze({RADIUS,RED,COLOUR_ALL,FOUL,CONTACT_EPS,TOUCH_EPS,ballOnNumbers,pinkRespotX,touchingStatus,remainingPoints,concessionStatus,earlyFrameOutcome,isSnookered,hasDirectHit,inferColour,evaluateJump,blackFrameOutcome,adjudicate});
})();

const PCOLCelebration = (() => {
  'use strict';
  const DURATION = 3200;
  const TIERS = {
    century: { duration: DURATION, eyebrow: 'CENTURY BREAK', title: '单杆破百', sparks: 10 },
    maximum: { duration: 4600, eyebrow: 'MAXIMUM BREAK', title: '完美满分', sparks: 24 },
    ultimate: { duration: 6000, eyebrow: 'ULTIMATE BREAK', title: '极限满分', sparks: 40 }
  };
  const STYLE = `
    :host { all: initial; position: fixed; z-index: 2147483646; inset: 19% 16px auto;
      display: flex; justify-content: center; pointer-events: none; color-scheme: dark; }
    *, *::before, *::after { box-sizing: border-box; }
    .card { position: relative; display: flex; align-items: center; gap: 28px;
      width: min(580px, 100%); min-height: 164px; padding: 24px 38px;
      color: #f9efd5; border: 1px solid #d8b87466; border-radius: 3px;
      background: radial-gradient(ellipse at 18% 75%, #355c4380, transparent 60%),
        linear-gradient(115deg, #102d25f5, #0b1e1af5 70%, #172e24f5);
      box-shadow: 0 18px 70px #0008, inset 0 0 36px #d7bd6b08;
      font: 14px/1.4 "Microsoft YaHei", "PingFang SC", sans-serif;
      animation: arrival ${DURATION}ms cubic-bezier(.22,.8,.3,1) both; }
    .card::before, .card::after { content: ''; position: absolute; height: 1px;
      left: 25px; right: 25px; background: linear-gradient(90deg, transparent, #edcc85, transparent); }
    .card::before { top: 7px; } .card::after { bottom: 7px; }
    .glow { position: absolute; inset: 0; overflow: hidden; border-radius: inherit; }
    .glow::before { content: ''; position: absolute; inset: -100% -50%;
      background: linear-gradient(110deg, transparent 43%, #fff3be18 49%, transparent 55%);
      animation: glint 1500ms 250ms ease-out both; }
    .score { position: relative; flex: 0 0 auto; min-width: 150px; text-align: center;
      border-right: 1px solid #c5a46555; padding-right: 28px; }
    .number { display: block; color: #f8dea0; font: 500 80px/.95 Georgia, "Times New Roman", serif;
      font-variant-numeric: tabular-nums; letter-spacing: -5px; text-shadow: 0 0 30px #f4ca6750; }
    .score-label { display: block; margin-top: 12px; color: #c4b791; font-size: 10px; letter-spacing: 4px; }
    .words { position: relative; min-width: 0; }
    .eyebrow { color: #dabe7d; font-size: 10px; letter-spacing: 3px; }
    .title { margin: 7px 0 8px; font-size: 29px; font-weight: 500; letter-spacing: 5px; }
    .player { color: #d1dcd2; font-size: 12px; letter-spacing: 1px; overflow-wrap: anywhere; }
    .diamond { display: inline-block; width: 5px; height: 5px; margin-right: 10px;
      background: #dabe7d; transform: rotate(45deg); vertical-align: 2px; }
    .spark { position: absolute; left: var(--x); top: var(--y); width: 2px; height: 2px;
      background: #ffe7ab; box-shadow: 0 0 7px #ebc76f; border-radius: 50%; opacity: 0;
      animation: spark 1900ms var(--delay) ease-out both; }
    @keyframes arrival { 0% { opacity: 0; transform: translateY(14px) scale(.97); }
      14%, 80% { opacity: 1; transform: translateY(0) scale(1); }
      100% { opacity: 0; transform: translateY(-8px) scale(1); } }
    @keyframes glint { from { transform: translateX(-45%); } to { transform: translateX(45%); } }
    @keyframes spark { 0% { opacity: 0; transform: translateY(12px); }
      20% { opacity: .7; } 100% { opacity: 0; transform: translateY(-20px); } }
    .stage { position: relative; display: flex; justify-content: center; isolation: isolate;
      width: min(660px, 100%); animation: arrival var(--duration) cubic-bezier(.22,.8,.3,1) both; }
    .stage.ultimate { width: min(720px, 100%); }
    .stage .card { z-index: 1; width: 100%; min-height: 190px; padding: 30px 42px;
      gap: 34px; border-color: #edcf8cb5; border-radius: 5px; animation: none;
      background: radial-gradient(ellipse at 16% 70%, #54724d80, transparent 58%),
        linear-gradient(115deg, #15352bf5, #0b211cf7 65%, #223c2cf5);
      box-shadow: 0 20px 80px #0009, 0 0 44px #d6b55a25, inset 0 0 45px #dfc47f12; }
    .stage .card::before, .stage .card::after { left: 19px; right: 19px; height: 2px;
      background: linear-gradient(90deg, transparent, #b9914b 20%, #fff1c7 50%, #b9914b 80%, transparent); }
    .stage .score { z-index: 2; min-width: 220px; padding-right: 34px; }
    .stage .number { position: relative; font-size: 100px; letter-spacing: -6px;
      color: #ffe5a0; background: linear-gradient(160deg, #fffae9 8%, #f2cb70 52%, #ffe8b0 77%, #aa7835);
      background-clip: text; -webkit-background-clip: text; -webkit-text-fill-color: transparent;
      text-shadow: none; filter: drop-shadow(0 0 16px #eac36a50); }
    .stage .score-label { position: relative; margin-top: 15px; color: #e5ce97; }
    .stage .words { z-index: 2; }
    .stage .eyebrow { color: #e7cd93; letter-spacing: 3px; }
    .stage .title { color: #fff1d0; font-size: 34px; letter-spacing: 6px; }
    .stage .glow::before { background: linear-gradient(110deg, transparent 38%, #fff3be30 49%, transparent 60%);
      animation: glint 2100ms 300ms ease-out both; }
    .crest { position: absolute; width: 204px; height: 224px;
      left: calc(50% - 17px); top: 50%; transform: translate(-50%, -50%);
      color: #e6c67f; opacity: .66; pointer-events: none; }
    .crest svg { width: 100%; height: 100%; overflow: visible; }
    .effects { position: absolute; inset: 0; z-index: 0; pointer-events: none; }
    .aura { position: absolute; inset: -140px -110px;
      background: radial-gradient(ellipse, #e6c76722, transparent 62%);
      animation: aura 2600ms 150ms ease-out both; }
    .rays { position: absolute; width: 600px; height: 600px; left: 50%; top: 50%;
      background: repeating-conic-gradient(from 6deg, transparent 0deg 16deg, #f3d9893d 18deg, transparent 20deg 30deg);
      mask-image: radial-gradient(circle, transparent 15%, #000 33%, transparent 68%);
      animation: radiance 4000ms ease-out both; }
    .stage .spark { width: 3px; height: 3px; background: #ffe7a5; box-shadow: 0 0 9px #efc768;
      animation: drift 2900ms var(--delay) ease-out both; }
    .stage .spark:nth-child(3n) { width: 4px; height: 7px; border-radius: 1px; }
    .burst { position: absolute; left: var(--x); top: var(--y); width: 1px; height: 1px; }
    .burst i { position: absolute; width: 2px; height: 7px; border-radius: 2px;
      background: #fff0bc; box-shadow: 0 0 9px #f3cb75; opacity: 0;
      animation: firework 1700ms var(--delay) cubic-bezier(.12,.62,.26,1) both; }
    .ultimate .card { min-height: 218px; padding: 36px 46px; border-color: #f3dfb3;
      background: radial-gradient(ellipse at 8% 70%, #446d6180, transparent 57%),
        radial-gradient(ellipse at 100% 10%, #ae91542b, transparent 60%),
        linear-gradient(115deg, #15372ff7, #0c2220fa 65%, #213c30f7);
      box-shadow: 0 24px 90px #0009, 0 0 70px #e5c76b38, inset 0 0 70px #bceee212; }
    .ultimate .score { min-width: 245px; }
    .ultimate .number { font-size: 114px; background-image: linear-gradient(155deg, #fffcef 12%, #ecd194 40%, #d7f5f0 60%, #ffe4a6 82%);
      filter: drop-shadow(0 0 20px #f0d89b70); }
    .ultimate .crest { width: 226px; height: 250px; color: #f2dca2; opacity: .8; }
    .ultimate .title { font-size: 38px; }
    .ultimate .eyebrow { color: #d8efdf; }
    .ultimate .diamond { background: #d6f4ea; box-shadow: 0 0 8px #b9eedc80; }
    .ultimate .aura { background: radial-gradient(ellipse at 32% 50%, #dfbc713d, transparent 57%),
      radial-gradient(ellipse at 76% 40%, #a0e5e02b, transparent 60%); animation-duration: 4200ms; }
    .ultimate .rays { width: 760px; height: 760px; opacity: .85; animation-duration: 5600ms; }
    .halo { position: absolute; left: 50%; top: 50%; width: 105%; height: 172%; border-radius: 50%;
      border: 1px solid #ebce8b65; box-shadow: 0 0 14px #d8b4681f, inset 0 0 14px #d8b4681f;
      transform: translate(-50%, -50%) rotate(-12deg); animation: orbit 4800ms ease-out both; }
    .halo.second { width: 98%; height: 205%; border-color: #bdece55c;
      transform: translate(-50%, -50%) rotate(13deg); animation-delay: 350ms; }
    .ultimate .spark:nth-child(even), .ultimate .burst:nth-child(even) i {
      background: #d3f8ef; box-shadow: 0 0 10px #a6e9de; }
    @keyframes aura { 0% { opacity: 0; transform: scale(.6); }
      28%, 78% { opacity: 1; } 100% { opacity: .4; transform: scale(1.15); } }
    @keyframes radiance { 0% { opacity: 0; transform: translate(-50%, -50%) rotate(-10deg) scale(.5); }
      20%, 75% { opacity: 1; } 100% { opacity: 0; transform: translate(-50%, -50%) rotate(8deg) scale(1.08); } }
    @keyframes drift { 0% { opacity: 0; transform: translate(0, 18px) rotate(0deg); }
      15% { opacity: .9; } 100% { opacity: 0; transform: translate(var(--drift), -65px) rotate(120deg); } }
    @keyframes firework { 0% { opacity: 0; transform: rotate(var(--angle)) translateY(8px) scale(.25); }
      12% { opacity: 1; } 100% { opacity: 0; transform: rotate(var(--angle)) translateY(var(--reach)) scale(.4); } }
    @keyframes orbit { 0% { opacity: 0; scale: .78; } 22%, 72% { opacity: 1; }
      100% { opacity: 0; scale: 1.09; } }
    @media (max-width: 480px) {
      :host { inset: 17% 12px auto; }
      .card { min-height: 138px; gap: 18px; padding: 24px 20px; }
      .score { min-width: 110px; padding-right: 18px; } .number { font-size: 62px; }
      .title { font-size: 23px; letter-spacing: 2px; }
      .eyebrow { font-size: 8px; letter-spacing: 2px; }
      .stage .card { min-height: 164px; padding: 24px 18px; gap: 18px; }
      .stage .score { min-width: 145px; padding-right: 18px; }
      .stage .number { font-size: 76px; letter-spacing: -4px; }
      .stage .title { font-size: 25px; letter-spacing: 3px; }
      .stage .eyebrow { font-size: 8px; letter-spacing: 2px; }
      .stage .crest { left: calc(50% - 9px); width: 150px; height: 178px; }
      .ultimate .card { min-height: 178px; }
      .ultimate .number { font-size: 84px; }
      .ultimate .crest { width: 162px; height: 190px; }
      .rays, .ultimate .rays { width: 480px; height: 480px; }
      .halo { width: 112%; height: 140%; }
      .halo.second { width: 106%; height: 165%; }
    }
    @media (prefers-reduced-motion: reduce) {
      .card, .stage { animation-name: quiet; } .stage .card { animation: none; }
      .spark, .glow, .effects { display: none; }
      @keyframes quiet { 0%, 100% { opacity: 0; } 10%, 85% { opacity: 1; } }
    }
  `;

  function create({ document, window, host = document.body }) {
    let overlay = null;
    let timer = null;
    let destroyed = false;

    function clear() {
      if (timer !== null) window.clearTimeout(timer);
      timer = null;
      if (overlay) overlay.remove();
      overlay = null;
    }

    function show({ playerLabel, breakScore }) {
      if (destroyed) return;
      clear();
      const tierName = breakScore === 155 ? 'ultimate' : breakScore === 147 ? 'maximum' : 'century';
      const tier = TIERS[tierName];
      overlay = document.createElement('div');
      overlay.dataset.pcolCelebration = tierName;
      const shadow = overlay.attachShadow({ mode: 'open' });
      const style = document.createElement('style');
      style.textContent = STYLE;
      const card = document.createElement('section');
      card.className = 'card';
      card.setAttribute('role', 'status');
      card.setAttribute('aria-live', 'polite');
      card.innerHTML = `<div class="glow" aria-hidden="true"></div>
        <div class="score"><span class="number"></span><span class="score-label">单杆得分</span></div>
        <div class="words"><div class="eyebrow"><span class="diamond" aria-hidden="true"></span>${tier.eyebrow}</div>
          <div class="title">${tier.title}</div><div class="player"></div></div>`;
      card.querySelector('.number').textContent = String(breakScore);
      card.querySelector('.player').textContent = playerLabel;
      for (let i = 0; i < tier.sparks; i++) {
        const spark = document.createElement('i');
        spark.className = 'spark';
        spark.setAttribute('aria-hidden', 'true');
        spark.style.cssText = tierName === 'century'
          ? `--x:${9 + i * 9}%;--y:${20 + (i * 23) % 67}%;--delay:${160 + (i * 137) % 900}ms`
          : `--x:${(i * 47) % 101}%;--y:${10 + (i * 31) % 92}%;--drift:${(i % 5 - 2) * 18}px;--delay:${250 + (i * 179) % (tier.duration - 3000)}ms`;
        card.append(spark);
      }
      shadow.append(style);
      if (tierName === 'century') shadow.append(card);
      else {
        const stage = document.createElement('div');
        stage.className = `stage ${tierName}`;
        stage.style.cssText = `--duration:${tier.duration}ms`;
        const effects = document.createElement('div');
        effects.className = 'effects';
        effects.setAttribute('aria-hidden', 'true');
        effects.innerHTML = `<div class="aura"></div><div class="rays"></div>${tierName === 'ultimate'
          ? '<div class="halo"></div><div class="halo second"></div>' : ''}`;
        const bursts = tierName === 'ultimate'
          ? [[8, -12, 350], [92, -18, 1000], [24, -25, 2100], [76, 104, 2800]]
          : [[12, -10, 600], [88, -10, 900]];
        for (const [x, y, delay] of bursts) {
          const burst = document.createElement('div');
          burst.className = 'burst';
          burst.style.cssText = `--x:${x}%;--y:${y}%;--delay:${delay}ms`;
          for (let i = 0; i < 12; i++) {
            const ray = document.createElement('i');
            ray.style.cssText = `--angle:${i * 30}deg;--reach:${tierName === 'ultimate' ? 105 : 75}px`;
            burst.append(ray);
          }
          effects.append(burst);
        }
        const crest = document.createElement('div');
        crest.className = 'crest';
        crest.setAttribute('aria-hidden', 'true');
        const leaves = [[49, 53, -38], [38, 77, -52], [35, 102, -66], [42, 127, -78],
          [56, 151, -92], [74, 171, -105]].map(([x, y, angle]) =>
          `<ellipse cx="${x}" cy="${y}" rx="5" ry="12" transform="rotate(${angle} ${x} ${y})"/>`).join('');
        crest.innerHTML = `<svg viewBox="0 0 200 220" aria-hidden="true"><g fill="none" stroke="currentColor" stroke-width="1.3">
          <path d="M95 193C45 170 18 105 51 38M105 193C155 170 182 105 149 38"/>
          <path d="M83 23L78 10L92 17L100 5L108 17L122 10L117 23ZM83 28H117"/>
          </g><g fill="currentColor">${leaves}<g transform="translate(200 0) scale(-1 1)">${leaves}</g></g>
          <path d="M90 199L100 191L110 199L100 207Z" fill="currentColor"/></svg>`;
        card.querySelector('.score').append(crest);
        stage.append(effects, card);
        shadow.append(stage);
      }
      host.append(overlay);
      timer = window.setTimeout(clear, tier.duration);
    }

    function destroy() {
      clear();
      destroyed = true;
    }

    return { show, clear, destroy };
  }

  return { create };
})();


const PCOLPractice = (() => {
  'use strict';
  const NAMES = ['白球', '红球', '黄球', '绿球', '棕球', '蓝球', '粉球', '黑球'];
  const COLOURS = ['#f7f6ec', '#db2538', '#f5ce42', '#329866', '#a16b42', '#418cdb', '#ef9cba', '#282d35'];
  const EPSILON = 1e-6;

  function placementError(layout, candidate, bounds) {
    const { x, z, r } = candidate;
    if (![x, z, r].every(Number.isFinite) || r <= 0) return '球的位置无效';
    if (!bounds.contains(x, z)) return '球不能摆在台面之外';
    if (layout.some(b => b.active && b.i !== candidate.i && Math.hypot(x - b.x, z - b.z) < r + b.r - EPSILON)) return '与另一颗球重叠，请稍微移开';
    return '';
  }

  function createEditor({ document, window, container, balls, onSelect, onClear, onStandard, onCancel }) {
    const POSITION_KEY = 'pcol-rules-patch:practice-palette-position';
    const root = document.createElement('aside');
    root.className = 'pe-palette-panel';
    root.setAttribute('aria-label', '自由摆球');
    root.innerHTML = `
      <style>
        .pe-palette-panel{position:fixed;right:14px;top:86px;width:104px;max-width:calc(100vw - 16px);max-height:calc(100dvh - 16px);overflow:auto;overscroll-behavior:contain;z-index:1000;pointer-events:auto;box-sizing:border-box;padding:10px;border:1px solid #64726070;border-radius:15px;background:linear-gradient(150deg,#172b25f5,#0b1916f5);box-shadow:0 12px 38px #0007;color:#e7eee9;font:12px/1.4 "Segoe UI","Microsoft YaHei",sans-serif;scrollbar-width:thin;scrollbar-color:#526a59 transparent}
        .pe-palette-panel[hidden]{display:none}.pe-palette-panel *{box-sizing:border-box}.pe-palette-panel button{font:inherit;cursor:pointer}.pe-palette-panel button:disabled{opacity:.38;cursor:default}.pe-palette-panel button:focus-visible{outline:2px solid #d7b778;outline-offset:2px}
        .pe-heading{margin:0 0 8px;padding:5px 2px 7px;text-align:center;font-size:16px;font-weight:600;letter-spacing:.02em;cursor:grab;touch-action:none;user-select:none}.pe-heading:active{cursor:grabbing}.pe-ball-list{display:grid;gap:3px}.pe-ball-button{display:flex;justify-content:center;align-items:center;width:100%;height:36px;padding:3px;border:1px solid transparent;border-radius:9px;background:transparent;transition:background .12s,border-color .12s}.pe-ball-button:hover{background:#ffffff0b}.pe-ball-button[aria-pressed="true"]{background:#d0b17718;border-color:#d0b177}.pe-orb{display:block;width:27px;height:27px;flex-shrink:0;border-radius:50%;background:radial-gradient(circle at 30% 22%,#ffffffa8,transparent 36%),var(--ball);box-shadow:inset -4px -5px 7px #0007,inset 1px 1px 2px #ffffff55,0 3px 5px #0008}
        .pe-controls{display:grid;grid-template-columns:1fr;gap:5px;margin-top:9px;padding-top:9px;border-top:1px solid #ffffff12}.pe-control{padding:7px 1px;color:#c3d2c8;border:1px solid #ffffff20;border-radius:7px;background:#ffffff05;font-size:10px!important;white-space:nowrap}.pe-control:hover:not(:disabled){background:#ffffff0c;border-color:#d0b17770}.pe-cancel{padding:6px 1px;border-color:transparent;background:transparent;color:#829c8c}
        @media(max-height:590px){.pe-heading{margin-bottom:5px;padding-top:3px}.pe-ball-button{height:32px}.pe-orb{width:25px;height:25px}.pe-controls{margin-top:7px;padding-top:7px}}
        @media(prefers-reduced-motion:reduce){.pe-ball-button{transition:none}}
      </style>
      <h2 class="pe-heading">自由摆球</h2>
      <div class="pe-ball-list"></div>
      <div class="pe-controls">
        <button type="button" class="pe-control pe-clear">清空目标球</button>
        <button type="button" class="pe-control pe-standard">标准球形</button>
        <button type="button" class="pe-control pe-cancel">取消本次编辑</button>
      </div>`;
    const $ = selector => root.querySelector(selector);
    const heading = $('.pe-heading');
    const buttons = [];
    for (let n = 0; n <= 7; n++) {
      const button = document.createElement('button');
      button.type = 'button';
      button.className = 'pe-ball-button';
      button.setAttribute('aria-label', `选择${NAMES[n]}`);
      button.title = NAMES[n];
      button.innerHTML = `<span class="pe-orb" style="--ball:${COLOURS[n]}" aria-hidden="true"></span>`;
      button.addEventListener('click', () => onSelect(n));
      $('.pe-ball-list').append(button);
      buttons.push(button);
    }
    $('.pe-clear').addEventListener('click', onClear);
    $('.pe-standard').addEventListener('click', onStandard);
    $('.pe-cancel').addEventListener('click', onCancel);
    for (const type of ['pointerdown', 'pointerup', 'pointermove', 'mousedown', 'mouseup', 'mousemove', 'click', 'dblclick', 'wheel', 'contextmenu']) {
      root.addEventListener(type, event => event.stopPropagation());
    }
    for (const type of ['keydown', 'keyup', 'keypress']) {
      root.addEventListener(type, event => {
        if (!['w', 'ArrowUp', 'Escape'].includes(event.key.length === 1 ? event.key.toLowerCase() : event.key)) event.stopPropagation();
      });
    }
    let position = null, drag = null;
    try {
      const saved = JSON.parse(window.localStorage.getItem(POSITION_KEY));
      if (Number.isFinite(saved?.x) && Number.isFinite(saved?.y)) position = saved;
    } catch (_) {}
    function savePosition() {
      try {
        if (position) window.localStorage.setItem(POSITION_KEY, JSON.stringify(position));
        else window.localStorage.removeItem(POSITION_KEY);
      } catch (_) {}
    }
    function place(x, y) {
      const rect = root.getBoundingClientRect();
      if (root.hidden || !rect.width || !rect.height) return;
      position = {
        x: Math.max(8, Math.min(x, window.innerWidth - rect.width - 8)),
        y: Math.max(8, Math.min(y, window.innerHeight - rect.height - 8))
      };
      root.style.left = `${position.x}px`;
      root.style.top = `${position.y}px`;
      root.style.right = 'auto';
    }
    function clamp() {
      const rect = root.getBoundingClientRect();
      place(position ? position.x : rect.left, position ? position.y : rect.top);
    }
    function finishDrag() {
      if (!drag) return;
      const pointerId = drag.pointerId;
      drag = null;
      if (heading.hasPointerCapture(pointerId)) heading.releasePointerCapture(pointerId);
      savePosition();
    }
    heading.addEventListener('pointerdown', event => {
      if (event.button !== 0) return;
      event.preventDefault();
      const rect = root.getBoundingClientRect();
      drag = { pointerId: event.pointerId, x: event.clientX - rect.left, y: event.clientY - rect.top };
      heading.setPointerCapture(event.pointerId);
    });
    heading.addEventListener('pointermove', event => {
      if (drag?.pointerId === event.pointerId) place(event.clientX - drag.x, event.clientY - drag.y);
    });
    for (const type of ['pointerup', 'pointercancel', 'lostpointercapture']) heading.addEventListener(type, finishDrag);
    heading.addEventListener('dblclick', () => {
      position = null;
      root.style.left = '';
      root.style.top = '';
      root.style.right = '';
      savePosition();
      clamp();
    });
    window.addEventListener('resize', clamp);
    function update(current, selectedIndex, editing = false) {
      const selected = current.find(b => b.i === selectedIndex);
      buttons.forEach((button, n) => button.setAttribute('aria-pressed', String(selected?.n === n)));
      buttons[1].title = `红球 · 已放 ${current.filter(b => b.n === 1 && b.active).length} / 15`;
      $('.pe-clear').disabled = !current.some(b => b.n !== 0 && b.active);
      $('.pe-cancel').disabled = !editing;
    }
    function setVisible(visible) {
      if (!visible) finishDrag();
      root.hidden = !visible;
      if (visible) clamp();
    }
    container.append(root);
    update(balls, null);
    clamp();
    return {
      update,
      setVisible,
      destroy() {
        finishDrag();
        window.removeEventListener('resize', clamp);
        root.remove();
      }
    };
  }
  return { placementError, createEditor };
})();

/* Compile a native stroke without touching the live controller or physics world. */
const PCOLTrialShot = (() => {
  const finite = (value, name) => {
    if (typeof value !== 'number' || !Number.isFinite(value)) throw new TypeError(`${name} must be finite`);
    return value;
  };
  const clamp = (n, lo, hi) => Math.max(lo, Math.min(hi, n));
  // Public main-thread compilation owns one detached cushion graph. The
  // decision worker reconstructs the native cushion once from exported bounds.
  function clone(value, seen = new Map()) {
    if (value === null || typeof value !== 'object') return value;
    if (seen.has(value)) return seen.get(value);
    if (ArrayBuffer.isView(value)) {
      const buffer = clone(value.buffer, seen);
      const copy = value instanceof DataView
        ? new DataView(buffer, value.byteOffset, value.byteLength)
        : new value.constructor(buffer, value.byteOffset, value.length);
      seen.set(value, copy);
      return copy;
    }
    if (value instanceof ArrayBuffer) {
      const copy = value.slice(0);
      seen.set(value, copy);
      return copy;
    }
    const copy = Array.isArray(value) ? [] : Object.create(Object.getPrototypeOf(value));
    seen.set(value, copy);
    for (const key of Reflect.ownKeys(value)) {
      if (Array.isArray(value) && key === 'length') continue;
      const descriptor = Object.getOwnPropertyDescriptor(value, key);
      if (!('value' in descriptor)) throw new Error('Unsupported accessor in native geometry');
      descriptor.value = clone(descriptor.value, seen);
      Object.defineProperty(copy, key, descriptor);
    }
    return copy;
  }
  function resetCushion(cushion) {
    if(Array.isArray(cushion.actives))cushion.actives.length=0;
    cushion.crtCushion=null;
    for(let segment=cushion.head;segment;segment=segment.next) {
      segment.toi=0;
      const point=segment.tp;
      if(point) {
        point.x=point.y=point.z=0;
        // Native near-plane detection calls copyFrom on a physics Vec3.
        if(typeof point.copyFrom!=='function' && typeof point.copy==='function')point.copyFrom=point.copy;
      }
    }
  }
  const contexts=new WeakMap();
  function compile(game, shot, overrideBalls) {
    const live=game?._fpc?._stickCtl,props=live?._state1?._cachedProps;
    const sourceBalls=game?._simulator?.getBalls?.();
    if(!props || !sourceBalls?.length || typeof live.getStrokeSpdWithPower!=='function')throw new Error('Native PCOL shot controller is unavailable');
    const source=live._state1._cushionBody;
    if(!source)throw new Error('Native cushion geometry is unavailable');
    let context=contexts.get(live);
    if(!context || context.source!==source) {
      context={source,cushion:clone(source)};contexts.set(live,context);
    }
    const balls=overrideBalls==null
      ? sourceBalls.map(b=>({number:b.number,radius:b.radius,active:b.active,position:clone(b.position)}))
      : overrideBalls.map(b=>{
        const original=sourceBalls.find(source=>source.index===b.i);
        if(!original || original.number!==b.n || !(b.r>0))throw new Error('Invalid detached ball configuration');
        const position=clone(original.position);
        for(const key of ['x','y','z'])position[key]=finite(b[key],`ball.${key}`);
        return {number:b.n,radius:b.r,active:b.active,position};
      });
    return compilePrepared({Stick:live.constructor,props,cushion:context.cushion},shot,balls);
  }

  function compilePrepared({Stick,props,cushion}, { direction, power, side = 0, vertical = 0, elevation = 0 } = {}, balls) {
    const x = finite(direction?.x, 'direction.x'), z = finite(direction?.z, 'direction.z');
    const length = Math.hypot(x, z);
    if (!Number.isFinite(length) || length === 0) throw new RangeError('direction must have nonzero finite length');
    const requested = { direction: { x, z }, power: finite(power, 'power'),
      side: finite(side, 'side'), vertical: finite(vertical, 'vertical'), elevation: finite(elevation, 'elevation') };
    for (const key of ['ballRadius', 'tipRadius', 'midRadius', 'stickLen']) finite(props[key], `stick.${key}`);
    if (!props.stickName || props.tipRadius <= 0 || props.stickLen <= 0) throw new Error('Native stick is not bound');
    const cue = balls.find(b => b.number === 0 && b.active);
    if (!cue) throw new Error('Active cue ball is unavailable');
    // These are all native Cushion filter/detect caches. A fresh Stick keeps
    // every aim, dirty flag and potential-touch cache private to this shot.
    resetCushion(cushion);
    const stick = new Stick(), state = stick._state1;
    if (!state || typeof state.bind !== 'function') throw new Error('Unsupported native stick constructor');
    state.onKissPropsChanged = () => {};
    state.bind({ stickName: props.stickName, specs: { tipRadius: props.tipRadius,
      buttRadius: 2 * props.midRadius - props.tipRadius, len: props.stickLen } }, balls, cushion);
    const dx = x / length, dz = z / length;
    state.resetAimPoint(cue.position);
    state.setCtlPoint(cue.position.x - dx, cue.position.z - dz);
    // The native initial slope sentinel (999) can skip exact matching slopes.
    // Initialize only this detached state, also handling opposite azimuths.
    const cx = state._worCtlPoint.x - cue.position.x, cz = state._worCtlPoint.z - cue.position.z;
    state._angleH = Math.atan2(-cz, cx) + Math.PI;
    state._cachedSlopeH = Number.isFinite(cz / cx) ? Infinity : 0;
    const radial = Math.max(1, Math.hypot(side, vertical));
    state.setLocTip(side / radial * state.maxTipOffset, vertical / radial * state.maxTipOffset, false);
    const normalizedPower = clamp(power, 0, 1);
    state.setAngleV(clamp(elevation, 0, Math.PI / 4));
    const point = state.getKissPoint(), dir = state.getKissDir();
    const stroke = Array.from(new Float32Array([point.x, point.y, point.z, dir.x, dir.y, dir.z,
      stick.getStrokeSpdWithPower(normalizedPower), props.tipRadius]));
    if (!stroke.every(Number.isFinite)) throw new Error('Native stroke geometry is non-finite');
    return { stroke, requested, actual: {
      direction: { x: stroke[3], y: stroke[4], z: stroke[5] },
      contactPoint: { x: stroke[0], y: stroke[1], z: stroke[2] },
      elevation: Math.asin(clamp(-stroke[4] / Math.hypot(...stroke.slice(3, 6)), -1, 1)),
      power: normalizedPower, side: state._locTipPoint.z / state.maxTipOffset,
      vertical: state._locTipPoint.y / state.maxTipOffset, speed: stroke[6], tipRadius: stroke[7],
      maxTipOffset: state.maxTipOffset
    } };
  }
  function exportCompiler(game, source) {
    const live=game?._fpc?._stickCtl,state=live?._state1,cushion=state?._cushionBody;
    if(!state || !live._state0 || !cushion || typeof source!=='string')throw new Error('Native compiler source is unavailable');
    // PCOL 1.0.0 inlines these classes in module 10. Preserve their complete
    // original closure, without executing its renderer, DOM or game startup.
    const section=(start,end)=>{
      const from=source.indexOf(start),to=from<0?-1:source.indexOf(end,from+start.length);
      if(from<0 || to<0)throw new Error('Unsupported native compiler closure: '+start);
      return source.slice(from,to);
    };
    if(live.constructor.name!=='Ei' || state.constructor.name!=='Ci' || live._state0.constructor.name!=='hi' || cushion.constructor.name!=='E')throw new Error('Unsupported native compiler classes');
    const native=section('const E=function(t,e){',';var w=E;')+';'+
      section('const G=1e-6,q=','class W extends')+
      section('class hi{','const wi=-.9');
    if(!native.includes(live.constructor.toString()) || !native.includes(state.constructor.toString()))throw new Error('Native compiler source does not match the live controller');
    const Vector=state._worTargetPoint.constructor,methods={},statics={};
    for(const key of ['equals','copyFrom','copyFromFloats','subtractToRef','normalize','length','lengthSquared']) {
      if(typeof Vector.prototype[key]!=='function')throw new Error('Missing native Vector3.'+key);
      methods[key]=Vector.prototype[key].toString();
    }
    for(const key of ['Dot','DistanceSquared']) {
      if(typeof Vector[key]!=='function')throw new Error('Missing native Vector3.'+key);
      statics[key]=Vector[key].toString();
    }
    const props={};
    for(const key of ['stickName','ballRadius','tipRadius','midRadius','stickLen'])props[key]=state._cachedProps[key];
    const bounds=[];
    for(let segment=cushion.head;segment;segment=segment.next)bounds.push(segment.a.x,segment.a.z);
    if(bounds.length<6 || !bounds.every(Number.isFinite) || !Number.isFinite(cushion.boundsY))throw new Error('Invalid native cushion bounds');
    return {native,vector:{constructor:Vector.toString(),methods,statics},props,cushion:{id:cushion.id,y:cushion.boundsY,bounds}};
  }

  function createCompiler(payload,req) {
    if(!payload?.vector || typeof payload.native!=='string' || typeof req!=='function')throw new Error('Invalid native compiler payload');
    const restore=source=>new Function('return ('+source+')')();
    const Vector=restore(payload.vector.constructor);
    for(const [key,source] of Object.entries(payload.vector.methods))Vector.prototype[key]=restore(source);
    for(const [key,source] of Object.entries(payload.vector.statics))Vector[key]=restore(source);
    const native=new Function('req','Vector','const A={a:req(13)},I={a:req(18)},s={Vector3:Vector};'+payload.native+';return {Stick:Ei,Cushion:E};')(req,Vector);
    const data=payload.cushion,cushion=new native.Cushion(data.id,{y:data.y,bounds:data.bounds});
    const context={Stick:native.Stick,props:{...payload.props},cushion};
    return {compile(shot,sourceBalls) {
      if(!Array.isArray(sourceBalls) || !sourceBalls.length)throw new Error('Detached compiler balls are required');
      const balls=sourceBalls.map(b=>{
        if(!Number.isInteger(b.i) || !Number.isInteger(b.n) || !(b.r>0))throw new Error('Invalid detached ball configuration');
        const position=new Vector(finite(b.x,'ball.x'),finite(b.y,'ball.y'),finite(b.z,'ball.z'));
        return {number:b.n,radius:b.r,active:b.active,position};
      });
      return compilePrepared(context,shot,balls);
    }};
  }
  return { compile,exportCompiler,createCompiler };
})();

const PCOLTrialWorkerSource = "/* Per-stroke Float64 trajectory. Native ball identity/radius are immutable;\n * every physics/contact sample retains position and active state unchanged.\n * Object rows are materialized only for explicit external trace exports. */\nconst PCOLShotTrace = (() => {\n  function create(nativeBalls, {cap = 15000, seconds = false, chunkSize = 128} = {}) {\n    const metadata = nativeBalls.map(b => ({i:b.index,n:b.number,r:b.radius}));\n    const slots = new Map();\n    for(let i=0;i<metadata.length;i++)if(!slots.has(metadata[i].i))slots.set(metadata[i].i,i);\n    const stride = 1 + 4*metadata.length, chunks = [];\n    const last = {t:0,x:0,y:0,z:0};\n    let length = 0;\n    function sample(balls, time) {\n      if(length >= cap)return null;\n      const chunkIndex = Math.floor(length/chunkSize), offset = (length%chunkSize)*stride;\n      let data = chunks[chunkIndex];\n      if(!data)data=chunks[chunkIndex]=new Float64Array(Math.min(chunkSize,cap-chunkIndex*chunkSize)*stride);\n      data[offset]=time;\n      for(let i=0;i<metadata.length;i++) {\n        const b=balls[i],p=b.position,k=offset+1+i*4;\n        data[k]=p.x;data[k+1]=p.y;data[k+2]=p.z;data[k+3]=b.active===false?0:1;\n      }\n      last.t=length++;last.x=data[offset+1];last.y=data[offset+2];last.z=data[offset+3];\n      return last;\n    }\n    function readCue(index, out = {}) {\n      const data=chunks[Math.floor(index/chunkSize)],offset=(index%chunkSize)*stride;\n      out.t=index;out.x=data[offset+1];out.y=data[offset+2];out.z=data[offset+3];\n      if(seconds)out.seconds=data[offset];\n      return out;\n    }\n    function readBall(index, fallback, out = {}) {\n      const slot=slots.get(fallback.i);\n      if(slot===undefined){Object.assign(out,fallback);out.active=false;return out;}\n      const data=chunks[Math.floor(index/chunkSize)],offset=(index%chunkSize)*stride+1+slot*4;\n      const m=metadata[slot];\n      out.i=m.i;out.n=m.n;out.r=m.r;\n      out.x=data[offset];out.y=data[offset+1];out.z=data[offset+2];out.active=data[offset+3]!==0;\n      return out;\n    }\n    function toArray() {\n      const rows=new Array(length);\n      for(let i=0;i<length;i++) {\n        const row=readCue(i);\n        row.balls=metadata.map(b=>readBall(i,b));rows[i]=row;\n      }\n      return rows;\n    }\n    function toCueArray() {\n      const rows=new Array(length),point={};\n      for(let i=0;i<length;i++) {\n        readCue(i,point);rows[i]={t:point.t,x:point.x,z:point.z};\n      }\n      return rows;\n    }\n    return {get length(){return length;},sample,readCue,readBall,toArray,toCueArray,toJSON:toArray};\n  }\n  return {create};\n})();\n\n/* PCOL rule helpers. x/z are cloth coordinates; y is height. No game mutation.\n * WPBSA 2024-25: definitions 17/20, play 3/4/7/8/11/12.\n * https://wpbsa.com/wp-content/uploads/2198_WPBSA-Rulebook-2024-25.pdf\n */\nconst PCOLCore = (() => {\n  'use strict';\n  const RADIUS = 0.02625;\n  const RED = 2, COLOUR_ALL = 252;\n  const FOUL = Object.freeze({MISS:1, FIRST_HIT:2, POTTING:4, CUE_POTTED:8, OFF_TABLE:16, JUMP:32, FREE_BALL_SNOOKER:64, PUSH:128, DOUBLE_HIT:256});\n  // Referee tolerance: the observed 0.188 mm resting gap counts as touching.\n  // Keep physical spotting clearance independent of this judgement tolerance.\n  const CONTACT_EPS = 1e-5, TOUCH_EPS = 2e-4;\n  const unique = a => [...new Set(a)];\n  const radius = (b, fallback = RADIUS) => b.r > 0 ? b.r : fallback;\n  const hypot2 = (a, b) => Math.hypot(a.x - b.x, a.z - b.z);\n  const active = b => b.active !== false;\n  const ballOnNumbers = mask => [1,2,3,4,5,6,7].filter(n => (mask & (1 << n)) !== 0);\n\n  // PCOL's x axis runs from Baulk to the black end. Leave a small gap beyond\n  // the touching tolerance, and only consider Baulk after the top side is full.\n  function pinkRespotX(balls, pink, minX, maxX) {\n    const intervals=[];\n    for(const b of balls){\n      if(!active(b)||b.i===pink.i)continue;\n      const rr=radius(pink)+radius(b)+2*CONTACT_EPS;\n      const across=(b.y-pink.y)**2+(b.z-pink.z)**2;\n      if(across>=rr*rr)continue;\n      const half=Math.sqrt(rr*rr-across);\n      intervals.push([b.x-half,b.x+half]);\n    }\n    intervals.sort((a,b)=>a[0]-b[0]);\n    const blocked=[];\n    for(const range of intervals){\n      const last=blocked[blocked.length-1];\n      if(last&&range[0]<last[1])last[1]=Math.max(last[1],range[1]);\n      else blocked.push(range);\n    }\n    let x=pink.x;\n    for(const [left,right] of blocked){\n      if(x<=left)break;\n      if(x<right)x=right;\n    }\n    if(x<=maxX)return x;\n    x=pink.x;\n    for(let i=blocked.length-1;i>=0;i--){\n      const [left,right]=blocked[i];\n      if(x>=right)break;\n      if(x>left)x=left;\n    }\n    return x>=minX?x:null;\n  }\n\n  function touchingStatus({balls,ballOn,nominatedColour=null,freeBallNominee=null}) {\n    const cue=balls.find(b=>b.n===0 && active(b));\n    const touched=cue?balls.filter(b=>b.n>0 && active(b) && Math.hypot(cue.x-b.x,cue.y-b.y,cue.z-b.z)<=radius(cue)+radius(b)+TOUCH_EPS):[];\n    const on=ballOn===COLOUR_ALL?(nominatedColour?[nominatedColour]:[]):ballOnNumbers(ballOn);\n    const eligible=freeBallNominee!=null?touched.filter(b=>b.i===freeBallNominee):touched.filter(b=>on.includes(b.n));\n    return {indices:touched.map(b=>b.i),eligibleIndices:eligible.map(b=>b.i),deemedHit:eligible.length>0,requiresColourDeclaration:ballOn===COLOUR_ALL && touched.some(b=>b.n>=2),tolerance:TOUCH_EPS};\n  }\n\n  function remainingPoints(balls, ballOn, {freeBall = false} = {}) {\n    if (!ballOn || ballOn === 65535) return 0;\n    const live = balls.filter(b => active(b) && b.n > 0);\n    const reds = live.filter(b => b.n === 1).length;\n    let maximum = reds || ballOn === COLOUR_ALL ? reds * 8 + 27 + (ballOn === COLOUR_ALL ? 7 : 0) : live.filter(b => b.n >= 2).reduce((sum,b) => sum+b.n,0);\n    if (freeBall) maximum += ballOn === RED ? 8 : ballOn === COLOUR_ALL ? 7 : ballOnNumbers(ballOn)[0] || 0;\n    return maximum;\n  }\n\n  // User-requested optional concession threshold, not a mandatory match rule.\n  function concessionStatus({balls, ballOn, scores, playerIndex, freeBall = false, threshold = 1}) {\n    const maximum = remainingPoints(balls,ballOn,{freeBall});\n    const valid = scores.length === 2 && (playerIndex === 0 || playerIndex === 1) && ballOn > 0 && ballOn !== 65535;\n    const deficit = valid ? scores[1-playerIndex]-scores[playerIndex] : 0;\n    const excess = deficit-maximum;\n    return {eligible:valid && excess >= threshold,playerIndex,remaining:maximum,deficit,excess,threshold};\n  }\n\n  /** User-customised early finish, separate from the official final-black rule.\n   * Supply settled post-stroke balls/scores, including foul penalties and respots.\n   * A known free-ball opportunity adds its possible points; unresolved review\n   * cannot establish an early finish. Omit actor/continueBreak for a stable turn.\n   * At 17 over only the leader's legal scoring break may continue. The separate\n   * blackLeadThreshold is a score lead (default 8), not points over the table.\n   * On the last Black, playerIndex is the incoming player: the leader keeps\n   * their shot, including after potting Pink; the trailing player's turn ends it.\n   */\n  function earlyFrameOutcome({balls,ballOn,scores,playerIndex=null,actor=null,continueBreak=false,freeBall=false,freeBallReview=false,threshold=17,blackLeadThreshold=8}) {\n    if(!Array.isArray(balls)||!Array.isArray(scores)||scores.length!==2||!scores.every(Number.isFinite)||\n      !ballOn||ballOn===65535||freeBallReview||freeBall==null||scores[0]===scores[1])return null;\n    const winner=scores[0]>scores[1]?0:1,loser=1-winner;\n    const deficit=scores[winner]-scores[loser],remaining=remainingPoints(balls,ballOn,{freeBall}),excess=deficit-remaining;\n    const live=balls.filter(b=>b.n>0&&active(b));\n    if(ballOn===128&&live.length===1&&live[0].n===7&&Number.isFinite(blackLeadThreshold)&&deficit>=blackLeadThreshold)\n      return playerIndex===loser?{winner,loser,deficit,remaining,excess,threshold:blackLeadThreshold,reason:'black-lead'}:null;\n    if(Number.isFinite(threshold)&&excess>=threshold&&!(actor===winner&&continueBreak===true))\n      return {winner,loser,deficit,remaining,excess,threshold,reason:'excess-threshold'};\n    return null;\n  }\n\n  // Earliest intersection of a cue-centre ray with a ball's expanded disc.\n  function rayBlocker(cue, direction, length, b, cueRadius, eps) {\n    const dx = b.x - cue.x, dz = b.z - cue.z;\n    const projection = dx * direction.x + dz * direction.z;\n    const rr = cueRadius + radius(b);\n    const perpendicular2 = dx * dx + dz * dz - projection * projection;\n    if (perpendicular2 >= rr * rr - eps || projection + rr < 0) return false;\n    const enter = projection - Math.sqrt(Math.max(0, rr * rr - perpendicular2));\n    return enter < length - eps && projection + Math.sqrt(Math.max(0, rr * rr - perpendicular2)) > eps;\n  }\n\n  /** Both extreme physical contacts must be available on at least one ball on.\n   * Cushions and other balls on cannot cause a snooker under definition 17.\n   * options.inHand requires an all-positions proof which this helper does not\n   * attempt: it returns null, never true based on a finite sample of the D.\n   * Effective blockers are returned for the free-ball safety restriction.\n   */\n  function isSnookered(balls, ballOn, cuePosition, options = {}) {\n    if (options.inHand) return {snookered:null, indeterminate:true, clearTargets:[], details:[], effectiveSnookeringBalls:[], reason:'All legal cue positions in the D must be considered.'};\n    const cue = cuePosition || balls.find(b => b.n === 0 && active(b));\n    const on = ballOnNumbers(ballOn);\n    const targets = balls.filter(b => active(b) && on.includes(b.n));\n    if (!cue || targets.length === 0) return {snookered:null, indeterminate:true, clearTargets:[], details:[], effectiveSnookeringBalls:[], reason:'Cue position or ball on unavailable.'};\n    const rc = radius(cue, options.radius || RADIUS), eps = options.epsilon || 1e-8;\n    const blockers = balls.filter(b => active(b) && b.n > 0 && !on.includes(b.n));\n    const details = targets.map(target => {\n      const distance = hypot2(cue, target), rr = rc + radius(target);\n      if (distance <= rr + eps) return {target:target.i, indeterminate:true, leftBlockedBy:[], rightBlockedBy:[], effective:[]};\n      const angle = Math.atan2(target.z - cue.z, target.x - cue.x);\n      const halfAngle = Math.asin(Math.min(1, rr / distance));\n      const travel = Math.sqrt(distance * distance - rr * rr);\n      const edge = sign => {\n        const theta = angle + sign * halfAngle;\n        const direction = {x:Math.cos(theta), z:Math.sin(theta)};\n        return blockers.filter(b => rayBlocker(cue, direction, travel, b, rc, eps)).map(b => b.i);\n      };\n      const leftBlockedBy = edge(1), rightBlockedBy = edge(-1);\n      const both = unique([...leftBlockedBy, ...rightBlockedBy]);\n      const nearest = Math.min(...both.map(i => hypot2(cue, balls.find(b => b.i === i))));\n      const effective = both.filter(i => Math.abs(hypot2(cue, balls.find(b => b.i === i)) - nearest) <= eps);\n      return {target:target.i, leftBlockedBy, rightBlockedBy, effective, clear:both.length === 0};\n    });\n    const clearTargets = details.filter(d => d.clear).map(d => d.target);\n    const indeterminate = !clearTargets.length && details.some(d => d.indeterminate);\n    const snookered = clearTargets.length ? false : indeterminate ? null : true;\n    let effectiveSnookeringBalls = snookered ? details[0].effective.slice() : [];\n    for (const d of details) effectiveSnookeringBalls = effectiveSnookeringBalls.filter(i => d.effective.includes(i));\n    return {snookered, indeterminate, clearTargets, details, effectiveSnookeringBalls};\n  }\n\n  /** Proves visibility of any part of a legal ball, not both extreme edges.\n   * Ray collision order can only change at disc tangent angles or the angles\n   * of expanded-disc intersections. Test each angular cell plus its boundaries.\n   * This handles arbitrarily narrow positive gaps without a fixed angle grid.\n   */\n  function hasDirectHit(balls, ballOn, cuePosition, options = {}) {\n    const unknown=reason=>({hasDirectHit:null,indeterminate:true,target:null,direction:null,reason});\n    if(options.inHand) return unknown('All legal cue positions in the D must be considered.');\n    const cue=cuePosition || balls.find(b=>b.n===0 && active(b));\n    if(!cue) return unknown('Cue position unavailable.');\n    const on=ballOnNumbers(ballOn), rc=radius(cue,options.radius || RADIUS),eps=options.epsilon || 1e-9;\n    const objects=balls.filter(b=>b.n>0 && active(b));\n    if(!objects.some(b=>on.includes(b.n))) return unknown('Ball on unavailable.');\n    const circles=objects.map(b=>({b,x:b.x-cue.x,z:b.z-cue.z,r:rc+radius(b)}));\n    const tau=2*Math.PI,normal=a=>(a%tau+tau)%tau;\n    const angles=[];\n    let touching=false;\n    for(const c of circles) {\n      const d=Math.hypot(c.x,c.z);\n      if(d<=c.r+eps){touching=true;continue;}\n      const angle=Math.atan2(c.z,c.x),h=Math.asin(c.r/d);\n      angles.push(normal(angle-h),normal(angle+h),normal(angle));\n    }\n    for(let i=0;i<circles.length;i++) for(let j=i+1;j<circles.length;j++) {\n      const a=circles[i],b=circles[j],dx=b.x-a.x,dz=b.z-a.z,d=Math.hypot(dx,dz);\n      if(d<=eps || d>a.r+b.r+eps || d<Math.abs(a.r-b.r)-eps)continue;\n      const along=(a.r*a.r-b.r*b.r+d*d)/(2*d),height=Math.sqrt(Math.max(0,a.r*a.r-along*along));\n      const x=a.x+along*dx/d,z=a.z+along*dz/d;\n      angles.push(normal(Math.atan2(z+height*dx/d,x-height*dz/d)),normal(Math.atan2(z-height*dx/d,x+height*dz/d)));\n    }\n    angles.sort((a,b)=>a-b);\n    const candidates=angles.slice();\n    for(let i=0;i<angles.length;i++)candidates.push(normal((angles[i]+(i+1<angles.length?angles[i+1]:angles[0]+tau))/2));\n    for(const angle of candidates) {\n      const direction={x:Math.cos(angle),z:Math.sin(angle)};\n      const entries=[];\n      for(const c of circles) {\n        const projection=c.x*direction.x+c.z*direction.z;\n        const discriminant=c.r*c.r-(c.x*c.x+c.z*c.z-projection*projection);\n        if(discriminant < -eps) continue;\n        const root=Math.sqrt(Math.max(0,discriminant)),near=projection-root,far=projection+root;\n        if(far<eps)continue;\n        entries.push({i:c.b.i,n:c.b.n,t:Math.max(0,near)});\n      }\n      if(!entries.length)continue;\n      const nearest=Math.min(...entries.map(e=>e.t));\n      const first=entries.filter(e=>Math.abs(e.t-nearest)<=eps);\n      if(first.every(e=>on.includes(e.n)) && nearest>eps) {\n        const point={x:cue.x+direction.x*nearest,y:cue.y,z:cue.z+direction.z*nearest};\n        if(options.isPathClear && !options.isPathClear(cue,point))continue;\n        return {hasDirectHit:true,indeterminate:false,target:first[0].i,direction,contactPoint:point,reason:'Direct first contact with a ball on is available.'};\n      }\n    }\n    if(touching) return unknown('Cue is touching or overlapping an object; touching-ball ruling required.');\n    return {hasDirectHit:false,indeterminate:false,target:null,direction:null,reason:'Every straight ray to a ball on first meets a ball not on.'};\n  }\n\n  // Nominate BEFORE the stroke from the current horizontal aim, never from its\n  // eventual outcome. A farther ball on the same ray cannot obscure the intent\n  // to hit the nearer ball. Touching/tangent/tied contacts need a declaration.\n  function inferColour(balls, direction) {\n    const unknown = reason => ({colour:null,ballIndex:null,reason});\n    const cue = balls.find(b => b.n === 0 && active(b));\n    const length = Math.hypot(direction?.x, direction?.z);\n    if (!cue || !Number.isFinite(length) || length < 1e-9) return unknown('invalid-aim');\n    const dx = direction.x / length, dz = direction.z / length, entries = [];\n    for (const b of balls) {\n      if (!active(b) || b.n < 1) continue;\n      const x = b.x-cue.x, z = b.z-cue.z, rr = radius(cue)+radius(b);\n      if (Math.hypot(x,z) <= rr+1e-8) return unknown('touching');\n      const projection = x*dx+z*dz;\n      const disc = rr*rr-(x*x+z*z-projection*projection);\n      if (projection <= 0 || disc < -1e-12) continue;\n      entries.push({b,t:projection-Math.sqrt(Math.max(0,disc)),tangent:disc <= 1e-12});\n    }\n    entries.sort((a,b) => a.t-b.t);\n    if (!entries.length) return unknown('no-direct-target');\n    const first = entries[0];\n    if (first.tangent || entries[1] && entries[1].t-first.t < 1e-7) return unknown('ambiguous');\n    if (first.b.n < 2) return unknown('blocked-by-red');\n    return {colour:first.b.n,ballIndex:first.b.i,reason:'direct'};\n  }\n\n  function lerp(a, b, u) { return {x:a.x+(b.x-a.x)*u, y:a.y+(b.y-a.y)*u, z:a.z+(b.z-a.z)*u}; }\n  function sampleBall(sample, b, indexed) {\n    if (!sample.balls) return b;\n    // Only rows whose IDs exactly match every array index may bypass find.\n    // Other rows retain its first-match behavior, including duplicate IDs.\n    const found = indexed && Number.isInteger(b.i) && b.i>=0 && b.i<sample.balls.length ? sample.balls[b.i] : sample.balls.find(v => v.i === b.i);\n    return found || {...b,active:false};\n  }\n  function traceReader(trace) {\n    if(typeof trace.readCue==='function' && typeof trace.readBall==='function')\n      return {length:trace.length,cue:(k,out)=>trace.readCue(k,out),ball:(k,b,out)=>trace.readBall(k,b,out),hasBalls:()=>true};\n    // Validate legacy object rows locally. Non-indexed/duplicate IDs retain\n    // the original first-match lookup and missing-ball behavior.\n    const indexedRows=new Uint8Array(trace.length);\n    for(let k=0;k<trace.length;k++) {\n      const row=trace[k].balls;\n      if(!row)continue;\n      let indexed=true;\n      for(let i=0;i<row.length;i++)if(!row[i] || row[i].i!==i){indexed=false;break;}\n      if(indexed)indexedRows[k]=1;\n    }\n    return {length:trace.length,cue:k=>trace[k],ball:(k,b)=>sampleBall(trace[k],b,indexedRows[k]),hasBalls:k=>!!trace[k].balls};\n  }\n  function ballAt(reader, b, t) {\n    const a={},next={},objectA={},objectB={};\n    let j = 0;\n    while (j + 1 < reader.length && reader.cue(j+1,next).t < t) j++;\n    if (j + 1 === reader.length) return reader.ball(j,b,objectA);\n    const current=reader.cue(j,a),following=reader.cue(j+1,next);\n    const u = Math.max(0, Math.min(1, (t-current.t) / (following.t-current.t || 1)));\n    return lerp(reader.ball(j,b,objectA),reader.ball(j+1,b,objectB),u);\n  }\n\n  // Relative swept-disc overlap, retaining only points with the cue above\n  // the object's surface. Merely lifting the cue/using masse is not a foul.\n  function sweptOver(a, b, objectA, objectB, rr, eps) {\n    const py=a.y-objectA.y,vy=b.y-objectB.y-py,endY=py+vy;\n    // Use the same relative-height interpolation as below, including its\n    // rounded endpoint. A finite linear segment cannot rise above both ends.\n    // Non-finite inputs retain the original conservative geometry path.\n    if(Number.isFinite(py)&&Number.isFinite(vy)&&Number.isFinite(endY)&&py<=eps&&endY<=eps)return null;\n    const px=a.x-objectA.x,pz=a.z-objectA.z;\n    const vx=b.x-objectB.x-px,vz=b.z-objectB.z-pz;\n    const limit2=(rr-eps)*(rr-eps);\n    const A = vx*vx+vz*vz, B = 2*(px*vx+pz*vz), C = px*px+pz*pz-limit2;\n    let lo = 0, hi = 1;\n    if (A < eps*eps) { if (C >= 0) return null; }\n    else {\n      const D = B*B-4*A*C;\n      if (D <= 0) return null;\n      lo = Math.max(0,(-B-Math.sqrt(D))/(2*A));\n      hi = Math.min(1,(-B+Math.sqrt(D))/(2*A));\n      if (lo > hi) return null;\n    }\n    // Total distance squared is convex. Endpoints and horizontal closest\n    // approach catch above-surface passage without treating overlap caused\n    // by the collision solver's penetration tolerance as an illegal jump.\n    const near = A > 0 ? Math.max(lo,Math.min(hi,-B/(2*A))) : (lo+hi)/2;\n    for (let i=0;i<4;i++) {\n      const u=i===0?near:i===1?(lo+hi)/2:i===2?lo+(hi-lo)*1e-4:hi-(hi-lo)*1e-4;\n      const qx=px+u*vx, qy=py+u*vy, qz=pz+u*vz;\n      const horizontal2 = qx*qx+qz*qz;\n      if (qy > eps && horizontal2 < limit2 && horizontal2+qy*qy >= limit2) return {u,position:lerp(a,b,u)};\n    }\n    return null;\n  }\n\n  /** Physics-step trace; optional trace[k].balls records moving object centres.\n   * contactEvents: {t,ballIndex,legal?}; cushions: {t,kind:'cushion'}.\n   * legal is only needed for exception 20(c). Missing legal metadata is treated\n   * conservatively; other rule checks still reject an illegal first hit.\n   * Borderline/unfinished airborne paths are indeterminate, not auto-penalised.\n   */\n  function evaluateJump(trace, ballsAtStart, contactEvents = [], fallbackRadius = RADIUS) {\n    if (!trace || trace.length < 2) return {foul:false, offendingBalls:[], reason:'Insufficient trajectory.', indeterminate:true, details:[]};\n    const reader=traceReader(trace);\n    const cue = ballsAtStart.find(b => b.n === 0) || {r:fallbackRadius,...reader.cue(0,{})};\n    const rc = radius(cue,fallbackRadius), eps = Math.max(1e-6,rc*0.002);\n    const groundY = cue.y;\n    const events = contactEvents.slice().sort((a,b) => a.t-b.t);\n    const objects = ballsAtStart.filter(b => b.n > 0 && active(b));\n    const touching = new Set(objects.filter(b => Math.hypot(cue.x-b.x,cue.y-b.y,cue.z-b.z) <= rc+radius(b,fallbackRadius)+eps).map(b => b.i));\n    const contacts = events.filter(e => e.ballIndex != null && objects.some(b => b.i === e.ballIndex));\n    const first = contacts[0];\n    const offendingBalls = [], details = [];\n    let indeterminate = false;\n    const cueA={},cueB={},objectA={},objectB={},takeoff={},landing={};\n    for (const object of objects) {\n      const passages=[];\n      let wasOver=false;\n      let previous=reader.ball(0,object,objectA);\n      for (let k=0;k<trace.length-1;k++) {\n        const a=reader.cue(k,cueA),b=reader.cue(k+1,cueB),oa=previous,ob=reader.ball(k+1,object,k%2?objectA:objectB);\n        previous=ob;\n        if (oa.active === false || ob.active === false) {wasOver=false;continue;}\n        const over=sweptOver(a,b,oa,ob,rc+radius(object,fallbackRadius),eps);\n        if (over && !wasOver) passages.push({k,t:a.t+(b.t-a.t)*over.u,position:over.position});\n        wasOver=!!over;\n      }\n      for(const passage of passages) {\n      const detail = {ballIndex:object.i,t:passage.t};\n      if (first && first.t <= passage.t && first.ballIndex !== object.i && !touching.has(first.ballIndex)) {\n        details.push({...detail,exception:'20(a): first hit another non-touching object ball.'});\n        continue;\n      }\n      const prior = contacts.find(e => e.ballIndex===object.i && e.t<=passage.t && !touching.has(e.ballIndex));\n      if (prior && prior.legal !== false && events.some(e => e.t > prior.t && e.t < passage.t && (e.kind==='cushion' || (e.ballIndex!=null && e.ballIndex!==object.i)))) {\n        details.push({...detail,exception:'20(c): returned after object/cushion contact.'});\n        continue;\n      }\n      // Find the takeoff and landing belonging to this airborne passage.\n      let start=passage.k;\n      while(start>0 && reader.cue(start,takeoff).y>groundY+eps) start--;\n      let land=passage.k+1;\n      while(land<trace.length && reader.cue(land,landing).y>groundY+eps) land++;\n      const startPoint=reader.cue(start,takeoff),landPoint=land<trace.length?reader.cue(land,landing):null;\n      const hitDuringFlight = contacts.find(e => e.ballIndex===object.i && e.t>=startPoint.t && (!landPoint || e.t<=landPoint.t));\n      if (hitDuringFlight && !touching.has(object.i)) {\n        if (land===trace.length) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball; landing not yet recorded.'});continue;}\n        if(!reader.hasBalls(land)) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball current position at landing is unavailable.'});continue;}\n        const objectAtLanding=ballAt(reader,object,landPoint.t);\n        const approach=ballAt(reader,object,passage.t);\n        const vx=approach.x-startPoint.x,vz=approach.z-startPoint.z;\n        const length=Math.hypot(vx,vz);\n        const far=length ? ((landPoint.x-objectAtLanding.x)*vx+(landPoint.z-objectAtLanding.z)*vz)/length : 0;\n        if (far <= eps) {details.push({...detail,exception:'20(b): hit airborne, landed on near side of the ball current position.'});continue;}\n        if (far < rc+radius(object,fallbackRadius)+eps) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Landing close to dividing plane; manual decision required.'});continue;}\n      }\n      offendingBalls.push(object.i);\n      details.push({...detail,foul:true,reason:'Cue passed above an object ball without a recorded exception.'});\n      }\n    }\n    return {foul:offendingBalls.length>0,offendingBalls:unique(offendingBalls),reason:offendingBalls.length?'Illegal jump over an object ball.':indeterminate?'Some airborne contact needs review.':'No illegal jump found.',indeterminate,details};\n  }\n\n  // Section 3.4: assess the scores after the final Black's pot or foul.\n  function blackFrameOutcome({ballOn,balls,score,scores,respottedBlack=false}) {\n    if(ballOn!==128 || score===0 || scores.length!==2)return null;\n    const remaining=balls.filter(b=>b.n>0 && active(b));\n    if(remaining.length!==1 || remaining[0].n!==7)return null;\n    return !respottedBlack && scores[0]===scores[1]?'respot':'end';\n  }\n\n  /** Indices identify firstHits (simultaneous), potted, outOfBounds and nominee.\n   * nominatedColour is a number 2..7. balls contains final positions and all\n   * objects including inactive entries. Removed indices are also excluded when\n   * callers supply pre-stroke active flags. Colours to respot are indices.\n   * This pure function does not decide discretionary Foul and a Miss, restore\n   * positions, choose colour spot geometry, or decide a tied-frame re-spot.\n   */\n  function adjudicate({ballOn,nominatedColour=null,freeBallNominee=null,balls,firstHits=[],potted=[],outOfBounds=[],jumpFoul=false,touchingAtStart=[],pushedTouching=[],cueStrikes=1}) {\n    const byIndex=new Map(balls.map(b=>[b.i,b]));\n    const hits=unique(firstHits).map(i=>byIndex.get(i)).filter(b=>b && b.n>0);\n    const pots=unique(potted).map(i=>byIndex.get(i)).filter(Boolean);\n    const outs=unique(outOfBounds).map(i=>byIndex.get(i)).filter(Boolean);\n    const removed=new Set([...potted,...outOfBounds]);\n    const onNumbers=ballOnNumbers(ballOn), colourChoice=ballOn===COLOUR_ALL;\n    const nominee=freeBallNominee==null?null:byIndex.get(freeBallNominee);\n    let on=onNumbers.length===1?onNumbers[0]:null;\n    if(colourChoice) on=nominatedColour>=2 && nominatedColour<=7?nominatedColour:(hits.length===1 && hits[0].n>=2?hits[0].n:null);\n    let foulCode=0,penalty=0;\n    const reasons=[];\n    const penalise=(code,value,reason)=>{foulCode|=code;penalty=Math.max(penalty,4,value||0);reasons.push(reason);};\n    const baseValue=on || (colourChoice?7:4);\n    const validNominee=nominee && nominee.n>0 && nominee.n!==on;\n    const value=b=>validNominee && b.i===nominee.i?baseValue:b.n;\n    const touching=unique(touchingAtStart).map(i=>byIndex.get(i)).filter(b=>b && b.n>0);\n    const deemedHit=validNominee?touching.some(b=>b.i===nominee.i):on!=null && touching.some(b=>b.n===on);\n    if(freeBallNominee!=null && !validNominee) penalise(FOUL.FIRST_HIT,baseValue,'Invalid free-ball nomination.');\n    if(!deemedHit && hits.length===0) penalise(FOUL.MISS,baseValue,'No object ball contacted.');\n    else if(!deemedHit) {\n      const firstLegal=validNominee?hits.some(b=>b.i===nominee.i) && hits.every(b=>b.i===nominee.i || b.n===on):on!=null && hits.every(b=>b.n===on);\n      if(!firstLegal) penalise(FOUL.FIRST_HIT,Math.max(baseValue,...hits.map(value)),'First contact was not on.');\n    }\n    for(const i of unique(pushedTouching)) {\n      const b=touching.find(b=>b.i===i);\n      if(b) penalise(FOUL.PUSH,Math.max(baseValue,value(b)),'Striking the cue caused an initially touching ball to move before playing away.');\n    }\n    if(cueStrikes>1)penalise(FOUL.DOUBLE_HIT,baseValue,'The cue tip struck the cue ball more than once in this stroke.');\n    for(const b of pots) {\n      if(b.n===0) penalise(FOUL.CUE_POTTED,baseValue,'Cue ball pocketed.');\n      else if(b.n!==on && !(validNominee && b.i===nominee.i)) penalise(FOUL.POTTING,Math.max(baseValue,value(b)),'Ball not on pocketed.');\n    }\n    for(const b of outs) penalise(FOUL.OFF_TABLE,Math.max(baseValue,value(b)),'Ball forced off the table.');\n    if(jumpFoul===true || jumpFoul && jumpFoul.foul) penalise(FOUL.JUMP,baseValue,'Illegal jump.');\n    let points=on===1?pots.filter(b=>b.n===1 || validNominee && b.i===nominee.i).length:pots.some(b=>b.n===on || validNominee && b.i===nominee.i)?(on||0):0;\n    const finalBalls=balls.map(b=>removed.has(b.i)?{...b,active:false}:b);\n    let freeBallSafety=null;\n    if(validNominee && !foulCode && points===0) {\n      const remaining=finalBalls.filter(b=>b.n>0 && active(b));\n      const twoColoursWithBlack=remaining.length===2 && remaining.every(b=>b.n>=2) && remaining.some(b=>b.n===7);\n      if(!twoColoursWithBlack) {\n        freeBallSafety=isSnookered(finalBalls,1<<on);\n        if(freeBallSafety.snookered && freeBallSafety.effectiveSnookeringBalls.includes(nominee.i)) penalise(FOUL.FREE_BALL_SNOOKER,baseValue,'Nominated free ball left an effective snooker after a non-scoring stroke.');\n      }\n    }\n    const score=foulCode?-penalty:points;\n    const redsRemain=finalBalls.some(b=>b.n===1 && active(b));\n    const canonicalPotted=pots.some(b=>b.n===on && !(validNominee && b.i===nominee.i));\n    let nextBallOn=ballOn;\n    if(score>0) {\n      if(ballOn===RED) nextBallOn=COLOUR_ALL;\n      else if(colourChoice) nextBallOn=redsRemain?RED:4;\n      else if(canonicalPotted) nextBallOn=on===7?0:1<<(on+1);\n    } else if(ballOn===RED || colourChoice) nextBallOn=redsRemain?RED:4;\n    // The host retains responsibility for tied scores and re-spotted black.\n    if(on===7 && !colourChoice && score<0 && !validNominee) nextBallOn=0;\n    const respots=unique([...pots,...outs].filter(b=>b.n>=2 && (foulCode || ballOn===RED || colourChoice || validNominee && b.i===nominee.i)).map(b=>b.i)).sort((a,b)=>byIndex.get(b).n-byIndex.get(a).n);\n    const cueBall=balls.find(b=>b.n===0);\n    const requiresInHand=!!cueBall && (removed.has(cueBall.i) || !active(cueBall));\n    return {score,foulCode,nextBallOn,respots,requiresInHand,ballOnUsed:on,penalty:foulCode?penalty:0,freeBallNominee:validNominee?nominee.i:null,reasons,freeBallSafety,canonicalPotted,continueBreak:score>0,cueStrikes,touching:{indices:touching.map(b=>b.i),deemedHit,pushedIndices:unique(pushedTouching)}};\n  }\n  return Object.freeze({RADIUS,RED,COLOUR_ALL,FOUL,CONTACT_EPS,TOUCH_EPS,ballOnNumbers,pinkRespotX,touchingStatus,remainingPoints,concessionStatus,earlyFrameOutcome,isSnookered,hasDirectHit,inferColour,evaluateJump,blackFrameOutcome,adjudicate});\n})();\n\n/* Isolated full-shot runner. This function is stringified into a dedicated worker. */\nfunction PCOLTrialWorker(options) {\n  'use strict';\n  const listen=options?.listen!==false;\n  let setup = null;\n  const requireModules = sources => {\n    const cache = Object.create(null);\n    function req(id) {\n      if (cache[id]) return cache[id].exports;\n      if (typeof sources[id] !== 'string') throw new Error('Missing physics module ' + id);\n      const mod = cache[id] = {exports:{}};\n      new Function('return (' + sources[id] + ')')()(mod, mod.exports, req);\n      return mod.exports;\n    }\n    req.o = (object, key) => Object.prototype.hasOwnProperty.call(object, key);\n    req.d = (exports, key, getter) => {\n      if (!req.o(exports,key)) Object.defineProperty(exports,key,{enumerable:true,get:getter});\n    };\n    req.r = exports => {\n      if (typeof Symbol !== 'undefined' && Symbol.toStringTag) Object.defineProperty(exports,Symbol.toStringTag,{value:'Module'});\n      Object.defineProperty(exports,'__esModule',{value:true});\n    };\n    req.n = mod => {\n      const getter = mod && mod.__esModule ? () => mod.default : () => mod;\n      req.d(getter,'a',getter); return getter;\n    };\n    return req;\n  };\n  const clock = () => performance.now();\n  const centres = world => world.balls.map(b => ({i:b.index,n:b.number,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,r:b.radius}));\n\n  function init(message) {\n    if(!message.modules || !message.geometry || !message.geometry.data || !(message.stepSize>0) || !Number.isFinite(message.stepSize) || !Number.isInteger(message.maxIter) || message.maxIter<1 || message.maxIter>100)throw new Error('Invalid worker initialization');\n    const req=requireModules(message.modules),MeshBody=req(84),mesh=new MeshBody(message.geometry.data);\n    mesh.id=message.geometry.id;\n    for(const group of mesh.groups) {\n      const nt=message.geometry.data[group.name].nt;\n      if(nt) {\n        const uv=req(80),table=uv.createNTableWithImgData({width:0,height:0,data:[]});\n        Object.assign(table,nt);uv.extendPolyGroup(group,table);\n      }\n    }\n    // Native collision/contact state belongs to each World, not MeshBody.\n    // Polygon._size is only a deterministic lazy geometry cache. Reuse this\n    // worker-owned geometry, but keep balls, solver and all contacts per shot.\n    setup={req,mesh,compiler:message.compiler,stepSize:message.stepSize,maxIter:message.maxIter};\n    return {ready:true};\n  }\n\n  function createCompiler() {\n    if(!setup || !setup.compiler)throw new Error('Native trial compiler is not initialized');\n    return PCOLTrialShot.createCompiler(setup.compiler,setup.req);\n  }\n\n  function preservePinkRespot(ref) {\n    const original=ref._liveRespotColorBalls;\n    ref._liveRespotColorBalls=function(list,sim) {\n      if(!list.some(b=>b.number===6))return original.call(this,list,sim);\n      const clearance=1.05*sim.ballRadius,reserved=new Set();\n      for(let i=list.length-1;i>=0;i--) {\n        const b=list[i];reserved.add(b.number);\n        if(!sim.touchBalls(b.index,b.spot,clearance)){list.splice(i,1);sim.respotIndexDefault(b.index);}\n      }\n      list.sort((a,b)=>a.number-b.number);\n      const colours=sim.getBalls().filter(b=>b.number>=2).sort((a,b)=>b.number-a.number);\n      for(const spotBall of colours) {\n        if(!list.length)break;\n        const b=list[list.length-1];\n        if(!reserved.has(spotBall.number)&&!sim.touchBalls(b.index,spotBall.spot,clearance))sim.resetBallPosition(list.pop(),spotBall.spot);\n      }\n      while(list.length) {\n        const b=list.pop();\n        if(b.number!==6){original.call(this,[b],sim);continue;}\n        const ground=sim.ground,margin=sim.ballRadius+2*PCOLCore.CONTACT_EPS;\n        const minX=ground.centerPosition.x-ground.size.x/2+margin,maxX=ground.centerPosition.x+ground.size.x/2-margin;\n        const bs=sim.getBalls().map(b=>({i:b.index,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,r:b.radius}));\n        const x=PCOLCore.pinkRespotX(bs,{i:b.index,...b.spot,r:b.radius},minX,maxX);\n        if(x===null)throw new Error('No legal pink-ball respot position');\n        sim.resetBallXYZ(b,x,b.spot.y,b.spot.z);\n      }\n    };\n  }\n\n  function simulate(message) {\n    if (!setup) throw new Error('Worker is not initialized');\n    const {snapshot,stroke} = message, options = message.options || {};\n    if (!snapshot || !snapshot.serial || !Array.isArray(snapshot.balls) || !snapshot.rules) throw new Error('Invalid trial snapshot');\n    if ((!Array.isArray(stroke) && !ArrayBuffer.isView(stroke)) || stroke.length !== 8 || !Array.from(stroke).every(Number.isFinite)) throw new Error('Invalid trial stroke');\n    const started = clock(), req = setup.req;\n    const World=req(39), Ball=req(49), Simulator=req(50), Solver=req(21);\n    const world = new World();\n    world.stepSize=setup.stepSize;\n    world.solver=new Solver();\n    world.solver.maxIter=setup.maxIter;\n    world.setMeshBody(setup.mesh);\n    for (const b of snapshot.balls) {\n      if (b.i !== world.balls.length || !(b.r>0) || !(b.mass>0) || !b.spot) throw new Error('Invalid ball configuration');\n      world.addBall(new Ball(b.n,b.r,b.mass,b.spot.x,b.spot.y,b.spot.z,b.i));\n    }\n    world.reset();\n    world.deserialize(snapshot.serial);\n    for(const source of snapshot.balls) {\n      const transient=source.transient;\n      if(!transient)continue;\n      const ball=world.balls[source.i];\n      for(const key of ['rfPower','penetration','collisionMask']) {\n        if(transient[key]!==undefined)ball[key]=transient[key];\n      }\n      for(const key of ['rfDir','peneOffset']) {\n        if(transient[key])ball[key].copy(transient[key]);\n      }\n    }\n    const sim=new Simulator('trial',world,null);\n    sim._syncList.ballRadius=world.balls[0].radius;\n    sim._sceneId=snapshot.sceneId || 'tigerClubSno';\n    sim._spotY=sim.ground.centerPosition.y+sim.ballRadius;\n    if(options.scenarioBalls)for(const b of options.scenarioBalls){\n      const ball=world.balls[b.i];\n      if(b.active!==false)sim.respotIndexXYZ(b.i,b.x,b.y,b.z);\n      else ball.active=false;\n    }\n    if (options.cuePosition != null) {\n      const position=options.cuePosition;\n      if (!['x','y','z'].every(key=>Number.isFinite(position[key]))) throw new Error('Invalid trial cue position');\n      sim.respotIndexXYZ(0,position.x,position.y,position.z);\n    }\n    const before=centres(world), rules={...snapshot.rules},custom=rules.ballOn===65535;\n    // A banked colour shot must declare its target before physics, rather than\n    // trying to infer a colour from the initial ray toward a cushion.\n    if (options.nominatedColour != null) {\n      const colour=options.nominatedColour;\n      if(rules.ballOn!==252 || !Number.isInteger(colour) || colour<2 || colour>7 ||\n        (rules.nominatedColour && rules.nominatedColour!==colour) ||\n        !before.some(b=>b.active && b.n===colour)) throw new Error('Invalid trial colour nomination');\n      rules.nominatedColour=colour;rules.nominationSource='manual';\n    }\n    const reviewReasons=[];\n    let touching=PCOLCore.touchingStatus({balls:before,...rules});\n    if(!custom) {\n      if(rules.freeBallReview)reviewReasons.push('Free-ball decision requires review.');\n      if(rules.freeBallAvailable && rules.freeBallNominee==null && !rules.freeBallDeclined)reviewReasons.push('Nominate or decline the available free ball.');\n      if(touching.requiresColourDeclaration && rules.nominationSource!=='manual')reviewReasons.push('Touching colour requires manual nomination.');\n      if(rules.ballOn===252 && !rules.nominatedColour && !touching.requiresColourDeclaration) {\n        const inferred=PCOLCore.inferColour(before,{x:stroke[3],z:stroke[5]});\n        if(inferred.colour) {\n          rules.nominatedColour=inferred.colour;rules.nominationSource='auto';\n          touching=PCOLCore.touchingStatus({balls:before,...rules});\n        } else reviewReasons.push('Colour nomination is ambiguous.');\n      }\n    }\n    const watches=new Map(touching.indices.map(i=>[i,{initial:true}]));\n    const trace=PCOLShotTrace.create(world.balls,{cap:15000,seconds:true}), contacts=[], pushedTouching=[];\n    let overflow=false,recording=false,steps=0,simulatedSeconds=0,cueStrikes=0;\n    function sample() {\n      const row=trace.sample(world.balls,simulatedSeconds);\n      if(!row){overflow=true;return null;}\n      const cue=world.balls[0],q=cue.position;\n      for(const [i,watch] of watches) {\n        const b=world.balls[i],p=b.position;\n        if(watch.initial && (!b.active || Math.hypot(q.x-p.x,q.y-p.y,q.z-p.z)>cue.radius+b.radius+PCOLCore.TOUCH_EPS*2)) watch.initial=false;\n      }\n      return row;\n    }\n    function record(contact,vix,viy,viz,vjx,vjy,vjz,closeSpeed) {\n      if (!(closeSpeed < -1e-6)) return;\n      const q=contact.bi.number===0?contact.bi:contact.isSS && contact.bj.number===0?contact.bj:null;\n      if (!contact.isSS) {\n        const normal=contact.normal || contact.bj.normal;\n        if(!q || contact.bj.end || contact.bj.tunnel || !normal || Math.abs(normal.y)>=.7)return;\n        if(!((q.v.x-vix)*normal.x+(q.v.y-viy)*normal.y+(q.v.z-viz)*normal.z>1e-7))return;\n        const row=sample();if(!row)return;\n        contacts.push({t:row.t,kind:'cushion',evolution:world.evolution,x:row.x,y:row.y,z:row.z});\n        for(const watch of watches.values())watch.initial=false;\n        return;\n      }\n      if(!q) {\n        if(!watches.size)return;\n        const bi=contact.bi,bj=contact.bj;\n        if(Math.hypot(bi.v.x-vix,bi.v.y-viy,bi.v.z-viz)>1e-7) {\n          const watch=watches.get(bi.index);if(watch)watch.initial=false;\n        }\n        if(Math.hypot(bj.v.x-vjx,bj.v.y-vjy,bj.v.z-vjz)>1e-7) {\n          const watch=watches.get(bj.index);if(watch)watch.initial=false;\n        }\n        return;\n      }\n      const cueIsI=q===contact.bi,obj=cueIsI?contact.bj:contact.bi;\n      const vx=cueIsI?vjx:vix,vy=cueIsI?vjy:viy,vz=cueIsI?vjz:viz;\n      const dx=obj.position.x-q.position.x,dy=obj.position.y-q.position.y,dz=obj.position.z-q.position.z;\n      const distance=Math.hypot(dx,dy,dz);\n      if(!distance || !(((obj.v.x-vx)*dx+(obj.v.y-vy)*dy+(obj.v.z-vz)*dz)/distance>1e-7))return;\n      const row=sample();if(!row)return;\n      const initialPush=watches.get(obj.index)?.initial;\n      if(initialPush && !pushedTouching.includes(obj.index))pushedTouching.push(obj.index);\n      const target=rules.ballOn===252 && rules.nominatedColour?2**rules.nominatedColour:rules.ballOn;\n      const allowed=touching.deemedHit || obj.index===rules.freeBallNominee || PCOLCore.ballOnNumbers(target).includes(obj.number);\n      const firstLegal=!contacts.some(c=>c.ballIndex!=null && c.legal===false);\n      contacts.push({t:row.t,ballIndex:obj.index,evolution:world.evolution,x:row.x,y:row.y,z:row.z,legal:allowed && firstLegal});\n      if(!initialPush)for(const watch of watches.values())watch.initial=false;\n    }\n    const solve=world.solver.solveContact;\n    world.solver.solveContact=function(contact) {\n      if(contact===world.tipContact&&contact.getCloseSpeed() < -1e-6)cueStrikes++;\n      const capture=recording && (contact.isSS || contact.bi.number===0);\n      // These pre-solve values are used only by this synchronous call. Scalars\n      // avoid temporary vector objects without sharing mutable contact state.\n      let vix,viy,viz,vjx,vjy,vjz;\n      if(capture) {\n        vix=contact.bi.v.x;viy=contact.bi.v.y;viz=contact.bi.v.z;\n        if(contact.isSS){vjx=contact.bj.v.x;vjy=contact.bj.v.y;vjz=contact.bj.v.z;}\n      }\n      const speed=capture?contact.getCloseSpeed():0;\n      const result=solve.call(this,contact);\n      if(capture)record(contact,vix,viy,viz,vjx,vjy,vjz,speed);\n      return result;\n    };\n    const internal=world.internalStep;\n    world.internalStep=function(){const result=internal.call(this);sample();return result;};\n    sim.stroke(Array.from(stroke));\n    recording=true;\n    const cue=world.balls[0];\n    for(const [i,watch] of watches) {\n      const obj=world.balls[i],dx=obj.position.x-cue.position.x,dy=obj.position.y-cue.position.y,dz=obj.position.z-cue.position.z;\n      const distance=Math.hypot(dx,dy,dz);\n      if(distance && (cue.v.x*dx+cue.v.y*dy+cue.v.z*dz)/distance < -1e-6)watch.initial=false;\n    }\n    sample();\n    const maxSteps=Number.isFinite(options.maxSteps)?Math.max(1,Math.min(100000,Math.floor(options.maxSteps))):12000;\n    const maxWallMs=Number.isFinite(options.maxWallMs)?Math.max(1,Math.min(60000,options.maxWallMs)):5000;\n    let reason=null;\n    do {\n      if(clock()-started>=maxWallMs){reason='wall-time limit';break;}\n      simulatedSeconds+=sim.step(setup.stepSize);steps++;\n      if(overflow){reason='trajectory limit';break;}\n      if(!world.balls.some(b=>b.active && !b.asleep))break;\n      if(steps>=maxSteps){reason='step limit';break;}\n    } while(true);\n    const balls=centres(world),status=reason?'incomplete':'complete';\n    const first=contacts.find(c=>c.ballIndex!=null);\n    const firstHits=first?[...new Set(contacts.filter(c=>c.ballIndex!=null && c.evolution===first.evolution && Math.hypot(c.x-first.x,c.y-first.y,c.z-first.z)<1e-5).map(c=>c.ballIndex))]:[];\n    const jump=PCOLCore.evaluateJump(trace,before,contacts,sim.ballRadius);\n    if(reason) {jump.indeterminate=true;jump.reason=reason;}\n    const potted=[...sim.result.pottedIndices],outOfBounds=[...sim.result.outOfBoundsIndices];\n    if(!custom && jump.indeterminate)reviewReasons.push('Jump assessment requires review.');\n    const adjudication=!custom && status==='complete' && !reviewReasons.length?PCOLCore.adjudicate({...rules,balls,firstHits,potted,outOfBounds,jumpFoul:jump.foul,touchingAtStart:touching.indices,pushedTouching,cueStrikes}):null;\n    const afterScores=(rules.scores||[]).map((score,index)=>score+(adjudication?.score>0 && index===rules.playerIndex?adjudication.score:adjudication?.score<0 && index!==rules.playerIndex?-adjudication.score:0));\n    const blackFrame=adjudication?PCOLCore.blackFrameOutcome({ballOn:rules.ballOn,balls:before,score:adjudication.score,scores:afterScores,respottedBlack:rules.respottedBlack}):null;\n    if(blackFrame){adjudication.frameOutcome=blackFrame;adjudication.continueBreak=false;}\n    const result={status,steps,simulatedSeconds,elapsedMs:clock()-started,balls,potted,outOfBounds,firstHits,contacts,stroke:Array.from(stroke),adjudication,jump};\n    if(reviewReasons.length)result.reviewReasons=reviewReasons;\n    if(status==='complete' && (custom || adjudication)) {\n      const Ref=req(54),ref=new Ref();\n      ref.syncAreaWithSimulator(sim);\n      preservePinkRespot(ref);\n      if(custom) {\n        if(!world.balls[0].active)ref._liveRespotCueBall(sim);\n      } else {\n        ref._liveRespot(adjudication.respots,[],sim);\n        if(adjudication.requiresInHand)ref._liveRespotCueBall(sim);\n        if(blackFrame==='respot'){\n          ref._liveRespotCueBall(sim);\n          sim.respotIndexDefault(world.balls.find(b=>b.number===7).index);\n        }\n      }\n      result.nextBalls=centres(world);\n      result.nextContext={ballOn:custom?65535:adjudication.nextBallOn,inHand:custom?1:adjudication.requiresInHand?2:0};\n      if(blackFrame==='respot')Object.assign(result.nextContext,{ballOn:128,inHand:2,respottedBlack:true,requiresDraw:true});\n      if(blackFrame==='end')Object.assign(result.nextContext,{ballOn:0,inHand:0});\n      // Only adjudicated legal continuations have an automatic next player/state.\n      // Fouls, cue placement and a drawn black decider require human decisions.\n      if(!custom && !adjudication.foulCode && !adjudication.requiresInHand && !result.nextContext.requiresDraw) {\n        const nextRules={...rules,...result.nextContext,scores:afterScores,\n          nRounds:(rules.nRounds || 0)+1,\n          playerIndex:adjudication.continueBreak?rules.playerIndex:(rules.playerIndex+1)%Math.max(1,afterScores.length),\n          nominatedColour:null,nominationSource:null,freeBallNominee:null,\n          freeBallAvailable:false,freeBallReview:false,freeBallDeclined:false,\n          respottedBlack:blackFrame==='end'?false:!!rules.respottedBlack};\n        result.nextSnapshot={sceneId:snapshot.sceneId,serial:world.serialize({balls:[]}),rules:nextRules,\n          balls:snapshot.balls.map(source=>{\n            const b=world.balls[source.i];\n            return {...source,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,spot:{...source.spot},transient:{rfPower:b.rfPower,\n              rfDir:{x:b.rfDir.x,y:b.rfDir.y,z:b.rfDir.z},penetration:b.penetration,\n              peneOffset:{x:b.peneOffset.x,y:b.peneOffset.y,z:b.peneOffset.z},collisionMask:b.collisionMask}};\n          })};\n      }\n    }\n    if(reason)result.reason=reason;\n    if(options.trace)result.trace=options.trace==='cue'?trace.toCueArray():trace.toArray();\n    return result;\n  }\n  if(listen)self.onmessage = event => {\n    const message=event.data;\n    try {\n      let result;\n      if(message.type==='init') result=init(message);\n      else if(message.type==='simulate') result=simulate(message);\n      else throw new Error('Unknown worker request');\n      self.postMessage({id:message.id,result});\n    } catch(error) {self.postMessage({id:message && message.id,error:String(error && error.message || error)});}\n  };\n  return {init,simulate,createCompiler};\n}\n\nPCOLTrialWorker();";

/* A lazy worker client. Only copied values cross the boundary into physics. */
const PCOLTrial = (() => {
  const moduleCache=new WeakMap();
  function collectModules(factories, compiler=false) {
    let cached=moduleCache.get(factories);
    if(!cached){cached={};moduleCache.set(factories,cached);}
    const key=compiler?'compiler':'physics';
    if(cached[key])return cached[key];
    const sources = {};
    function visit(id) {
      if (sources[id]) return;
      if(typeof factories[id]!=='function')throw new Error('Missing native module '+id);
      const source = factories[id].toString();
      sources[id] = source;
      const parameter = source.match(/^function\s*\([^,]+,[^,]+,\s*([^\s,)]+)/)?.[1];
      if (parameter) for (const match of source.matchAll(new RegExp('\\b' + parameter + '\\((\\d+)\\)', 'g'))) visit(Number(match[1]));
    }
    for (const id of compiler?[13,18,49,50,54]:[13,49,50,54]) visit(id);
    return cached[key]=sources;
  }
  function exportGeometry(mesh) {
    const data = {};
    // Preserve polygon uid order as well as shared edges from the native mesh.
    const groups = [...mesh.groups].sort((a,b) => a.polys[0].uid-b.polys[0].uid);
    for (const group of groups) {
      const vertices = new Map(), p = [], q = [];
      for (const poly of group.polys) {
        const indices = poly.edges.map(edge => {
          if (!vertices.has(edge.va)) {
            vertices.set(edge.va, p.length / 3);
            p.push(edge.va.x, edge.va.y, edge.va.z);
          }
          return vertices.get(edge.va);
        });
        const row = {i:indices,n:[poly.normal.x,poly.normal.y,poly.normal.z],
          f:['ground','sidesoft','sidehard','pocket','tunnel','end'].filter(flag => poly[flag])};
        if (poly.uv) row.uv = Array.from(poly.uv);
        if (poly.bCenter) row.s = [poly.bCenter.x,poly.bCenter.y,poly.bCenter.z,poly.bR];
        q.push(row);
      }
      data[group.name] = {p,q};
      const table = group.polys.find(poly => poly.hasCustomNormalHandler)?.nTable;
      if (table) data[group.name].nt = {array2D:table.array2D.map(row=>row.slice()),maxRow:table.maxRow,maxLine:table.maxLine};
    }
    return {id:mesh.id,data};
  }
  function create({game, factories, getRules, isReady, fixedSnapshot=null, runtimeCache={}}) {
    let worker = null, workerRuntime = null, initialized = null, pending = null, sequence = 0, generation = 0, busy = false;
    let lastResult = null;
    let cachedSnapshot = fixedSnapshot, cachedKey = fixedSnapshot ? JSON.stringify(fixedSnapshot) : null;
    const fixedKey = cachedKey;
    function dispose(reason = 'Trial cancelled') {
      generation++;
      worker?.terminate(); worker = null; initialized = null; workerRuntime = null;
      if (pending) { clearTimeout(pending.timer); pending.reject(new Error(reason)); pending = null; }
    }
    function request(type, payload, timeout = 10000) {
      return new Promise((resolve,reject) => {
        const id = ++sequence;
        pending = {id,resolve,reject,timer:setTimeout(() => dispose('Trial worker timed out'),timeout)};
        worker.postMessage({id,type,...payload});
      });
    }
    function exportPhysics() {
      const sim=game._simulator,world=sim._world;
      if(runtimeCache.mesh!==world.meshBody || runtimeCache.sceneId!==sim.sceneId) {
        runtimeCache.mesh=world.meshBody;runtimeCache.sceneId=sim.sceneId;
        runtimeCache.geometry=exportGeometry(world.meshBody);runtimeCache.physics=null;
      }
      let payload=runtimeCache.physics;
      if(!payload || payload.stepSize!==world.stepSize || payload.maxIter!==world.solver.maxIter) {
        payload=runtimeCache.physics={modules:collectModules(factories),geometry:runtimeCache.geometry,
          stepSize:world.stepSize,maxIter:world.solver.maxIter};
      }
      return payload;
    }
    function exportRuntime() {
      const physics=exportPhysics(),state=game._fpc?._stickCtl?._state1,props=state?._cachedProps;
      if(!props)throw new Error('Native shot compiler is unavailable');
      const key=JSON.stringify(['stickName','ballRadius','tipRadius','midRadius','stickLen'].map(name=>props[name]));
      if(runtimeCache.runtimePhysics!==physics || runtimeCache.compilerKey!==key || runtimeCache.cushion!==state._cushionBody) {
        const factory=factories[10],source=factory?.__pcolNativeSource || factory?.toString();
        const compiler=PCOLTrialShot.exportCompiler(game,source);
        runtimeCache.runtime={...physics,modules:collectModules(factories,true),compiler};
        runtimeCache.runtimePhysics=physics;runtimeCache.compilerKey=key;runtimeCache.cushion=state._cushionBody;
      }
      return runtimeCache.runtime;
    }
    function initialize() {
      const payload=exportPhysics();
      if (worker && workerRuntime === payload) return initialized;
      dispose();
      workerRuntime=payload;
      const url = URL.createObjectURL(new Blob([PCOLTrialWorkerSource],{type:'text/javascript'}));
      try { worker = new Worker(url); } finally { URL.revokeObjectURL(url); }
      worker.onmessage = ({data}) => {
        if (!pending || data.id !== pending.id) return;
        const task = pending; pending = null; clearTimeout(task.timer);
        data.error ? task.reject(new Error(data.error)) : task.resolve(data.result);
      };
      worker.onerror = event => dispose(event.message || 'Trial worker failed');
      initialized = request('init',payload);
      return initialized;
    }
    function fingerprint() {
      if(fixedSnapshot)return fixedKey;
      const sim=game._simulator,balls=sim.getBalls();
      if(!isReady()||balls.some(b=>b.active&&!b.asleep))throw new Error('Wait for a settled, playable table');
      return JSON.stringify([sim.sceneId,sim._world.evolution,getRules(),balls.map(b=>
        [b.index,b.number,b.radius,b.mass,b.active,b.position.x,b.position.y,b.position.z,b.spot.x,b.spot.y,b.spot.z])]);
    }
    function readSnapshot(refresh=false) {
      if(fixedSnapshot)return fixedSnapshot;
      const key=fingerprint();
      if(cachedSnapshot&&key===cachedKey&&!refresh)return cachedSnapshot;
      const sim = game._simulator;
      const state = {sceneId:sim.sceneId,serial:sim._world.serialize({balls:[]}),rules:getRules(),
        balls:sim.getBalls().map(b => ({i:b.index,n:b.number,r:b.radius,mass:b.mass,active:b.active,
          x:b.position.x,y:b.position.y,z:b.position.z,
          spot:{x:b.spot.x,y:b.spot.y,z:b.spot.z},transient:{rfPower:b.rfPower,
            rfDir:{x:b.rfDir.x,y:b.rfDir.y,z:b.rfDir.z},penetration:b.penetration,
            peneOffset:{x:b.peneOffset.x,y:b.peneOffset.y,z:b.peneOffset.z},collisionMask:b.collisionMask}}))};
      const captured=structuredClone(state);
      if(!cachedSnapshot||key!==cachedKey){cachedKey=key;cachedSnapshot=refresh?structuredClone(captured):captured;}
      return refresh?captured:cachedSnapshot;
    }
    // Explicit/public checks still capture the full world; trials reuse the settled root.
    const snapshot=()=>fixedSnapshot?structuredClone(fixedSnapshot):readSnapshot(true);
    function currentStroke() {
      const ctl = game._fpc;
      if (!ctl.isReadyToStroke()) throw new Error('Aim and let the cue settle before simulating this shot');
      const stroke = new Float32Array(ctl._strokeVars);
      stroke[6] = ctl._stickCtl.getStrokeSpdWithPower(ctl.strokePower);
      return {stroke:Array.from(stroke)};
    }
    const roots = new WeakSet();
    async function runTrial(before, root, compiled, options, rootKey) {
      busy = true;
      try {
        const ready = initialize(), run = generation;
        await ready;
        if (run !== generation || !worker) throw new Error('Trial cancelled');
        const result = await request('simulate',{snapshot:before,stroke:compiled.stroke,options},
          Math.min(60000, Math.max(1, options.maxWallMs || 5000)) + 3000);
        let stale = true;
        try { stale = rootKey !== fingerprint(); } catch (_) {}
        lastResult = {...result,stale,compiled,snapshot:root};
        roots.add(lastResult);
        return lastResult;
      } finally { busy = false; }
    }
    async function simulate(shot, options = {}) {
      if (busy) throw new Error('A trial is already running');
      const before = readSnapshot(),rootKey=cachedKey;
      const compiled = shot == null ? currentStroke() : Array.isArray(shot) || ArrayBuffer.isView(shot)
        ? {stroke:Array.from(new Float32Array(shot))} : PCOLTrialShot.compile(game,shot,fixedSnapshot?before.balls:undefined);
      return runTrial(before,before,compiled,options,rootKey);
    }
    async function simulateFrom(parentResult, shot, options = {}) {
      if (busy) throw new Error('A trial is already running');
      if (!parentResult || !roots.has(parentResult) || parentResult.stale || !parentResult.nextSnapshot || !parentResult.nextBalls)
        throw new Error('A settled legal trial continuation is required');
      if (parentResult.snapshot !== readSnapshot()) throw new Error('Trial root is stale');
      const rootKey=cachedKey;
      if (shot == null) throw new Error('A detached continuation shot is required');
      const compiled = Array.isArray(shot) || ArrayBuffer.isView(shot)
        ? {stroke:Array.from(new Float32Array(shot))} : PCOLTrialShot.compile(game,shot,parentResult.nextBalls);
      return runTrial(parentResult.nextSnapshot,parentResult.snapshot,compiled,options,rootKey);
    }
    async function simulateScenario(scenario, shot, options = {}) {
      if (busy) throw new Error('A trial is already running');
      if (!scenario || typeof scenario !== 'object' || shot == null) throw new Error('A detached scenario and shot are required');
      const root = readSnapshot(), rootKey=cachedKey, before = structuredClone(root);
      if (scenario.serial != null) {
        before.serial = structuredClone(scenario.serial);
        for (const ball of before.balls) delete ball.transient;
      }
      if (scenario.rules != null) before.rules = structuredClone(scenario.rules);
      const balls = scenario.balls != null ? structuredClone(scenario.balls)
        : game._simulator.getBalls().map(b => ({i:b.index,n:b.number,active:b.active,
          x:b.position.x,y:b.position.y,z:b.position.z,r:b.radius}));
      const trialOptions = {...options};
      if(scenario.balls != null)trialOptions.scenarioBalls=balls;
      if (scenario.cuePosition != null) {
        const position = structuredClone(scenario.cuePosition);
        if (!['x','y','z'].every(key => Number.isFinite(position[key]))) throw new Error('Invalid trial cue position');
        const cue = balls.find(b => b.n === 0);
        if (!cue) throw new Error('Scenario cue ball is unavailable');
        Object.assign(cue,position,{active:true});
        trialOptions.cuePosition = position;
      } else delete trialOptions.cuePosition;
      const compiled = Array.isArray(shot) || ArrayBuffer.isView(shot)
        ? {stroke:Array.from(new Float32Array(shot))} : PCOLTrialShot.compile(game,shot,balls);
      return runTrial(before,root,compiled,trialOptions,rootKey);
    }
    return {snapshot,fingerprint,exportRuntime,simulate,simulateFrom,simulateScenario,simulateAim:options => simulate(null,options),
      createSession:root=>create({game,factories,getRules,isReady,fixedSnapshot:structuredClone(root),runtimeCache}),
      compile:shot => { const before=readSnapshot(); return PCOLTrialShot.compile(game,shot,fixedSnapshot?before.balls:undefined); },
      cancel:() => dispose(),dispose,
      getStatus:() => ({busy,initialized:!!worker,lastResult:lastResult && {
        status:lastResult.status,stale:lastResult.stale,steps:lastResult.steps,elapsedMs:lastResult.elapsedMs}})};
  }
  return {create};
})();

/* Bounded geometric seeds and terminal-position heuristics; legality belongs to the trial. */
const PCOLSearchGeometry = (() => {
  const distance = (a,b) => Math.hypot(a.x-b.x,a.z-b.z);
  const unit = (a,b) => { const d=distance(a,b); return d>1e-9?{x:(b.x-a.x)/d,z:(b.z-a.z)/d}:null; };
  const radius = b => Number.isFinite(b.r)&&b.r>0?b.r:.026;
  const active = b => b.active!==false && Number.isFinite(b.x) && Number.isFinite(b.z);
  function targets(state, mask=state.rules?.ballOn, nominee=state.rules?.freeBallNominee) {
    const nomination=mask===252?state.rules?.nominatedColour:null;
    const effectiveMask=Number.isInteger(nomination)&&nomination>=2&&nomination<=7?1<<nomination:mask;
    return (state.balls||[]).filter(b=>active(b)&&b.n>0&&(nominee!=null?b.i===nominee:((effectiveMask||0)&(1<<b.n))));
  }
  function clear(state,a,b,movingRadius,excluded=[]) {
    const dx=b.x-a.x,dz=b.z-a.z,l2=dx*dx+dz*dz;
    if(l2<1e-12)return false;
    for(const ball of state.balls||[]){
      if(!active(ball)||excluded.includes(ball.i))continue;
      const t=Math.max(0,Math.min(1,((ball.x-a.x)*dx+(ball.z-a.z)*dz)/l2));
      const x=ball.x-a.x-t*dx,z=ball.z-a.z-t*dz,limit=movingRadius+radius(ball)-1e-5;
      // Component bounds reject distant balls without changing the contact comparison.
      if(Math.abs(x)>=limit||Math.abs(z)>=limit)continue;
      if(Math.hypot(x,z)<limit)return false;
    }
    return true;
  }
  function pocketAccepts(target,pocket) {
    const d=unit(target,pocket),n=pocket.normal;
    if(!d)return false;
    if(!n||!Number.isFinite(n.x)||!Number.isFinite(n.z))return true;
    // Native normals face into the table; maxHalfOpen is a dot threshold.
    const dot=d.x*n.x+d.z*n.z;
    return !Number.isFinite(pocket.maxHalfOpen)||dot<=pocket.maxHalfOpen;
  }
  function plantRoutes(state,cue,on=targets(state)) {
    if(!cue||!Array.isArray(on)||on.length<2)return [];
    const routes=[],pockets=state.pockets||[];
    for(const potBall of on)for(let p=0;p<pockets.length;p++){
      const pocket=pockets[p],d2=unit(potBall,pocket);
      if(!d2||!pocketAccepts(potBall,pocket)||!clear(state,potBall,pocket,radius(potBall),[cue.i,potBall.i]))continue;
      const g2={x:potBall.x-d2.x*(radius(potBall)*2),z:potBall.z-d2.z*(radius(potBall)*2)};
      for(const hitBall of on){
        if(hitBall.i===potBall.i)continue;
        const pairDist=distance(hitBall,potBall);if(pairDist>.42)continue;
        const d12=unit(hitBall,g2);if(!d12)continue;
        const plantCut=d12.x*d2.x+d12.z*d2.z;if(plantCut<.45)continue;
        if(!clear(state,hitBall,g2,radius(hitBall),[cue.i,hitBall.i,potBall.i]))continue;
        const g1={x:hitBall.x-d12.x*(radius(cue)+radius(hitBall)),z:hitBall.z-d12.z*(radius(cue)+radius(hitBall))};
        const direction=unit(cue,g1);if(!direction)continue;
        const cueCut=direction.x*d12.x+direction.z*d12.z;if(cueCut<.25)continue;
        if(!clear(state,cue,g1,radius(cue),[cue.i,hitBall.i,potBall.i]))continue;
        const gap=distance(hitBall,g2),travel=distance(cue,g1)+gap+distance(potBall,pocket);
        const deadPlant=plantCut>=.96&&pairDist<=.14;
        const cut=Math.min(.95,cueCut*(plantCut**1.15)*(deadPlant?1.08:1/(1+gap*1.1)));
        routes.push({kind:'attack',targetIndex:hitBall.i,potTargetIndex:potBall.i,pocketIndex:p,
          priority:(deadPlant?1.15:.92)/(.1+travel),label:deadPlant?'死传球进攻':'组合传球进攻',
          direction,travel,cut,plant:true,deadPlant,plantCut,cueCut});
      }
    }
    return routes.sort((a,b)=>b.priority-a.priority);
  }
  function doubleRoutes(state,cue,on=targets(state)) {
    const b=state.bounds,pockets=state.pockets||[];
    if(!cue||!b||pockets.length<2||!Array.isArray(on)||!on.length)return [];
    const routes=[];
    for(const target of on){
      const r=radius(target),walls=[
        ['z',b.minZ+r,pk=>pk.z>0],
        ['z',b.maxZ-r,pk=>pk.z<0],
        ['x',b.minX+r,pk=>pk.x>-.2],
        ['x',b.maxX-r,pk=>pk.x<.2]
      ];
      for(let p=0;p<pockets.length;p++){
        const pocket=pockets[p];
        for(const [axis,value,validPocket] of walls){
          if(!validPocket(pocket))continue;
          const other=axis==='x'?'z':'x';
          const denom=Math.abs(target[axis]-value)+Math.abs(pocket[axis]-value);
          if(denom<=1e-5)continue;
          const tRatio=Math.abs(target[axis]-value)/denom;
          const bounceNominal={x:target.x,z:target.z};
          bounceNominal[axis]=value;
          bounceNominal[other]=target[other]+(pocket[other]-target[other])*tRatio;
          if(pockets.some(q=>distance(bounceNominal,q)<.14))continue;
          const d1=distance(target,bounceNominal),d2=distance(bounceNominal,pocket);
          if(d1<=.08||d2<=.08)continue;
          const incidenceCos=Math.abs(bounceNominal[axis]-target[axis])/d1;
          if(incidenceCos<.35||!pocketAccepts(bounceNominal,pocket))continue;
          if(!clear(state,target,bounceNominal,r,[cue.i,target.i])||!clear(state,bounceNominal,pocket,r,[cue.i,target.i]))continue;
          const makeVariant=comp=>{
            const bounce={...bounceNominal};
            bounce[other]=bounceNominal[other]+(pocket[other]-bounceNominal[other])*comp;
            const d1Vec=unit(target,bounce);if(!d1Vec)return null;
            const ghost={x:target.x-d1Vec.x*(radius(cue)+r),z:target.z-d1Vec.z*(radius(cue)+r)};
            const direction=unit(cue,ghost);if(!direction)return null;
            const cueCut=direction.x*d1Vec.x+direction.z*d1Vec.z;
            return {bounce,ghost,direction,cueCut,travel:distance(cue,ghost)+d1+d2};
          };
          const primary=makeVariant(.05);
          if(!primary||primary.cueCut<.32||!clear(state,cue,primary.ghost,radius(cue),[cue.i,target.i]))continue;
          const aimVariants=[0,.05,.1].map(makeVariant).filter(v=>v&&v.cueCut>=.28&&clear(state,cue,v.ghost,radius(cue),[cue.i,target.i]));
          const cut=Math.min(.78,primary.cueCut*incidenceCos*.68);
          routes.push({kind:'attack',targetIndex:target.i,pocketIndex:p,priority:.72/(.1+primary.travel),
            label:'翻袋进攻',direction:primary.direction,aimVariants,travel:primary.travel,cut,doubleShot:true,cushionAxis:axis});
        }
      }
    }
    return routes.sort((a,b)=>b.priority-a.priority);
  }
  function attackRoutes(state,cue,on) {
    const routes=[];
    for(const target of on)for(let p=0;p<(state.pockets||[]).length;p++){
      const pocket=state.pockets[p],d=unit(target,pocket);
      if(!d||!pocketAccepts(target,pocket))continue;
      const ghost={x:target.x-d.x*(radius(cue)+radius(target)),z:target.z-d.z*(radius(cue)+radius(target))};
      const direction=unit(cue,ghost);
      const cut=direction?direction.x*d.x+direction.z*d.z:0;
      if(!direction||cut<.15)continue;
      if(!clear(state,target,pocket,radius(target),[cue.i,target.i])||!clear(state,cue,ghost,radius(cue),[cue.i,target.i]))continue;
      const travel=distance(cue,ghost)+distance(target,pocket);
      routes.push({kind:'attack',targetIndex:target.i,pocketIndex:p,priority:1/(.1+travel),label:'直线进攻',direction,travel,cut});
    }
    if(Array.isArray(on)&&on.length>=2)routes.push(...plantRoutes(state,cue,on));
    return routes.sort((a,b)=>b.priority-a.priority);
  }
  function banks(state,cue,target) {
    const b=state.bounds;if(!b)return [];
    const r=radius(cue),routes=[];
    const walls=[['x',b.minX+r],['x',b.maxX-r],['z',b.minZ+r],['z',b.maxZ-r]];
    for(const [axis,value] of walls){
      const other=axis==='x'?'z':'x',mirror={x:target.x,z:target.z};mirror[axis]=2*value-target[axis];
      const denom=mirror[axis]-cue[axis],t=(value-cue[axis])/denom;
      if(!Number.isFinite(t)||t<=0||t>=1)continue;
      const contact={x:cue.x+t*(mirror.x-cue.x),z:cue.z+t*(mirror.z-cue.z)};
      const lo=other==='x'?b.minX+r:b.minZ+r,hi=other==='x'?b.maxX-r:b.maxZ-r;
      if(contact[other]<lo||contact[other]>hi)continue;
      if(!clear(state,cue,contact,r,[cue.i])||!clear(state,contact,target,r,[cue.i,target.i]))continue;
      routes.push({kind:'escape',targetIndex:target.i,priority:.5/(.1+distance(cue,contact)+distance(contact,target)),label:'一库解球',direction:unit(cue,contact)});
    }
    return routes;
  }
  function roundRobin(items,key) {
    const groups=new Map();for(const item of items){const k=key(item);if(!groups.has(k))groups.set(k,[]);groups.get(k).push(item);}
    const out=[];for(let i=0;out.length<items.length;i++)for(const group of groups.values())if(group[i])out.push(group[i]);
    return out;
  }
  const routeKey=c=>[c.kind,c.targetIndex,c.potTargetIndex??c.targetIndex,c.pocketIndex??null,c.development?'development':c.doubleShot?'double':c.plant?'plant':'direct'].join(':');
  function diverse(items) { return roundRobin(roundRobin(items,routeKey),c=>c.targetIndex); }
  function softContacts(state) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue)return [];
    return targets(state).filter(t=>clear(state,cue,t,radius(cue),[cue.i,t.i])).sort((a,b)=>distance(cue,a)-distance(cue,b)).slice(0,2).map(t=>({
      kind:'safety',targetIndex:t.i,...nomination(state,t.i),softContact:true,label:'物理校准轻贴',
      shot:{direction:unit(cue,t),power:.14,vertical:0,side:0,elevation:0}}));
  }
  function generate(state) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue)return [];
    const on=targets(state),direct=attackRoutes(state,cue,on),doubles=doubleRoutes(state,cue,on).slice(0,4);
    const doubleExpanded=doubles.flatMap(r=>(r.aimVariants?.length?r.aimVariants:[{direction:r.direction,travel:r.travel}]).map(v=>({...r,direction:v.direction,travel:v.travel,aimVariants:undefined})));
    const groups={attack:direct.concat(doubleExpanded),safety:[],escape:[]};
    for(const target of on){
      const d=unit(cue,target);if(!d)continue;
      if(clear(state,cue,target,radius(cue),[cue.i,target.i])){
        groups.escape.push({kind:'escape',targetIndex:target.i,priority:1/(.1+distance(cue,target)),label:'直接解球',direction:d});
      }
        for(const thin of [0,-.45,.45,-.8,.8,-.94,.94]){
          const aim={x:target.x-d.z*thin*(radius(cue)+radius(target)),z:target.z+d.x*thin*(radius(cue)+radius(target))};
          if(clear(state,cue,aim,radius(cue),[cue.i,target.i]))groups.safety.push({kind:'safety',targetIndex:target.i,priority:1/(.1+distance(cue,target)),label:thin?'薄球防守':'直接防守',direction:unit(cue,aim)});
        }
      groups.escape.push(...banks(state,cue,target));
    }
    // Rotate target balls before thickness variants; obstruction decides escape allocation.
    groups.attack=diverse(groups.attack);groups.safety=roundRobin(groups.safety,c=>c.targetIndex);
    const blocked=!groups.escape.some(c=>c.label==='直接解球');
    groups.escape=roundRobin(groups.escape,c=>c.targetIndex);
    if(!blocked)groups.escape=groups.escape.filter(c=>c.label!=='直接解球').slice(0,2);
    // Explore independent routes before parameter variants.
    const result=[],kinds=['attack','safety','escape'];
    const longest=Math.max(...kinds.map(k=>groups[k].length));
    for(let variant=0;variant<5&&result.length<96;variant++){
      for(let i=0;i<longest&&result.length<96;i++)for(const kind of kinds){
        const route=groups[kind][i];if(!route||result.length>=96)continue;
        const base=kind==='attack'?Math.max(.20,Math.min(.55,.20+.045*route.travel+.10*(1-route.cut))):kind==='safety'?.28:.48;
        const {direction,...meta}=route;
        const draw=kind==='attack'&&variant===1;
        const vertical=draw?-.35:[0,-.35,.3,-.5,.5][variant];
        result.push({...meta,...nomination(state,route.targetIndex),shot:{direction,power:Math.max(.08,Math.min(.85,draw?base*.9:base+[0,-.1,.1,.2,.04][variant])),side:0,vertical,elevation:vertical<0?.025*Math.PI:0}});
      }
    }
    return result;
  }
  function nomination(state,index) {
    if(state.rules?.ballOn!==252)return {};
    const explicit=state.rules?.nominatedColour;
    const target=(state.balls||[]).find(b=>b.i===index);
    // A free ball may stand for an explicitly nominated colour; never overwrite it.
    return {nominatedColour:explicit>=2&&explicit<=7?explicit:target?.n>=2&&target.n<=7?target.n:2};
  }
  function refine(state,candidate) {
    if(!candidate.shot)return [];
    const boundary=candidate.executionBoundary,repairPower=boundary?.repairPower;
    if(candidate.kind!=='attack')return Number.isFinite(repairPower)?[{...candidate,parentCandidateId:candidate.id,label:'到球力度修正',
      executionRepair:{...boundary,referenceReachedPower:boundary.reachedPower},shot:{...candidate.shot,power:repairPower}}]:[];
    // Compare adequate speed with stun, a modest draw and a deeper draw before
    // reducing speed for position. Native outcomes decide which spin is useful.
    const minimumDelta=Number.isFinite(repairPower)?Math.max(0,repairPower-candidate.shot.power):0,seen=new Set();
    return [[Math.max(.06,minimumDelta),0],[Math.max(.10,minimumDelta),-.2],[Math.max(.12,minimumDelta),-.5],
      [-.06,0],[.06,0],[-.03,-.5],[.04,-.5],[-.03,.5],[.04,.5]].flatMap(([delta,vertical],index)=>{
      const power=Math.max(.08,Math.min(.85,candidate.shot.power+delta)),signature=[power,vertical].join(':');
      if(seen.has(signature))return [];seen.add(signature);
      return [{...candidate,...nomination(state,candidate.targetIndex),parentCandidateId:candidate.id,label:'进攻走位微调',
        executionRepair:index<3&&boundary?{...boundary,referenceReachedPower:boundary.reachedPower}:undefined,
        shot:{...candidate.shot,power,side:0,vertical,elevation:vertical<0?.025*Math.PI:0}}];
    });
  }
  function multiBanks(state,cue,on) {
    const b=state.bounds;if(!b)return [];
    const r=radius(cue),walls=[['x',b.minX+r],['x',b.maxX-r],['z',b.minZ+r],['z',b.maxZ-r]],routes=[];
    function trace(target,sequence) {
      const mirror={x:target.x,z:target.z};
      for(const index of sequence.slice().reverse()){const [axis,value]=walls[index];mirror[axis]=2*value-mirror[axis];}
      const direction=unit(cue,mirror);if(!direction)return;
      let point=cue,ray={...direction},travel=0;
      for(const index of sequence){
        const [axis,value]=walls[index],other=axis==='x'?'z':'x';
        const t=(value-point[axis])/ray[axis];if(!Number.isFinite(t)||t<=1e-6)return;
        const contact={x:point.x+t*ray.x,z:point.z+t*ray.z};
        const lo=other==='x'?b.minX+r:b.minZ+r,hi=other==='x'?b.maxX-r:b.maxZ-r;
        if(contact[other]<=lo+1e-5||contact[other]>=hi-1e-5||!clear(state,point,contact,r,[cue.i]))return;
        travel+=t;point=contact;ray[axis]*=-1;
      }
      if(!clear(state,point,target,r,[cue.i,target.i]))return;
      travel+=distance(point,target);
      routes.push({kind:'escape',targetIndex:target.i,label:sequence.length===2?'两库解球':'三库解球',direction,travel,priority:1/(.1+travel)});
    }
    for(const depth of [2,3]){
      function enumerate(sequence){
        if(sequence.length===depth){for(const target of on)trace(target,sequence);return;}
        for(let w=0;w<4;w++)if(w!==sequence[sequence.length-1])enumerate([...sequence,w]);
      }
      enumerate([]);if(routes.length)break;
    }
    return routes.sort((a,b)=>b.priority-a.priority).slice(0,32);
  }
  function generateRecovery(state,options={}) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue)return [];
    const routes=options.multiCushion?multiBanks(state,cue,targets(state)):[];
    for(const target of options.multiCushion?[]:targets(state)){
      const d=unit(cue,target);if(!d)continue;
      for(const thin of [0,-.92,.92]){
        const aim={x:target.x-d.z*thin*(radius(cue)+radius(target)),z:target.z+d.x*thin*(radius(cue)+radius(target))};
        if(clear(state,cue,aim,radius(cue),[cue.i,target.i]))routes.push({kind:'escape',targetIndex:target.i,label:thin?'薄球解球微调':'直接解球微调',direction:unit(cue,aim)});
      }
      routes.push(...banks(state,cue,target));
    }
    const result=[],seen=new Set();
    const variants=options.multiCushion?[.67,.85,.39].flatMap(power=>routes.map(route=>({route,power}))):routes.flatMap(route=>[.19,.39,.67].map(power=>({route,power})));
    for(const offset of [0,-.003,.003])for(const {route,power} of variants){
      if(result.length>=96)return result;
      const a=Math.atan2(route.direction.z,route.direction.x)+offset;
      const key=[a.toFixed(5),power,route.targetIndex].join(':');if(seen.has(key))continue;seen.add(key);
      const {direction,...meta}=route;
      result.push({...meta,...nomination(state,route.targetIndex),shot:{direction:{x:Math.cos(a),z:Math.sin(a)},power,side:0,vertical:0,elevation:0}});
    }
    return result;
  }
  function opportunity(state,mask) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);
    if(!cue||!mask)return {chance:0,lanes:0};
    const routes=attackRoutes(state,cue,targets(state,mask,null));
    return {chance:routes.length?Math.max(...routes.map(r=>r.priority)):0,lanes:routes.length};
  }
  function evaluate(state,candidate,trialResult) {
    const adjudication=trialResult.adjudication;
    const scoreDelta=Number.isFinite(adjudication.score)?adjudication.score:0;
    const next={...state,balls:trialResult.nextBalls||[],rules:{ballOn:adjudication.nextBallOn}};
    const cue=next.balls.find(b=>active(b)&&b.n===0),on=targets(next,adjudication.nextBallOn,null);
    const scale=state.bounds?Math.hypot(state.bounds.maxX-state.bounds.minX,state.bounds.maxZ-state.bounds.minZ):1;
    const separation=cue&&on.length?Math.min(...on.map(b=>distance(cue,b)))/Math.max(scale,1e-9):0;
    const incoming=opportunity(next,adjudication.nextBallOn);
    const root=state.rootPlayerIndex??state.rules?.playerIndex??0,actor=state.rules?.playerIndex??0;
    const nextActor=trialResult.nextContext?.playerIndex??trialResult.nextSnapshot?.rules?.playerIndex??(adjudication.continueBreak?actor:1-actor);
    const stays=nextActor===root;
    const features={scoreDelta,cueSafety:separation,targetSeparation:separation,
      opponentChance:stays?0:incoming.chance,nextChance:stays?incoming.chance:0,
      laneAvailability:incoming.lanes};
    const netPoints=scoreDelta*(actor===root?1:-1),futureValue=Math.min(7,incoming.chance*3)*(stays?1:-1);
    Object.assign(features,{netPoints,futureValue,nextPlayerIndex:nextActor});
    return {score:netPoints+futureValue,netPoints,futureValue,terminalValue:0,features};
  }
  function positionSectors(state,target,limit=4,ignoredIds=[]) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue||!target)return [];
    const out=[],b=state.bounds;
    for(let p=0;p<(state.pockets||[]).length;p++){
      const pocket=state.pockets[p],toward=unit(target,pocket);if(!toward||!pocketAccepts(target,pocket)||!clear(state,target,pocket,radius(target),[cue.i,target.i,...ignoredIds]))continue;
      for(const offset of [0,-.35,.35])for(const length of [.24,.42]){
        const angle=Math.atan2(-toward.z,-toward.x)+offset,axis={x:Math.cos(angle),z:Math.sin(angle)};
        const centre={x:target.x+axis.x*length,z:target.z+axis.z*length};
        if(b&&(centre.x<b.minX+radius(cue)||centre.x>b.maxX-radius(cue)||centre.z<b.minZ+radius(cue)||centre.z>b.maxZ-radius(cue)))continue;
        const ghost={x:target.x+axis.x*(radius(cue)+radius(target)),z:target.z+axis.z*(radius(cue)+radius(target))};
        if(!clear(state,centre,ghost,radius(cue),[cue.i,target.i,...ignoredIds]))continue;
        out.push({id:`sector-${target.i}-${p}-${length}-${offset}`,targetId:target.i,pocketIndex:p,origin:{x:target.x,z:target.z},axis,centre,distance:length,minDistance:Math.max(.09,length-.12),maxDistance:length+.12,angleTolerance:.15,arrivalTolerance:.75,priority:1/(.2+distance(target,pocket)+length+Math.abs(offset)*.15)});
      }
    }
    return out.sort((a,b)=>b.priority-a.priority).slice(0,limit);
  }
  function sectorCheck(cue,sector,trace) {
    if(!cue||!sector)return {met:false,distance:null,angle:null,arrivalAligned:false};
    const dx=cue.x-sector.origin.x,dz=cue.z-sector.origin.z,length=Math.hypot(dx,dz);
    const angle=length>1e-9?Math.acos(Math.max(-1,Math.min(1,(dx*sector.axis.x+dz*sector.axis.z)/length))):Math.PI;
    let arrivalAngle=null;
    if(Array.isArray(trace))for(let j=trace.length-2;j>=0;j--){const a=trace[j];if(!Number.isFinite(a.x)||!Number.isFinite(a.z))continue;const d=Math.hypot(cue.x-a.x,cue.z-a.z);if(d<.015)continue;
      arrivalAngle=Math.acos(Math.max(-1,Math.min(1,Math.abs(((cue.x-a.x)*sector.axis.x+(cue.z-a.z)*sector.axis.z)/d))));break;}
    const inSector=length>=sector.minDistance&&length<=sector.maxDistance&&angle<=sector.angleTolerance;
    const arrivalAligned=arrivalAngle!==null&&arrivalAngle<=sector.arrivalTolerance;
    return {met:inSector,inSector,distance:length,angle,arrivalAngle,arrivalAligned};
  }
  function transitionGraph(state,limit=12) {
    const balls=(state.balls||[]).filter(active),cue=balls.find(b=>b.n===0),allReds=balls.filter(b=>b.n===1),colours=balls.filter(b=>b.n>=2),edges=[];
    const open=cue?attackRoutes(state,cue,allReds):[],openIds=new Set(open.map(r=>r.targetIndex));
    const pocketableReds=allReds.filter(b=>(state.pockets||[]).some(p=>pocketAccepts(b,p)&&clear(state,b,p,radius(b),[cue?.i,b.i]))||openIds.has(b.i))
      .sort((a,b)=>Number(openIds.has(b.i))-Number(openIds.has(a.i))||
        Math.min(...(state.pockets||[{x:0,z:0}]).map(p=>distance(a,p)))-Math.min(...(state.pockets||[{x:0,z:0}]).map(p=>distance(b,p))));
    const toReds=(pocketableReds.length?pocketableReds:allReds).slice(0,6);
    const fromReds=state.rules?.ballOn===2&&openIds.size?allReds.filter(b=>openIds.has(b.i)).slice(0,5):toReds;
    const poolReds=[...new Map([...fromReds,...toReds].map(b=>[b.i,b])).values()];
    const sectorTargets=[...poolReds,...colours],ignoredIds=sectorTargets.map(b=>b.i);
    const sectorsById=new Map(sectorTargets.map(b=>[b.i,positionSectors(state,b,24,ignoredIds)]));
    // All sectors aimed at one pocket share this geometry; keep caches private to this call.
    const pocketGeometry=new Map();
    for(const from of [...fromReds,...colours])for(const to of from.n===1?colours:toReds){
      const sectors=sectorsById.get(to.i);if(!sectors?.length)continue;
      let byPocket=pocketGeometry.get(to);if(!byPocket){byPocket=new Map();pocketGeometry.set(to,byPocket);}
      const pocketClear=new Map(),excluded=[cue.i,to.i,from.i];
      for(const sector of sectors){
        const p=sector.pocketIndex;let path=byPocket.get(p);
        if(!path){const pocket=state.pockets[p],toward=unit(to,pocket);
          path={pocket,ghost:{x:to.x-toward.x*(radius(cue)+radius(to)),z:to.z-toward.z*(radius(cue)+radius(to))}};byPocket.set(p,path);}
        const {pocket,ghost}=path;
        let laneClear=pocketClear.get(p);
        if(laneClear===undefined){laneClear=clear(state,to,pocket,radius(to),excluded);pocketClear.set(p,laneClear);}
        if(!laneClear||!clear(state,sector.centre,ghost,radius(cue),excluded))continue;
        const travel=distance(from,sector.centre);edges.push({fromId:from.i,toId:to.i,sectorId:sector.id,sector,priority:sector.priority/(.2+travel)});}}
    const ranked=edges.sort((a,b)=>b.priority-a.priority),out=[];
    for(const from of [...fromReds,...colours])out.push(...ranked.filter(e=>e.fromId===from.i).slice(0,2));
    for(const edge of out.filter(e=>fromReds.some(b=>b.i===e.fromId))){const successor=out.find(e=>e.fromId===edge.toId&&e.toId!==edge.fromId);edge.successor=successor?{fromId:successor.fromId,toId:successor.toId,sectorId:successor.sectorId}:null;}
    return out.sort((a,b)=>b.priority-a.priority).slice(0,limit);
  }
  function shadowZones(state,on=targets(state)) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0),out=[],bounds=state.bounds;if(!cue)return out;
    for(const blocker of (state.balls||[]).filter(b=>active(b)&&b.n>0&&!on.some(t=>t.i===b.i)))for(const target of on){
      const axis=unit(target,blocker);if(!axis)continue;
      let visibleTarget=null;
      for(const length of [.10,.22,.36]){const centre={x:blocker.x+axis.x*length,z:blocker.z+axis.z*length};
        if(bounds&&(centre.x<bounds.minX+radius(cue)||centre.x>bounds.maxX-radius(cue)||centre.z<bounds.minZ+radius(cue)||centre.z>bounds.maxZ-radius(cue)))continue;
        const shadowCue={...cue,...centre};
        let hidden=true;
        if(visibleTarget&&edgeVisibility(state,shadowCue,visibleTarget,true)!==0)hidden=false;
        else for(const t of on){if(t===visibleTarget)continue;if(edgeVisibility(state,shadowCue,t,true)!==0){visibleTarget=t;hidden=false;break;}}
        if(hidden){out.push({id:`shadow-${blocker.i}-${target.i}-${length}`,hideBehindBallId:blocker.i,centre,radius:.045});if(out.length===12)return out;}}}
    return out;
  }
  function edgeVisibility(state,cue,target,stopAtFirst) {
    const length=distance(cue,target);if(!(length>1e-9))return 0;
    const cueRadius=radius(cue),r=cueRadius+radius(target),excluded=[cue.i,target.i];
    if(length<=r)return clear(state,cue,target,cueRadius,excluded)?2:0;
    const tangent=Math.asin(Math.min(1,r/length)),angle=Math.atan2((target.z-cue.z)/length,(target.x-cue.x)/length),travel=Math.sqrt(length*length-r*r);
    let visible=0;
    for(let sign=-1;sign<=1;sign+=2){const a=angle+sign*tangent,contact={x:cue.x+Math.cos(a)*travel,z:cue.z+Math.sin(a)*travel};if(clear(state,cue,contact,cueRadius,excluded)){visible++;if(stopAtFirst)return visible;}}
    return visible;
  }
  function visibleEdges(state,cue,target) { return edgeVisibility(state,cue,target,false); }

  return {generate,generateRecovery,refine,roundRobin,routeKey,diverse,softContacts,targets,plantRoutes,doubleRoutes,attackRoutes,opportunity,clear,evaluate,positionSectors,transitionGraph,sectorCheck,shadowZones,visibleEdges};
})();
if(typeof module!=='undefined'&&module.exports)module.exports=PCOLSearchGeometry;


/* Bounded geometric proxies, not calibrated pot probabilities or opponent trials. */
const PCOLTacticalPolicy = (() => {
  const core=typeof PCOLCore!=='undefined'?PCOLCore:typeof require==='function'?require('./rules-core'):null;
  const skill=()=>typeof PCOLShotSkill!=='undefined'?PCOLShotSkill:require('./shot-skill');
  const active=b=>b.active!==false;
  const dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);
  const clamp=n=>Math.max(0,Math.min(1,n));
  function analyze(state) {
    const scores=state.scores||state.rules?.scores||[0,0],actor=state.rootPlayerIndex??state.rules?.playerIndex??0;
    const deficit=(scores[1-actor]||0)-(scores[actor]||0);
    const remaining=Number.isFinite(state.remainingPoints)?state.remainingPoints:null;
    const liveReds=(state.balls||[]).filter(b=>active(b)&&b.n===1).length;
    const snookersInHand=remaining!==null&&-deficit>remaining;
    const shallowNeedSnookers=remaining!==null&&deficit>remaining&&(deficit-remaining)<=12&&liveReds>=3;
    return {objective:remaining!==null&&deficit>remaining?'need-snookers':deficit<0&&remaining!==null&&-deficit>remaining*.55?'contain':'build',
      style:'unified',deficit,remainingPoints:remaining,
      snookersInHand,shallowNeedSnookers};
  }
  function routeQuality(route,scale) {
    return clamp((route.cut||.15)**1.5/(1+2*(route.travel||0)/scale));
  }
  function aggregate(state,values) {
    const context=analyze(state),mean=values.reduce((a,b)=>a+b,0)/values.length;
    const downside=Math.max(0,mean-Math.min(...values));
    const lead=-(context.deficit||0),remaining=Math.max(1,context.remainingPoints||1);
    const riskPreference=.12+.18*clamp(lead/remaining);
    return {score:mean-riskPreference*downside,mean,downside,riskPreference};
  }
  function layout(state,geometry) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0),on=geometry.targets(state,state.rules?.ballOn,null);
    const b=state.bounds,scale=b?Math.hypot(b.maxX-b.minX,b.maxZ-b.minZ):2;
    if(!cue)return {best:0,lanes:0,edgeVisibility:0,rail:1,access:0,buried:1,mobility:0};
    const routes=geometry.attackRoutes(state,cue,on).map(r=>{
      const potId=r.potTargetIndex??r.targetIndex;
      const target=on.find(b=>b.i===potId)||on.find(b=>b.i===r.targetIndex),nominee=state.rules?.freeBallNominee===r.targetIndex;
      const mask=state.rules?.ballOn||0,nominated=state.rules?.nominatedColour;
      const points=nominee?(mask===2?1:mask===252?(nominated||target?.n||2):Math.max(0,...[2,3,4,5,6,7].filter(n=>mask&(1<<n)))):target?.n||0;
      let quality=routeQuality(r,scale);
      const level=state.rules?.playerIndex===(state.rootPlayerIndex??state.rules?.playerIndex)?state.skill:state.opponentSkill;
      const pocket=state.pockets?.[r.pocketIndex];
      if(level&&target&&pocket?.r&&r.direction&&!r.plant&&!r.doubleShot){
        const shot={direction:r.direction,power:.3,vertical:0};
        const uncertainty=skill().describe(state,{...r,shot},level);
        const tolerance=Math.atan2(Math.max(0,pocket.r-(target.r||.026))*(r.cut||.15),Math.max(.01,r.travel||dist(cue,target)+dist(target,pocket)));
        quality*=clamp(tolerance/(Math.sqrt(3)*uncertainty.angleSigma));
      }
      return {...r,quality,pointValue:quality*points};
    }).sort((a,b)=>b.pointValue-a.pointValue);
    const best=routes[0],alternative=routes.find(r=>r.targetIndex!==best?.targetIndex);
    const third=routes.find(r=>r.targetIndex!==best?.targetIndex&&r.targetIndex!==alternative?.targetIndex);
    const mobility=clamp((best?.quality||0)+.45*(alternative?.quality||0)+.2*(third?.quality||0));
    let visible=0,total=0;
    for(const target of on){
      const d=dist(cue,target);if(!d)continue;
      const dx=(target.x-cue.x)/d,dz=(target.z-cue.z)/d,offset=(cue.r||.026)+(target.r||.026);
      for(const edge of [-.8,0,.8]){
        total++;
        if(geometry.clear(state,cue,{x:target.x-dz*offset*edge,z:target.z+dx*offset*edge},cue.r||.026,[cue.i,target.i]))visible++;
      }
    }
    const rail=b?clamp(1-Math.min(cue.x-b.minX,b.maxX-cue.x,cue.z-b.minZ,b.maxZ-cue.z)/(.12*scale)):0;
    const neighbours=(state.balls||[]).filter(ball=>active(ball)&&ball.n>0&&dist(cue,ball)<.13).length;
    // Accessibility counts target/pocket lanes independently of the cue path.
    let accessible=0;
    for(const target of on)if((state.pockets||[]).some(p=>geometry.clear(state,target,p,target.r||.026,[cue.i,target.i])))accessible++;
    const effectiveMask=state.rules?.ballOn===252&&state.rules?.nominatedColour?1<<state.rules.nominatedColour:state.rules?.ballOn;
    const snooker=geometry.visibleEdges?null:core?.isSnookered(state.balls||[],effectiveMask,undefined,{inHand:!!state.rules?.inHand});
    const direct=core?.hasDirectHit(state.balls||[],effectiveMask,undefined,{inHand:!!state.rules?.inHand});
    return {best:best?.quality||0,pointValue:best?.pointValue||0,bestQuality:Math.max(0,...routes.map(r=>r.quality)),
      snookered:geometry.visibleEdges?on.length>0&&on.every(target=>geometry.visibleEdges(state,cue,target)===0):snooker?.snookered??null,hasDirectHit:direct?.hasDirectHit??null,
      bestTargetIndex:best?.targetIndex??null,alternative:alternative?.quality||0,
      alternativeTargets:Math.max(0,new Set(routes.map(r=>r.targetIndex)).size-1),targets:on.length,mobility,
      lanes:routes.length,edgeVisibility:total?visible/total:0,
      rail,access:on.length?accessible/on.length:0,buried:clamp(neighbours/3)};
  }
  function accessibleReds(state,ids,geometry) {
    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);
    return new Set((state.balls||[]).filter(b=>active(b)&&b.n===1&&ids.has(b.i)&&
      (state.pockets||[]).some(p=>geometry.clear(state,b,p,b.r||.026,[cue?.i,b.i]))).map(b=>b.i));
  }
  function blockerResources(state) {
    const live=(state.balls||[]).filter(b=>active(b)&&b.n>0),on=core?.ballOnNumbers(state.rules?.ballOn||0)||[];
    return live.filter(b=>!on.includes(b.n)).length;
  }
  function classify(state,candidate,result,geometry,prepared) {
    const verdict=result.adjudication||{};
    if(verdict.foulCode)return 'escape';
    if(verdict.score>0)return 'attack';
    const rules={...state.rules,...result.nextSnapshot?.rules,...result.nextContext};
    rules.ballOn=result.nextContext?.ballOn??result.nextSnapshot?.rules?.ballOn??verdict.nextBallOn??state.rules?.ballOn;
    const next={...state,balls:result.nextBalls||state.balls,rules};
    const before=prepared?(prepared.root.before??=(prepared.root.layout?prepared.root.layout(state):layout(state,geometry))):layout(state,geometry);
    // Classification retains declarations; evaluation clears them for the next turn.
    const sameNext=prepared&&next.balls===prepared.next.balls&&
      Object.keys(rules).every(k=>rules[k]===prepared.next.rules[k])&&
      Object.keys(prepared.next.rules).every(k=>rules[k]===prepared.next.rules[k]);
    const after=sameNext?prepared.after:prepared?.root.layout?prepared.root.layout(next):layout(next,geometry);
    if(before.hasDirectHit===false&&after.hasDirectHit!==false)return 'escape';
    if(after.snookered===true)return 'snooker';
    if(after.bestQuality<.2&&after.pointValue<1)return 'contain';
    return 'exposure';
  }
  function prepareRoot(state,geometry) {
    const redIds=new Set((state.balls||[]).filter(b=>active(b)&&b.n===1).map(b=>b.i));
    return {context:analyze(state),redIds,oldAccess:accessibleReds(state,redIds,geometry),
      scale:state.bounds?Math.hypot(state.bounds.maxX-state.bounds.minX,state.bounds.maxZ-state.bounds.minZ):2,
      blockersBefore:blockerResources(state),shadowBefore:geometry.shadowZones?geometry.shadowZones(state).length:0};
  }
  // A session belongs to one bounded search. Ordinary evaluate calls still accept mutable inputs.
  function createSession(geometry) {
    const roots=new WeakMap(),layouts=new WeakMap();
    // Both unset declaration forms are geometric equivalents; an actual nomination is distinct.
    const sameRules=(a={},b={})=>[...new Set([...Object.keys(a),...Object.keys(b)])].every(k=>
      a[k]===b[k]||['nominatedColour','freeBallNominee'].includes(k)&&a[k]==null&&b[k]==null);
    function cachedLayout(state) {
      const balls=state.balls;
      if(!balls||typeof balls!=='object')return layout(state,geometry);
      let entries=layouts.get(balls);
      const cached=entries?.find(e=>e.bounds===state.bounds&&e.pockets===state.pockets&&e.skill===state.skill&&e.opponentSkill===state.opponentSkill&&e.rootPlayerIndex===state.rootPlayerIndex&&sameRules(e.rules,state.rules));
      if(cached)return cached.value;
      const value=layout(state,geometry);
      if(!entries){entries=[];layouts.set(balls,entries);}
      entries.push({bounds:state.bounds,pockets:state.pockets,rules:state.rules,skill:state.skill,opponentSkill:state.opponentSkill,rootPlayerIndex:state.rootPlayerIndex,value});
      return value;
    }
    return {layout:cachedLayout,evaluate(state,candidate,result){
      let root=roots.get(state);
      if(!root){root={...prepareRoot(state,geometry),layout:cachedLayout,results:new WeakMap()};roots.set(state,root);}
      return evaluate(state,candidate,result,geometry,root);
    }};
  }
  function createEvaluator(state,geometry) {
    const session=createSession(geometry);
    return (candidate,result)=>session.evaluate(state,candidate,result);
  }
  function evaluate(state,candidate,result,geometry,preparedRoot) {
    const verdict=result.adjudication||{},points=Number.isFinite(verdict.score)?verdict.score:0;
    const root=state.rootPlayerIndex??state.rules?.playerIndex??0,actor=state.rules?.playerIndex??0;
    const nextRules={...state.rules,...result.nextSnapshot?.rules,...result.nextContext};
    nextRules.ballOn=result.nextContext?.ballOn??result.nextSnapshot?.rules?.ballOn??verdict.nextBallOn;
    nextRules.playerIndex=result.nextContext?.playerIndex??result.nextSnapshot?.rules?.playerIndex??(verdict.continueBreak?actor:1-actor);
    const stays=nextRules.playerIndex===root;
    const next={...state,balls:result.nextBalls||[],rules:{...nextRules,nominatedColour:null,freeBallNominee:null}};
    const rootData=preparedRoot||prepareRoot(state,geometry),facts=rootData.results?.get(result)||{};
    if(rootData.results)rootData.results.set(result,facts);
    const after=facts.after??=(rootData.layout?rootData.layout(next):layout(next,geometry));
    const {context,redIds,oldAccess,scale,blockersBefore,shadowBefore}=rootData;
    const newAccess=facts.newAccess??=accessibleReds(next,redIds,geometry);
    const freedRedIds=[...newAccess].filter(i=>!oldAccess.has(i));
    // Fixed original-red denominator: a pot or red/colour phase change cannot inflate development.
    const development=(redIds.size?freedRedIds.length/redIds.size:0)*(1-after.buried)*(1-after.rail);
    const effect=facts.effect??=classify(state,candidate,result,geometry,{root:rootData,next,after,newAccess});
    const difficulty=effect==='attack'?1-routeQuality(candidate,scale):0;
    const features={scoreDelta:points,objective:context.objective,style:context.style,routeDifficulty:difficulty,
      nextChance:stays?after.best:0,nextTargetIndex:stays?after.bestTargetIndex:null,
      alternativeLanes:stays?after.alternative||0:0,alternativeTargets:stays?after.alternativeTargets||0:0,
      opponentChance:stays?0:after.best,opponentTargetIndex:stays?null:after.bestTargetIndex,
      visibleTargetEdges:after.edgeVisibility,cueRailRestriction:after.rail,cueBuried:after.buried,
      clusterAccessibility:redIds.size?newAccess.size/redIds.size:0,freedRedIds,
      development,laneAvailability:after.lanes};
    const netPoints=points*(actor===root?1:-1);
    // All values use points. Route quality is a bounded proxy for short-horizon value.
    const leaf=(after.pointValue||0)+.6*(after.alternative||0)+.25*Math.min(2,after.alternativeTargets||0);
    let futureValue=stays?leaf:-leaf;
    const baseScores=state.scores||state.rules?.scores||[0,0];
    const derivedScores=baseScores.map((score,index)=>score+(points>0&&index===actor?points:points<0&&index!==actor?-points:0));
    const scores=result.nextContext?.scores||result.nextSnapshot?.rules?.scores||derivedScores;
    const early=!verdict.foulCode&&core?.earlyFrameOutcome({balls:next.balls,ballOn:next.rules.ballOn,scores,playerIndex:nextRules.playerIndex,
      actor,continueBreak:!!verdict.continueBreak,freeBall:!!nextRules.freeBallAvailable,freeBallReview:!!nextRules.freeBallReview});
    const terminal=verdict.frameOutcome==='end'||nextRules.ballOn===0||!!early;
    const margin=(scores[root]||0)-(scores[1-root]||0);
    const remaining=core?.remainingPoints(next.balls,next.rules.ballOn);
    const removed=Number.isFinite(state.remainingPoints)&&Number.isFinite(remaining)?Math.max(0,state.remainingPoints-remaining):0;
    const blockersAfter=blockerResources(next);
    const blockerDelta=blockersAfter-blockersBefore;
    const live=(next.balls||[]).filter(b=>active(b)&&b.n>0);
    const liveRedsAfter=live.filter(b=>b.n===1).length;
    const mathematicallyDead=margin< -7&&live.length===1&&live[0].n===7;
    const cue=next.balls.find(b=>active(b)&&b.n===0),bounds=next.bounds;
    const cueBaulk=bounds&&cue?clamp(1-(cue.x-bounds.minX)/(bounds.maxX-bounds.minX)):0;
    const displaced=facts.displaced??=(next.balls||[]).filter(b=>active(b)&&b.n>0&&state.balls.some(old=>old.i===b.i&&dist(old,b)>.02));
    const objectBallLeak=facts.objectBallLeak??=(()=>{
      const legalIds=new Set(geometry.targets(next,next.rules.ballOn,null).map(b=>b.i));
      const displacedLegal=displaced.filter(b=>legalIds.has(b.i));
      const leakRoutes=!stays&&cue?geometry.attackRoutes(next,cue,displacedLegal):[];
      return stays?0:leakRoutes.reduce((best,route)=>{
        const target=displacedLegal.find(b=>b.i===route.targetIndex);
        const proximity=target?Math.max(0,...(next.pockets||[]).map(p=>clamp(1-dist(target,p)/(.18*scale)))):0;
        return Math.max(best,routeQuality(route,scale)*(1+proximity));
      },0);
    })();
    const stillNeedsSnookers=Number.isFinite(remaining)&&-margin>remaining;
    const snookerGap=Number.isFinite(remaining)?Math.max(0,-margin-remaining):0;
    const shallowComeback=stillNeedsSnookers&&liveRedsAfter>=2&&snookerGap<=12&&(points>=5||(points===1&&stays&&after.best>=.25));
    const clinchAfter=Number.isFinite(remaining)&&margin>remaining;
    const clinchBonus=!verdict.foulCode&&clinchAfter&&netPoints>0?(context.snookersInHand?1.5:3.5):0;
    const recoveryCost=context.objective==='need-snookers'&&margin<0&&!shallowComeback?Math.max(0,removed-Math.max(0,netPoints)):0;
    const shadowAfter=facts.shadowAfter??=(geometry.shadowZones?geometry.shadowZones(next).length:0);
    const shadowDelta=clamp(shadowAfter/6)-clamp(shadowBefore/6);
    const lostObjects=(state.balls||[]).filter(b=>active(b)&&b.n>0&&!live.some(n=>n.i===b.i)).length;
    const resourceValue=stillNeedsSnookers&&!shallowComeback?(2*blockerDelta-4*lostObjects+6*shadowDelta)+(!stays&&after.snookered?6:0):
      stillNeedsSnookers&&!stays&&after.snookered?6:0;
    const scoringDiscount=stillNeedsSnookers&&netPoints>0?(shallowComeback?-.15*netPoints:-.85*netPoints):0;
    if(stillNeedsSnookers&&futureValue>0)futureValue*=shallowComeback?.75:.15;
    const incomingSign=nextRules.playerIndex===root?1:-1;
    const effectiveLeak=clinchAfter?objectBallLeak*.2:objectBallLeak;
    const defensiveValue=verdict.continueBreak?0:-incomingSign*((cueBaulk+after.rail)*(1-Math.min(1,effectiveLeak))-3*effectiveLeak);
    const openingBonus=candidate?.opening&&!verdict.foulCode&&!stays&&bounds&&cue?
      (cueBaulk>=.68?2.5*cueBaulk*(1-Math.min(1,after.best*2)):-5*Math.max(0,.6-cueBaulk)):0;
    const safeMiss=!verdict.foulCode&&points===0&&!stays&&after.best<.22&&objectBallLeak<.25&&(cueBaulk>=.55||after.rail>=.5||after.snookered===true);
    const costlyMiss=!verdict.foulCode&&points===0&&!stays&&(after.best>=.35||objectBallLeak>=.35);
    const twoWayPotential=!verdict.foulCode&&points>0&&stays&&(cueBaulk>=.58||after.rail>=.55);
    const immediateCost=-recoveryCost+resourceValue+defensiveValue+scoringDiscount+clinchBonus+openingBonus;
    const terminalValue=terminal?(margin>0?100000:margin<0?-100000:0):0;
    if(terminal)futureValue=0;
    Object.assign(features,{netPoints,immediateCost,futureValue,terminalValue,nextPlayerIndex:nextRules.playerIndex,routeQualityProxy:1-difficulty,
      snookered:after.snookered,opponentSnookered:!stays&&after.snookered===true,selfSnookered:stays&&after.snookered===true,
      hasDirectHit:after.hasDirectHit,remainingPoints:remaining,recoveryCost,effect,blockersBefore,blockersAfter,blockerDelta,resourceValue,stillNeedsSnookers,shallowComeback,clinchAfter,scoringDiscount,shadowBefore,shadowAfter,shadowDelta,lostObjects,earlyFrameReason:early?.reason||null,
      cueBaulk,objectBallLeak,mobility:stays?after.mobility||0:0,safeMiss,costlyMiss,twoWayPotential,displacedObjectBallIds:displaced.map(b=>b.i),mathematicallyDead});
    return {score:netPoints+immediateCost+futureValue+terminalValue,netPoints,immediateCost,futureValue,terminalValue,features};
  }
  function estimate(state,geometry) {
    const after=layout(state,geometry);
    return {value:after.pointValue||0,layout:after};
  }
  // Optional concession reuses the finished local search; it never runs another trial.
  // Poor bounded observations support a practical choice, never a claim of impossibility.
  function concession(state,decision,geometry) {
    const rules=state.rules||{},actor=rules.playerIndex,scores=state.scores||rules.scores;
    const evidence={policy:'position-and-local-evidence-v1',actor,
      interpretation:'execution observations, not calibrated win probabilities'};
    const finish=(action,reason)=>({action,reason,evidence});
    if(!core||!Array.isArray(state.balls)||!Array.isArray(scores)||scores.length!==2||!scores.every(Number.isFinite)||
      ![0,1].includes(actor)||!rules.ballOn||rules.ballOn===65535)
      return finish('continue','incomplete-position');
    if(state.pending||rules.freeBallReview||rules.freeBallAvailable&&!rules.freeBallDeclined&&rules.freeBallNominee==null)
      return finish('continue','unresolved-turn-options');
    const status=core.concessionStatus({balls:state.balls,ballOn:rules.ballOn,scores,playerIndex:actor,
      freeBall:!!rules.freeBallAvailable&&!rules.freeBallDeclined});
    Object.assign(evidence,{deficit:status.deficit,remaining:status.remaining,excess:status.excess,
      minimumFoulEvents:Math.ceil(Math.max(0,status.excess)/7)});
    if(!status.eligible)return finish('continue','not-beyond-table-points');
    const search=decision?.search||decision||{},selected=decision?.candidate||decision?.selected;
    const candidates=[...new Map([selected,...(decision?.shortlist||decision?.candidates||[])].filter(Boolean)
      .map(c=>[c.id||c,c])).values()];
    const categories=search.categoryBest||{};
    if(categories.snooker?.snookered===true||candidates.some(c=>c.evidence?.nominal?.legal===true&&
      (c.features?.opponentSnookered===true||(c.evidence.samples||[]).some(r=>r.legal&&r.nextActor!==actor&&r.opponentSnookered))))
      return finish('continue','verified-snooker-available');
    if(categories.contain?.points===0&&Number.isFinite(categories.contain.opponentChance)&&categories.contain.opponentChance<.2||
      candidates.some(c=>c.evidence?.nominal?.legal===true&&(c.features?.safeMiss===true||c.risk?.safeMissRate>0||
        c.evidence.nominal.nextActor!==actor&&c.features?.effect==='contain'&&c.features.opponentChance<.2)))
      return finish('continue','verified-safe-defense-available');
    if(candidates.some(c=>c.evidence?.nominal?.legal===true&&(c.features?.shallowComeback===true||
      c.features?.shadowAfter>c.features?.shadowBefore||c.features?.blockerDelta>0)))
      return finish('continue','recovery-resources-can-improve');
    if(!['complete','candidate-limit','budget-exhausted'].includes(search.status)||!geometry?.shadowZones)
      return finish('continue','incomplete-search-evidence');
    // Two distinct routes and their existing paired execution samples are a minimum
    // safeguard against conceding from one failed seed or an interrupted risk check.
    const routes=new Set(candidates.map(c=>geometry.routeKey?geometry.routeKey(c):[c.kind,c.targetIndex,c.pocketIndex].join(':')));
    const complete=c=>{
      const f=c.features,r=c.risk,rows=c.evidence?.samples,n=c.evidence?.nominal;
      return n?.legal===true&&f&&Number.isFinite(f.opponentChance)&&Number.isFinite(f.objectBallLeak)&&
        r?.coverage==='complete'&&r.samples>=2&&!r.incomplete&&Array.isArray(rows)&&rows.length===r.samples&&
        Number.isFinite(r.costlyMissRate)&&rows.every(row=>typeof row.legal==='boolean'&&Number.isFinite(row.points)&&
          [0,1].includes(row.nextActor)&&typeof row.opponentSnookered==='boolean');
    };
    if(routes.size<2||!candidates.every(complete))return finish('continue','incomplete-recovery-evidence');
    const shadows=geometry.shadowZones(state),usefulBlockers=new Set(shadows.map(s=>s.hideBehindBallId)).size;
    const liveReds=state.balls.filter(b=>active(b)&&b.n===1).length;
    Object.assign(evidence,{blockers:blockerResources(state),usefulBlockers,shadowZones:shadows.length,liveReds,
      routes:routes.size,candidates:candidates.map(c=>{
        const n=c.risk.samples,fouls=c.evidence.samples.filter(r=>!r.legal).length;
        return {id:c.id,samples:n,fouls,costlyMisses:Math.round(c.risk.costlyMissRate*n),
          opponentChanceProxy:c.features.opponentChance,mathematicallyDead:!!c.features.mathematicallyDead};
      })});
    // A blocker can be reused; these counts express scarce resources, not a limit
    // on how many fouls a position can ever produce. Several reds keep options open.
    const scarce=usefulBlockers===0||evidence.minimumFoulEvents>=2&&usefulBlockers===1&&shadows.length<=3;
    if(!scarce||liveReds>=3)return finish('continue','defensive-resources-remain');
    const poor=c=>{
      const f=c.features,n=c.evidence.nominal,observed=evidence.candidates.find(row=>row.id===c.id);
      const poorNominal=f.mathematicallyDead===true||f.costlyMiss===true||
        n.nextActor!==actor&&(f.opponentChance>=.35||f.objectBallLeak>=.35)||
        f.stillNeedsSnookers===true&&f.blockerDelta<0&&f.shadowAfter<=f.shadowBefore;
      const minimumBad=evidence.minimumFoulEvents>=2?Math.ceil(observed.samples/2):observed.samples;
      return poorNominal&&(f.mathematicallyDead===true||observed.fouls+observed.costlyMisses>=minimumBad);
    };
    return candidates.every(poor)?finish('concede','weak-tested-recovery-and-scarce-blockers'):
      finish('continue','recovery-evidence-not-poor-enough');
  }
  return {analyze,aggregate,evaluate,createEvaluator,createSession,layout,estimate,classify,concession};
})();

/* Local geometric intentions; native trials establish achievement. */
const PCOLTacticalBrain=(()=>{
 const live=b=>b.active!==false&&Number.isFinite(b.x)&&Number.isFinite(b.z),dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z),tasks=['position','build','contain','need-snookers','escape','develop'];
 function analyze(state,g){
  const balls=(state.balls||[]).filter(live),cue=balls.find(b=>b.n===0),on=g.targets(state),routes=cue?g.attackRoutes(state,cue,on):[],reds=balls.filter(b=>b.n===1);
  const graph=g.transitionGraph(state,24),sectors=[...new Map(graph.map(e=>[e.sector.id,e.sector])).values()];
  const clusters=reds.filter(b=>reds.some(c=>c.i!==b.i&&dist(b,c)<2.5*(b.r||.026))).map(b=>b.i);
  const pockets=state.pockets||[],hangingIds=reds.filter(b=>pockets.some(p=>dist(b,p)<=.22)).map(b=>b.i);
  const preserveIds=[...new Set(graph.map(e=>e.toId))].filter(i=>!clusters.includes(i)&&!hangingIds.includes(i)).slice(0,4);
  const actor=state.rules?.playerIndex||0,scores=state.scores||state.rules?.scores||[0,0],deficit=(scores[1-actor]||0)-(scores[actor]||0),remainingPoints=state.remainingPoints??reds.length*8+balls.filter(b=>b.n>=2).reduce((n,b)=>n+b.n,0);
  const hasGoodPot=routes.some(r=>(r.cut||0)>=.38);
  const shallowComeback=deficit>remainingPoints&&(deficit-remainingPoints)<=12&&reds.length>=3&&hasGoodPot;
  const directlyReachable=cue&&on.some(t=>g.clear(state,cue,t,cue.r||.026,[cue.i,t.i])||g.visibleEdges(state,cue,t)>0);
  const task=deficit>remainingPoints?(shallowComeback?'position':'need-snookers'):!routes.length?(directlyReachable?'contain':'escape'):-deficit>remainingPoints*.55&&!hasGoodPot?'contain':'position';
  const edge=graph.find(e=>routes.some(r=>r.targetIndex===e.fromId)),targetId=edge?.fromId??routes[0]?.targetIndex??on[0]?.i??null;
  const primary={task,targetId,nextBallId:edge?.toId??null,sectorId:edge?.sectorId??null,preserveIds:preserveIds.filter(i=>i!==targetId)};
  const fallback={task:deficit>remainingPoints?'need-snookers':routes.length||directlyReachable?'contain':'escape',targetId,nextBallId:null,sectorId:null,preserveIds:primary.preserveIds};
  return {task,allowedTasks:tasks.slice(),tasks:tasks.slice(),ballIds:balls.filter(b=>b.n>0).map(b=>b.i),targetIds:on.map(b=>b.i),sectors,transitionGraph:graph,defaultPrimary:primary,defaultFallback:fallback,primaryIntent:primary,fallbackIntent:fallback,preserveIds,problemOrder:clusters,roles:{problemIds:clusters,insuranceIds:preserveIds,keyColourIds:balls.filter(b=>b.n>=5).map(b=>b.i),transitionIds:graph.map(e=>e.toId),hangingIds},shadowZones:g.shadowZones(state,on),scoreboard:{scores,deficit,remainingPoints}};
 }
 function normalizePlan(raw,brief){
  raw=raw&&typeof raw==='object'?raw:{};
  const normalize=(input,base)=>{input=input&&typeof input==='object'?input:{};const targetId=brief.targetIds.includes(input.targetId)?input.targetId:base.targetId;
   const edge=brief.transitionGraph.find(e=>e.fromId===targetId&&e.toId===input.nextBallId&&(input.sectorId==null||e.sectorId===input.sectorId))||brief.transitionGraph.find(e=>e.fromId===targetId);
   const sector=brief.sectors.find(s=>s.id===input.sectorId&&s.targetId===(input.nextBallId??edge?.toId));
   return {task:tasks.includes(input.task)?input.task:base.task,targetId,nextBallId:sector?.targetId??edge?.toId??null,sectorId:sector?.id??edge?.sectorId??null,preserveIds:[...new Set((Array.isArray(input.preserveIds)?input.preserveIds:base.preserveIds||[]).filter(i=>brief.ballIds.includes(i)&&i!==targetId&&!(brief.roles?.hangingIds||[]).includes(i)))].slice(0,4),...(brief.ballIds.includes(input.hideBehindBallId)?{hideBehindBallId:input.hideBehindBallId}:{}),reason:typeof input.reason==='string'?input.reason.slice(0,180):undefined};};
  return {primaryIntent:normalize(raw.primaryIntent||raw,brief.defaultPrimary),fallbackIntent:normalize(raw.fallbackIntent,brief.defaultFallback),reason:typeof raw.reason==='string'?raw.reason.slice(0,180):'局部几何路线与下一杆走位'};
 }
 function directed(state,seeds,intent,g,brief=analyze(state,g)){
  const sector=brief.sectors.find(s=>s.id===intent.sectorId),shadow=brief.shadowZones.find(z=>intent.hideBehindBallId==null||z.hideBehindBallId===intent.hideBehindBallId),zone=['contain','need-snookers'].includes(intent.task)?shadow?.centre:sector?.centre;
  const attacking=['position','build','develop'].includes(intent.task),defensive=['contain','need-snookers'].includes(intent.task);
  const eligible=seeds.filter(c=>c.shot&&(intent.targetId==null||c.targetIndex===intent.targetId)&&(!attacking||c.kind==='attack')&&(!defensive||c.kind==='safety'));
  // Choose independent pot lanes before spending trials on spin; generator order interleaves safety and escape.
  const lanes=new Map();for(const c of eligible){const key=[c.targetIndex,c.pocketIndex,Math.atan2(c.shot.direction.z,c.shot.direction.x).toFixed(5)].join(':');if(!lanes.has(key))lanes.set(key,c);}
  const picked=[...lanes.values()].slice(0,defensive?7:4),out=[],groups=[];
  for(const c of picked){const target=state.balls.find(b=>b.i===c.targetIndex);if(!target)continue;
   const pocket=state.pockets[c.pocketIndex],length=pocket?dist(target,pocket):0,normal=length?{x:(pocket.x-target.x)/length,z:(pocket.z-target.z)/length}:c.shot.direction;
   const incoming=c.shot.direction,dot=incoming.x*normal.x+incoming.z*normal.z,tangent={x:incoming.x-dot*normal.x,z:incoming.z-dot*normal.z},want=zone?{x:zone.x-target.x,z:zone.z-target.z}:{x:0,z:0},wantLength=Math.hypot(want.x,want.z),along=want.x*normal.x+want.z*normal.z;
   const spin=Math.max(-.55,Math.min(.55,along/Math.max(.08,wantLength)*.55)),delta=zone?Math.min(.12,wantLength*.10):0,group=[];
   for(const [powerDelta,vertical] of [[0,0],[delta,spin],[delta+.06,spin*.65],[-.04,spin],[delta*.5,-spin*.5],[delta+.03,0]]){
    const outgoing={x:tangent.x+vertical*normal.x,z:tangent.z+vertical*normal.z},alignment=(outgoing.x*want.x+outgoing.z*want.z)/(Math.hypot(outgoing.x,outgoing.z)*wantLength||1);
    group.push({...c,directed:true,requiresTrace:true,intentTask:intent.task,destinationAlignment:alignment,label:'任务几何走位',shot:{...c.shot,power:Math.max(.08,Math.min(.85,c.shot.power+powerDelta)),vertical,side:0,elevation:vertical<0?.025*Math.PI:0}});}
   // Preserve a plain pot reference, then try the best predicted outgoing direction on each pocket.
   group.splice(1,group.length-1,...group.slice(1).sort((a,b)=>b.destinationAlignment-a.destinationAlignment));
   if(defensive){const originalVariant=eligible.find(s=>s.shot.power!==c.shot.power&&Math.abs(s.shot.direction.x-c.shot.direction.x)<1e-8&&Math.abs(s.shot.direction.z-c.shot.direction.z)<1e-8);
    if(originalVariant)group.unshift(originalVariant);}
   groups.push(group);
   if((c.kind==='escape'&&/库|cushion|bank/i.test(c.label||''))||c.contacts?.some(e=>e.kind==='cushion'))group.push(...[-.18,.18].map(side=>({...c,directed:true,requiresTrace:true,label:'库边适度侧旋走位',shot:{...c.shot,side,vertical:0,elevation:0}})));
  }
  for(let variant=0;variant<8;variant++)for(const group of groups)if(group[variant])out.push(group[variant]);
  if(zone&&['contain','need-snookers'].includes(intent.task)){
   const cue=state.balls.find(b=>live(b)&&b.n===0),target=state.balls.find(b=>b.i===intent.targetId);if(cue&&target){const d=dist(cue,target),axis={x:(target.x-cue.x)/d,z:(target.z-cue.z)/d};
    const variants=[];for(const thin of [-.94,-.8,-.55,.55,.8,.94]){const sum=(cue.r||.026)+(target.r||.026),aim={x:target.x-axis.z*thin*sum,z:target.z+axis.x*thin*sum},length=dist(cue,aim),direction={x:(aim.x-cue.x)/length,z:(aim.z-cue.z)/length};
     if(!g.clear(state,cue,aim,cue.r||.026,[cue.i,target.i]))continue;const n={x:(aim.x-target.x)/sum,z:(aim.z-target.z)/sum},dot=direction.x*n.x+direction.z*n.z,outgoing={x:direction.x-dot*n.x,z:direction.z-dot*n.z},want={x:zone.x-aim.x,z:zone.z-aim.z},alignment=(outgoing.x*want.x+outgoing.z*want.z)/(Math.hypot(outgoing.x,outgoing.z)*Math.hypot(want.x,want.z)||1);
     for(const power of [.18,.3,.45])variants.push({kind:'safety',targetIndex:target.i,hideBehindBallId:shadow?.hideBehindBallId,directed:true,requiresTrace:true,priority:alignment,label:'遮挡阴影薄球种子',shot:{direction,power,vertical:0,side:0,elevation:0}});}
    const shadows=variants.sort((a,b)=>b.priority-a.priority).slice(0,12),plain=out.splice(0);
    for(let i=0;i<Math.max(plain.length,shadows.length);i++){if(plain[i])out.push(plain[i]);if(shadows[i])out.push(shadows[i]);}}}
  return out.slice(0,28);
 }
 function destination(state,intent,brief){return ['contain','need-snookers'].includes(intent.task)?brief.shadowZones.find(z=>intent.hideBehindBallId==null||z.hideBehindBallId===intent.hideBehindBallId)?.centre:brief.sectors.find(s=>s.id===intent.sectorId)?.centre;}
 function refineIntent(state,candidate,result,intent,g,brief=analyze(state,g)){
  const zone=destination(state,intent,brief),cue=(result.nextBalls||result.balls||[]).find(b=>live(b)&&b.n===0),start=state.balls.find(b=>live(b)&&b.n===0);if(!zone||!cue||!start||!candidate.shot)return [];
  const distance=dist(cue,zone),travel=dist(start,cue),dx=cue.x-start.x,dz=cue.z-start.z,projection=travel>1e-6?((zone.x-cue.x)*dx+(zone.z-cue.z)*dz)/travel:distance;
  const correction=Math.max(-.12,Math.min(.12,projection/(Math.max(.1,travel)*2)*candidate.shot.power)),cushion=result.contacts?.some(c=>c.kind==='cushion'),base=candidate.shot;
  const target=state.balls.find(b=>b.i===candidate.targetIndex),direction=base.direction,forward=target?(zone.x-cue.x)*direction.x+(zone.z-cue.z)*direction.z:projection,spinCorrection=Math.sign(forward)*Math.min(.2,distance*.4);
  const specs=[[correction,0,0],[correction*.5,spinCorrection,0],[correction*1.4,-spinCorrection*.5,0],[-correction*.35,spinCorrection,0]];
  if(cushion)specs.push([correction*.5,0,-.16],[correction*.5,0,.16]);else specs.push([0,spinCorrection*1.25,0],[correction*.8,0,0]);
  return specs.map(([powerDelta,verticalDelta,side])=>({...candidate,parentCandidateId:candidate.id,directed:true,requiresTrace:true,destinationDistance:distance,refinement:'actual-destination-miss',shot:{...base,power:Math.max(.08,Math.min(.85,base.power+powerDelta)),vertical:Math.max(-.6,Math.min(.6,(base.vertical||0)+verticalDelta)),side:cushion?side:0,elevation:(base.vertical||0)+verticalDelta<0?.025*Math.PI:0}}));
 }
 function nextState(state,result){return {...state,balls:result.nextBalls||result.balls||[],rules:{...state.rules,...result.nextSnapshot?.rules,ballOn:result.adjudication?.nextBallOn??state.rules?.ballOn,freeBallNominee:null,nominatedColour:null}};}
 function compliance(state,expected,g){
  if(!expected)return {met:false,reason:'missing expectation'};const cue=state.balls?.find(b=>live(b)&&b.n===0),target=state.balls?.find(b=>live(b)&&b.i===expected.targetId);
  if(!cue||!target||!g.targets(state).some(b=>b.i===target.i))return {met:false,reason:'next target unavailable'};
  const position=g.sectorCheck(cue,expected.sector),route=g.attackRoutes(state,cue,[target]).some(r=>expected.sector?.pocketIndex==null||r.pocketIndex===expected.sector.pocketIndex);
  return {...position,routeAvailable:route,met:route,reason:route?'next route available':'next route blocked'};
 }
 function assess(state,candidate,result,intent,g,brief=analyze(state,g),options){
  const next=nextState(state,result),cue=next.balls.find(b=>live(b)&&b.n===0),sector=brief.sectors.find(s=>s.id===intent.sectorId),position=g.sectorCheck(cue,sector,result.trace),foul=!!(result.adjudication?.foul||result.adjudication?.foulCode),potted=result.potted||[];
  const expectedPotId=candidate?.potTargetIndex??intent.targetId;
  const scored=(result.adjudication?.score||0)>0&&(potted.includes(intent.targetId)||potted.includes(expectedPotId)),continues=result.adjudication?.continueBreak===true;
  const nextTargets=g.targets(next),nextRoutes=cue?g.attackRoutes(next,cue,nextTargets):[];
  const pockets=state.pockets||[],hasReds=(state.balls||[]).some(b=>live(b)&&b.n===1);
  let hasAlternative;
  const preserveConsumed=(intent.preserveIds||[]).filter(i=>{
   if(!potted.includes(i))return false;
   const obj=(state.balls||[]).find(b=>b.i===i);
   if(obj&&obj.n>=2&&(hasReds||(result.adjudication?.respots||[]).includes(i)))return false;
   if(obj&&pockets.some(p=>dist(obj,p)<=.22))return false;
   if(i===expectedPotId&&!foul&&continues){
    if(nextRoutes.length>0)return false;
    if(hasAlternative===undefined){const startCue=(state.balls||[]).find(b=>live(b)&&b.n===0);hasAlternative=!!startCue&&g.attackRoutes(state,startCue,g.targets(state)).some(r=>r.targetIndex!==expectedPotId&&(r.cut||0)>=.45);}
    if(!hasAlternative)return false;
   }
   return true;
  }).length;
  const nextTarget=next.balls.find(b=>live(b)&&b.i===intent.nextBallId),targetPositionChanged=!!(sector&&nextTarget&&dist(nextTarget,sector.origin)>(nextTarget.r||.026));
  const route=sector&&cue&&!targetPositionChanged?g.attackRoutes(next,cue,nextTargets.filter(b=>b.i===intent.nextBallId)).some(r=>r.pocketIndex===sector.pocketIndex):false;
  const hidden=cue&&nextTargets.length>0&&nextTargets.every(t=>g.visibleEdges(next,cue,t)===0);
  let developed=false;
  if(!foul&&scored&&continues&&cue){
   const clusterIds=candidate?.development?.clusterIds||brief.problemOrder||[],contact=result.contacts?.some(c=>clusterIds.includes(c.ballIndex));
   if(contact&&clusterIds.some(i=>{const a=state.balls.find(b=>b.i===i),b=next.balls.find(b=>live(b)&&b.i===i);return a&&b&&dist(a,b)>(a.r||.026)*2;})){
    const baseline={...state,balls:state.balls.filter(b=>!potted.includes(b.i))},beforeOpen=new Set(g.attackRoutes(baseline,cue,baseline.balls.filter(b=>live(b)&&b.n===1)).map(r=>r.targetIndex)),afterOpen=new Set(g.attackRoutes(next,cue,next.balls.filter(b=>live(b)&&b.n===1)).map(r=>r.targetIndex));
    const freed=clusterIds.some(i=>afterOpen.has(i)&&!beforeOpen.has(i)),insuranceIds=candidate?.development?.insuranceIds||intent.preserveIds||[];
    developed=freed&&(insuranceIds.some(i=>afterOpen.has(i)&&!clusterIds.includes(i))||(!!candidate?.development?.powerSplit&&!insuranceIds.length));
   }
  }
  const defensive=['contain','need-snookers'].includes(intent.task);
  const actor=state.rules?.playerIndex??0,nextActor=result.nextContext?.playerIndex??result.nextSnapshot?.rules?.playerIndex??(continues?actor:1-actor),handedOver=nextActor!==actor&&!continues&&(result.adjudication?.score||0)<=0&&potted.length===0;
  const zone=destination(state,intent,brief),destinationDistance=cue&&zone?dist(cue,zone):null;
  const b=state.bounds,fullTable=b&&(b.maxX-b.minX)>2.5,scale=b?Math.hypot(b.maxX-b.minX,b.maxZ-b.minZ):2;
  const cueBaulk=b&&cue?Math.max(0,Math.min(1,1-(cue.x-b.minX)/(b.maxX-b.minX))):0;
  const rail=b&&cue?Math.max(0,Math.min(1,1-Math.min(cue.x-b.minX,b.maxX-cue.x,cue.z-b.minZ,b.maxZ-cue.z)/(.12*scale))):0;
  const containSafe=!fullTable||cueBaulk>=.52||rail>=.45||hidden||(destinationDistance!==null&&destinationDistance<=.28);
  const met=!foul&&(defensive?(handedOver&&(intent.task==='need-snookers'?hidden:nextRoutes.length===0&&containSafe)):intent.task==='escape'?(result.firstHits||[]).some(i=>g.targets(state).some(b=>b.i===i)):intent.task==='develop'?!!developed:scored&&continues&&nextRoutes.length>0);
  const qFn=r=>Math.max(0,Math.min(1,((r.cut||.15)**1.4)/(1+(r.travel||0)/1.8)));
  const distinctNext=[],seenNext=new Set();for(const r of nextRoutes.slice().sort((a,b)=>qFn(b)-qFn(a)))if(!seenNext.has(r.targetIndex)){distinctNext.push(r);seenNext.add(r.targetIndex);if(distinctNext.length===3)break;}
  const mobilityBonus=scored&&continues&&!foul?Math.min(4.5,2.8*(distinctNext[0]?qFn(distinctNext[0]):0)+1.1*(distinctNext[1]?qFn(distinctNext[1]):0)+.5*(distinctNext[2]?qFn(distinctNext[2]):0)):0;
  const sectorProx=scored&&continues&&!foul&&sector&&cue?Math.max(0,1-dist(cue,sector.centre)/.55)*(route?1.8:.6):0;
  let expectedNext=null;
  if(options?.expectedNext!==false&&scored&&continues&&sector&&route&&(position.met||!distinctNext.length)){
   const edge=g.transitionGraph(next,24).find(e=>e.fromId===intent.nextBallId);
   expectedNext={targetId:intent.nextBallId,sector:{...sector,axis:{...sector.axis},origin:{...sector.origin},centre:{...sector.centre}},preserveIds:(intent.preserveIds||[]).filter(i=>next.balls.some(b=>live(b)&&b.i===i)),intent:edge?{task:'position',targetId:edge.fromId,nextBallId:edge.toId,sectorId:edge.sectorId,preserveIds:(intent.preserveIds||[]).filter(i=>i!==edge.fromId)}:undefined};
  }else if(options?.expectedNext!==false&&scored&&continues&&!foul&&cue&&distinctNext.length){
   const graph=g.transitionGraph(next,24),bestR=distinctNext[0],nb=next.balls.find(x=>live(x)&&x.i===bestR.targetIndex);
   const edge=graph.find(e=>e.fromId===bestR.targetIndex)||graph[0];
   if(nb&&edge){
    const d=Math.max(.08,dist(nb,cue)),ax={x:(cue.x-nb.x)/d,z:(cue.z-nb.z)/d};
    expectedNext={targetId:nb.i,sector:{id:`opportunistic-${nb.i}-${bestR.pocketIndex}`,targetId:nb.i,pocketIndex:bestR.pocketIndex,origin:{x:nb.x,z:nb.z},axis:ax,centre:{x:cue.x,z:cue.z},distance:d,minDistance:Math.max(.05,d-.18),maxDistance:d+.18,angleTolerance:.32,arrivalTolerance:.85},preserveIds:(intent.preserveIds||[]).filter(i=>next.balls.some(x=>live(x)&&x.i===i)),intent:{task:'position',targetId:edge.fromId,nextBallId:edge.toId,sectorId:edge.sectorId,preserveIds:(intent.preserveIds||[]).filter(i=>i!==edge.fromId)}};
   }
  }
  // Intent is planning metadata. Value is assigned once, in the shared points-based policy.
  const scoreDelta=0;
  return {met,destinationDistance,scoreDelta,features:{visitTask:intent.task,intentMet:met,destinationDistance,cueSectorReached:position.met,arrivalAligned:position.arrivalAligned,arrivalAngle:position.arrivalAngle,cueSectorAngle:position.angle,cueSectorDistance:position.distance,nextRouteAvailable:!!route,targetPositionChanged,snookerAchieved:!!hidden,handedOver,problemHandled:!!developed,preserveConsumed,mobilityBonus},expectedNext};
 }
 function rank(state,candidate,result,intent,g,brief){return assess(state,candidate,result,intent,g,brief);}
 return {analyze,normalizePlan,directed,refineIntent,assess,compliance,rank};
})();
if(typeof module!=='undefined'&&module.exports)module.exports=PCOLTacticalBrain;


/* Execution uncertainty calibrated against a fixed native-physics practice shot,
 * not a measured professional-player skill distribution.
 * describe is deterministic. perturb draws three uniform samples once and
 * returns a coherent native-compatible shot; search and delivery share it.
 */
const PCOLShotSkill = (() => {
  const profiles={club:{angle:.01026,power:.01728,vertical:.0324},strong:{angle:.0010098,power:.00972,vertical:.0216},expert:{angle:.00053568,power:.0054,vertical:.01296}};
  const clamp=(v,lo,hi)=>Math.max(lo,Math.min(hi,v));
  const distance=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);
  function describe(state,candidate,level='strong') {
    const profile=profiles[level]||profiles.strong;
    const cue=state.balls?.find(b=>b.n===0&&b.active!==false);
    const target=state.balls?.find(b=>b.i===candidate.targetIndex);
    const pocket=state.pockets?.[candidate.pocketIndex];
    const bounds=state.bounds;
    const scale=bounds?Math.max(.1,Math.hypot(bounds.maxX-bounds.minX,bounds.maxZ-bounds.minZ)):3.6;
    const travel=cue&&target?distance(cue,target)/scale:.3;
    let cut=0;
    if(target&&pocket) {
      const d=distance(target,pocket),direction=candidate.shot.direction;
      if(d>1e-9)cut=1-clamp((direction.x*(pocket.x-target.x)+direction.z*(pocket.z-target.z))/d,0,1);
    }
    const railGap=cue&&bounds?Math.min(cue.x-bounds.minX,bounds.maxX-cue.x,cue.z-bounds.minZ,bounds.maxZ-cue.z):Infinity;
    const rail=Number.isFinite(railGap)?clamp(1-railGap/Math.max(.06,(cue.r||.026)*4),0,1):0;
    const power=clamp(candidate.shot.power,0,1),difficulty=clamp(travel*.65+cut*.7+power*.2+rail*.3,0,1);
    return {level:profiles[level]?level:'strong',difficulty,distance:travel,cut,rail,
      angleSigma:profile.angle*(1+travel*2+cut*2+rail),
      powerSigma:profile.power*(1+travel+power+rail*.5),
      verticalSigma:profile.vertical*(1+power+rail)};
  }
  function perturb(shot,descriptor,random=Math.random) {
    // Uniform zero-mean error with the requested standard deviation.
    // Angular accuracy is independent of the power and spin error profiles.
    const sample=sigma=>(clamp(random(),0,1)*2-1)*Math.sqrt(3)*sigma;
    const angle=Math.atan2(shot.direction.z,shot.direction.x)+sample(descriptor.angleSigma);
    const power=clamp(shot.power+sample(descriptor.powerSigma),0,1);
    const vertical=clamp((shot.vertical||0)+sample(descriptor.verticalSigma),-1,1);
    return {...shot,direction:{x:Math.cos(angle),z:Math.sin(angle)},power,vertical,side:shot.side||0,
      elevation:vertical<0?.025*Math.PI:0};
  }
  // Common, stratified coordinates for comparisons. Each new pair changes all
  // three axes; actual delivery still draws independent uniform errors.
  function coordinates(index) {
    const pairs=[[.25,.25,.75],[1/12,7/12,5/12],[5/12,1/12,1/12]];
    const row=pairs[Math.floor(index/2)%pairs.length];
    return index%2?row.map(v=>1-v):row;
  }
  return {describe,perturb,coordinates};
})();

/* Geometric development intentions only; the native trial must prove the cannon and continuation. */
const PCOLDevelopment = (() => {
  const active=b=>b.active!==false&&Number.isFinite(b.x)&&Number.isFinite(b.z);
  const r=b=>Number.isFinite(b.r)&&b.r>0?b.r:.026;
  const dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);
  const unit=v=>{const d=Math.hypot(v.x,v.z);return d>1e-8?{x:v.x/d,z:v.z/d}:null;};
  function generate(state,geometry) {
    const balls=(state.balls||[]).filter(active),cue=balls.find(b=>b.n===0);
    if(!cue||!geometry?.attackRoutes||!geometry?.targets||!geometry?.clear)return [];
    const reds=balls.filter(b=>b.n===1),remaining=new Set(reds),clusters=[];
    while(remaining.size){
      const first=remaining.values().next().value,group=[first];remaining.delete(first);
      for(let i=0;i<group.length;i++)for(const b of remaining)if(dist(group[i],b)<=1.55*(r(group[i])+r(b))){group.push(b);remaining.delete(b);}
      if(group.length>=2)clusters.push(group);
    }
    if(!clusters.length)return [];
    const routes=geometry.attackRoutes(state,cue,geometry.targets(state));
    const insuranceRoutes=geometry.attackRoutes(state,cue,reds),result=[];
    for(const route of routes){
      const target=balls.find(b=>b.i===route.targetIndex),pocket=state.pockets?.[route.pocketIndex];
      if(!target||!pocket)continue;
      const normal=unit({x:pocket.x-target.x,z:pocket.z-target.z}),incoming=unit(route.direction);
      if(!normal||!incoming)continue;
      const projection=incoming.x*normal.x+incoming.z*normal.z;
      const tangent={x:incoming.x-projection*normal.x,z:incoming.z-projection*normal.z};
      const contact={x:target.x-normal.x*(r(cue)+r(target)),z:target.z-normal.z*(r(cue)+r(target))};
      const {direction,...meta}=route;
      const explicit=state.rules?.nominatedColour;
      const nomination=state.rules?.ballOn===252?{nominatedColour:explicit>=2&&explicit<=7?explicit:target.n>=2&&target.n<=7?target.n:2}:{};
      const label=target.n>=2?'借彩球轻拆':'进攻轻拆';
      for(const cluster of clusters){
        if(cluster.some(b=>b.i===target.i))continue;
        const ids=cluster.map(b=>b.i),centre={x:cluster.reduce((s,b)=>s+b.x,0)/cluster.length,z:cluster.reduce((s,b)=>s+b.z,0)/cluster.length};
        const insuranceIds=[...new Set(insuranceRoutes.filter(a=>!ids.includes(a.targetIndex)&&a.targetIndex!==target.i).map(a=>a.targetIndex))];
        let delicateAdded=0;
        for(const vertical of [0,.3,-.3]){
          // Modest axial component is an alignment heuristic, not a spin/trajectory solver.
          const outgoing=unit({x:tangent.x+normal.x*vertical*.35,z:tangent.z+normal.z*vertical*.35});
          if(!outgoing)continue;
          const entries=cluster.map(b=>{const dx=b.x-contact.x,dz=b.z-contact.z,t=dx*outgoing.x+dz*outgoing.z;
            return {b,t,offset:Math.abs(dx*outgoing.z-dz*outgoing.x)};
          }).filter(e=>e.t>r(cue)+r(e.b)&&e.t<1.5&&e.offset<r(cue)+r(e.b)*.8&&e.offset>r(e.b)*.3).sort((a,b)=>a.t-b.t);
          const entry=entries[0];if(!entry)continue;
          // Approach an exposed edge: reject a line aimed deeply through the cluster centre.
          const centreOffset=Math.abs((centre.x-contact.x)*outgoing.z-(centre.z-contact.z)*outgoing.x);
          if(centreOffset<r(entry.b)*.65)continue;
          const endpoint={x:contact.x+outgoing.x*Math.max(0,entry.t-(r(cue)+r(entry.b))),z:contact.z+outgoing.z*Math.max(0,entry.t-(r(cue)+r(entry.b)))};
          if(!geometry.clear(state,contact,endpoint,r(cue),[cue.i,target.i,entry.b.i]))continue;
          const base=Math.max(.24,Math.min(.62,.23+.045*route.travel+.10*(1-route.cut)+.08*entry.t));
          for(const delta of [0,.07]){
            result.push({...meta,...nomination,label,development:{clusterIds:ids.slice(),entryIndex:entry.b.i,insuranceIds:insuranceIds.slice()},
              shot:{direction:{...route.direction},power:Math.min(.85,base+delta),side:0,vertical,elevation:vertical<0?.025*Math.PI:0}});
            delicateAdded++;
          }
        }
        if((cluster.length>=3||!delicateAdded)&&(route.cut||0)>=.38){
          for(const vertical of [0,-.45,.45,-.3,.3]){
            const outgoing=unit({x:tangent.x+normal.x*vertical*.45,z:tangent.z+normal.z*vertical*.45});
            if(!outgoing)continue;
            const entries=cluster.map(b=>{const dx=b.x-contact.x,dz=b.z-contact.z,t=dx*outgoing.x+dz*outgoing.z;
              return {b,t,offset:Math.abs(dx*outgoing.z-dz*outgoing.x)};
            }).filter(e=>e.t>r(cue)+r(e.b)&&e.t<1.65&&e.offset<r(cue)+r(e.b)*.95).sort((a,b)=>a.t-b.t);
            const entry=entries[0];if(!entry)continue;
            const endpoint={x:contact.x+outgoing.x*Math.max(0,entry.t-(r(cue)+r(entry.b))),z:contact.z+outgoing.z*Math.max(0,entry.t-(r(cue)+r(entry.b)))};
            if(!geometry.clear(state,contact,endpoint,r(cue),[cue.i,target.i,entry.b.i]))continue;
            const powerBase=Math.max(.66,Math.min(.82,.58+.06*route.travel+.08*entry.t));
            for(const delta of [0,.07]){
              result.push({...meta,...nomination,powerSplit:true,label,development:{clusterIds:ids.slice(),entryIndex:entry.b.i,insuranceIds:insuranceIds.slice(),powerSplit:true},
                shot:{direction:{...route.direction},power:Math.min(.85,powerBase+delta),side:0,vertical,elevation:vertical<0?.025*Math.PI:0}});
            }
          }
        }
      }
    }
    return (geometry.diverse?geometry.diverse(result):result).slice(0,16);
  }
  return {generate};
})();

/* Bounded minimax replaces a leaf estimate with adjudicated points and a new leaf. */
const PCOLContinuation=(()=>{
  function create({geometry,policy,core,development,skill}) {
    function settled(base,result) {
      if(!result.nextSnapshot||!result.nextBalls||result.adjudication?.foulCode)return null;
      const rules={...base.rules,...result.nextSnapshot.rules,...result.nextContext};
      const next={...base,balls:result.nextBalls,rules,scores:rules.scores,touching:null};
      if(core?.remainingPoints)next.remainingPoints=core.remainingPoints(next.balls,rules.ballOn);
      if(!rules.ballOn||rules.requiresDraw||rules.inHand||rules.freeBallAvailable||rules.freeBallReview)return null;
      if(core?.touchingStatus){next.touching=core.touchingStatus({balls:next.balls,...rules});if(next.touching?.requiresColourDeclaration)return null;}
      return next;
    }
    function orderedSeeds(state,layout) {
      const blocked=layout(state).hasDirectHit===false;
      const developed=development?.generate(state,geometry)||[];
      const pool=geometry.generate(state),attacks=pool.filter(c=>c.kind==='attack'&&!c.development);
      const merit=c=>((c.cut??1)**1.5)/(1+(c.travel||0))*(state.balls?.find(b=>b.i===(c.potTargetIndex??c.targetIndex))?.n||1);
      attacks.sort((a,b)=>merit(b)-merit(a));
      const diverse=geometry.diverse||((items)=>items),objective=policy.analyze?.(state).objective;
      const safety=diverse(pool.filter(c=>c.kind==='safety')),escape=diverse(pool.filter(c=>c.kind==='escape'));
      const ordered=blocked?escape.concat(safety,attacks,developed):objective==='need-snookers'?safety.concat(attacks,developed,escape):
        attacks.length?[attacks[0],...(developed.length?diverse(developed):diverse(attacks.slice(1))),...diverse(attacks.slice(1)),...safety,...escape]:safety.concat(escape,developed);
      const seen=new Set(),first=[],rest=[];
      for(const seed of ordered){const key=geometry.routeKey?geometry.routeKey(seed):[seed.kind,seed.targetIndex,seed.pocketIndex,!!seed.development].join(':');
        if(seen.has(key))rest.push(seed);else{seen.add(key);first.push(seed);}}
      return first.concat(rest);
    }
    // Revisited first layers share immutable nodes and seed order within this search only.
    function createSession({policySession}={}) {
      const sharedPolicy=policySession||policy.createSession?.(geometry);
      const nodes=new WeakMap(),seedLists=new WeakMap(),evaluators=new WeakMap(),rootStates=new WeakMap();
      const layout=state=>sharedPolicy?sharedPolicy.layout(state):policy.layout(state,geometry);
      function nextState(base,result) {
        let children=nodes.get(base);
        if(!children){children=new WeakMap();nodes.set(base,children);}
        if(!children.has(result))children.set(result,settled(base,result));
        return children.get(result);
      }
      function seeds(state,count) {
        let list=seedLists.get(state);
        if(!list){list=orderedSeeds(state,layout);seedLists.set(state,list);}
        return list.slice(0,count);
      }
      function evaluatePolicy(state,candidate,result) {
        if(sharedPolicy)return sharedPolicy.evaluate(state,candidate,result);
        let evaluator=evaluators.get(state);
        if(!evaluator){evaluator=policy.createEvaluator?.(state,geometry)||((c,r)=>policy.evaluate(state,c,r,geometry));evaluators.set(state,evaluator);}
        return evaluator(candidate,result);
      }
    async function evaluate({state,candidate,result,preparedEvaluation,simulateFrom,canContinue=()=>true,maxTrials=6,depth:requestedDepth,breadth:requestedBreadth}) {
      const root=state.rootPlayerIndex??state.rules.playerIndex;
      if(state.rootPlayerIndex==null){
        let rooted=rootStates.get(state);
        if(!rooted){rooted={...state,rootPlayerIndex:root};rootStates.set(state,rooted);}
        state=rooted;
      }
      const original=preparedEvaluation||evaluatePolicy(state,candidate,result);
      const summary={mode:'unassessed',status:'unassessed',trials:0,completed:0,verifiedPath:[],coverage:'unknown',chainVerified:false,insuranceVerified:false,provenTerminalLoss:false,rootTerminalLoss:original.terminalValue<0,
        assessment:'bounded sampled branch; not evidence for every execution outcome'};
      let interrupted=false;
      const cap=Math.max(0,Math.min(12,Math.floor(maxTrials)));
      const levelFor=s=>s.rules.playerIndex===root?s.skill:s.opponentSkill;
      const checkExecution=!!skill&&!!levelFor(nextState(state,result)||state);
      const width=checkExecution?3:1;
      const horizon=requestedDepth??(cap>=(checkExecution?12:6)?2:cap>0?1:0);
      const requestedWidth=requestedBreadth??(checkExecution&&horizon>1?1:2);
      summary.depth=horizon;
      summary.execution=checkExecution?'nominal-and-common-error-pair':'geometric-proxy; opponent skill may be unknown';
      async function visit(base,parent,depth) {
        const next=nextState(base,parent);if(!next||depth<=0)return null;
        const maximise=next.rules.playerIndex===root,branches=[];
        const available=cap-summary.trials;
        // Compare siblings before spending the same bounded cap below a single route.
        const level=levelFor(next),sampleCount=skill&&level?2:0,unit=1+sampleCount;
        const breadth=Math.min(requestedWidth,Math.floor(cap/unit));
        if(!breadth||available<breadth*unit){interrupted=true;return null;}
        for(const seed of seeds(next,breadth)) {
          const executions=[seed],uncertainty=sampleCount?skill.describe(next,seed,level):null;
          for(let i=0;i<sampleCount;i++){let k=0;const values=skill.coordinates(i);
            executions.push({...seed,shot:skill.perturb(seed.shot,uncertainty,()=>values[k++])});}
          const observations=[];
          for(let sample=0;sample<executions.length;sample++){
          if(summary.trials>=cap||!canContinue()){interrupted=true;break;}
          summary.trials++;
          const r=await simulateFrom(parent,executions[sample]);
          if(r?.status!=='complete'||!r.adjudication||!r.nextBalls){interrupted=true;continue;}
          summary.completed++;
          const e=evaluatePolicy(next,seed,r);
          if(!e.terminalValue&&!nextState(next,r)){interrupted=true;summary.adjudicationPending=true;}
          const potted=!r.adjudication.foulCode&&r.adjudication.score>0&&(r.potted||[]).some(i=>i===seed.targetIndex||i===seed.potTargetIndex);
          const cluster=seed.development?.clusterIds||[];
          const opened=cluster.some(i=>(e.features?.freedRedIds||[]).includes(i)&&(r.contacts||[]).some(c=>c.ballIndex===i));
          const entry={actor:next.rules.playerIndex,ballPhase:next.rules.ballOn,targetIndex:seed.targetIndex,execution:sample===0?'nominal':'sample-'+(sample-1),
            nominatedColour:seed.nominatedColour??null,points:r.adjudication.score||0,potted,
            nextActor:e.features?.nextPlayerIndex??r.nextContext?.playerIndex??r.nextSnapshot?.rules?.playerIndex,
            foulCode:r.adjudication.foulCode||0,development:!!seed.development,developmentOpened:opened,clusterIds:cluster,components:{netPoints:e.netPoints,immediateCost:e.immediateCost||0,futureValue:e.futureValue,terminalValue:e.terminalValue}};
          observations.push({value:e.score,path:[entry],r,e,terminalLoss:e.terminalValue<0});
          }
          const nominal=observations.find(row=>row.path[0].execution==='nominal');
          if(!nominal)continue;
          const errors=observations.filter(row=>row!==nominal);
          const value=errors.length===sampleCount&&sampleCount?policy.aggregate({...next,rootPlayerIndex:next.rules.playerIndex},errors.map(row=>maximise?row.value:-row.value)).score*(maximise?1:-1):nominal.value;
          if(observations.length!==executions.length)interrupted=true;
          branches.push({...nominal,value,observations,sampleCount});
        }
        branches.sort((a,b)=>maximise?b.value-a.value:a.value-b.value);
        const expandable=branches.flatMap(branch=>branch.observations.filter(row=>!row.e.terminalValue&&nextState(next,row.r)));
        if(depth>1&&cap-summary.trials<expandable.length*requestedWidth*width){interrupted=true;return branches[0]||null;}
        if(depth>1)for(const branch of expandable) {
          if(summary.trials>=cap||!canContinue()){interrupted=true;break;}
          if(branch.e.terminalValue)continue;
          const child=await visit(next,branch.r,depth-1);
          if(child){branch.value=branch.e.netPoints+(branch.e.immediateCost||0)+branch.e.terminalValue+child.value;branch.path=branch.path.concat(child.path);branch.terminalLoss=child.terminalLoss;}
        }
        if(depth>1)for(const branch of branches){
          const errors=branch.observations.slice(1),nominal=branch.observations[0];
          branch.value=errors.length===branch.sampleCount&&errors.length?policy.aggregate({...next,rootPlayerIndex:next.rules.playerIndex},errors.map(row=>maximise?row.value:-row.value)).score*(maximise?1:-1):nominal.value;
          branch.path=nominal.path;branch.terminalLoss=nominal.terminalLoss;
        }
        branches.sort((a,b)=>maximise?b.value-a.value:a.value-b.value);
        return branches[0]||null;
      }
      const next=nextState(state,result);
      if(next&&result.adjudication&&!original.terminalValue) {
        summary.mode=next.rules.playerIndex===root?'continuation':'opponent-reply';
        const best=await visit(state,result,horizon);
        if(best){
          summary.sampledPath=best.path;
          summary.executionOutcomes=best.observations.map(row=>({value:row.value,path:row.path}));
          if(summary.mode==='continuation'&&!result.adjudication.foulCode&&result.adjudication.score>0)
            for(const entry of best.path){if(entry.actor!==root||!entry.potted)break;summary.verifiedPath.push(entry);}
          summary.provenContinuation=summary.verifiedPath.length>0;
          summary.chainVerified=summary.verifiedPath.length>=2;
          const cluster=candidate.development?.clusterIds||summary.verifiedPath.find(e=>e.development)?.clusterIds||[];
          const developedAt=summary.verifiedPath.findIndex(e=>e.development);
          summary.insuranceVerified=summary.chainVerified&&cluster.length>0&&summary.verifiedPath.some((e,i)=>
            i>developedAt&&e.ballPhase===2&&!cluster.includes(e.targetIndex));
          if(summary.verifiedPath.some(e=>e.development)&&(!summary.verifiedPath.some(e=>e.developmentOpened)||!summary.insuranceVerified))summary.chainVerified=false;
          if(summary.mode==='opponent-reply')summary.opponentBestReply=best.path[0];
          summary.status=interrupted?'partial':'complete';summary.coverage=interrupted?'partial':'covered';
          summary.sampledTerminalLoss=!!best.terminalLoss;
          // A terminal leaf proves that sampled execution lost, not a forced minimax loss.
          summary.provenTerminalLoss=false;
          return {futureValue:best.value,scoreDelta:best.value-original.futureValue,shallowScore:original.score,comparableScore:original.score,horizonScore:original.score+best.value-original.futureValue,summary};
        }
      }
      if(summary.trials){summary.status='partial';summary.coverage='partial';}
      if(result.adjudication?.foulCode)summary.adjudicationPending=true;
      if(original.terminalValue){summary.status='complete';summary.coverage='covered';summary.provenTerminalLoss=original.terminalValue<0;}
      return {futureValue:original.futureValue,scoreDelta:0,shallowScore:original.score,comparableScore:original.score,horizonScore:original.terminalValue?original.score:null,summary};
    }
      return {evaluate};
    }
    return {evaluate:options=>createSession({policySession:options.policySession}).evaluate(options),createSession};
  }
  return {create};
})();

/* Shared cooperative clock: explicit pauses never spend effective search time. */
const PCOLComputeScheduler=(()=>{
  const bounded=(value,fallback)=>Number.isFinite(value)?Math.max(0,Math.min(16,value)):fallback;
  function create({now=()=>performance.now(),setTimer=setTimeout,clearTimer=clearTimeout}={}) {
    let pacing={sliceMs:6,delayMs:4};
    function setPacing(settings={}) {pacing={sliceMs:bounded(settings.sliceMs,pacing.sliceMs),delayMs:bounded(settings.delayMs,pacing.delayMs)};}
    function start({cooperativeYield}={}) {
      const enabled=cooperativeYield!==false,settings=cooperativeYield||{},started=now();
      let waitMs=0,yields=0,sliceStarted=started,pause=null,cancelled=false,closed=false;
      const deadlines=new Set();
      const pausedMs=()=>waitMs+(pause?now()-pause.started:0);
      const clock=()=>now()-pausedMs();
      function arm(entry) {
        clearTimer(entry.timer);
        if(!pause&&!closed&&!cancelled)entry.timer=setTimer(()=>{
          if(!deadlines.delete(entry))return;
          entry.callback();
        },Math.max(0,entry.deadline-clock()));
      }
      function setDeadline(deadline,callback) {
        const entry={deadline,callback};deadlines.add(entry);arm(entry);
        return ()=>{clearTimer(entry.timer);deadlines.delete(entry);};
      }
      function resume() {
        if(!pause)return;
        const current=pause;pause=null;clearTimer(current.timer);
        waitMs+=now()-current.started;sliceStarted=now();
        for(const entry of deadlines)arm(entry);
        current.resolve(!cancelled&&!closed);
      }
      async function checkpoint() {
        if(cancelled||closed)return false;
        const sliceMs=bounded(settings.sliceMs,pacing.sliceMs),delayMs=bounded(settings.delayMs,pacing.delayMs);
        if(!enabled||now()-sliceStarted<sliceMs)return true;
        if(pause)return pause.promise;
        for(const entry of deadlines)clearTimer(entry.timer);
        yields++;
        const current={started:now()};pause=current;
        current.promise=new Promise(resolve=>{current.resolve=resolve;current.timer=setTimer(resume,delayMs);});
        return current.promise;
      }
      // Call after creating the promise: synchronous Worker simulation still fills
      // the slice; only the subsequent natural await is ignored for pacing.
      async function wait(promise) {
        const waiting=now();try{return await promise;}finally{sliceStarted+=now()-waiting;}
      }
      function cancel() {cancelled=true;resume();for(const entry of deadlines)clearTimer(entry.timer);}
      function close() {closed=true;resume();for(const entry of deadlines)clearTimer(entry.timer);deadlines.clear();}
      return {now:clock,checkpoint,wait,setDeadline,cancel,close,
        stats:()=>({enabled,yields,waitMs:pausedMs(),budgetElapsedMs:clock()-started})};
    }
    return {start,setPacing};
  }
  return {create};
})();

/* Compact legal turn options. Geometry scores are proxies; native trials rank shots. */
const PCOLTurnOptions = (() => {
  const active=b=>b.active!==false&&Number.isFinite(b.x)&&Number.isFinite(b.z);
  const radius=b=>b.r>0?b.r:.026;
  const dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);
  const copy=s=>({...s,balls:(s.balls||[]).map(b=>({...b})),rules:{...s.rules},scores:[...(s.scores||s.rules?.scores||[0,0])]});
  function create({geometry,core}) {
    function placements(state,dArea=state.dArea) {
      if(!dArea)return [];
      const {center,arcDir,diameterDir,radius:R}=dArea;
      const cue=(state.balls||[]).find(b=>b.n===0),r=radius(cue||{}),bounds=state.bounds;
      const positions=[[.72,.12],[-.72,.12],[0,.30],[0,0],[.42,.42],[-.42,.42],[0,.75],[.82,0],[-.82,0]];
      return positions.map(([side,back],i)=>({id:`d-${i}`,x:center.x+R*(side*diameterDir.x+back*arcDir.x),y:center.y??cue?.y??0,z:center.z+R*(side*diameterDir.z+back*arcDir.z)})).filter(p=>{
        const dx=p.x-center.x,dz=p.z-center.z;
        return dx*dx+dz*dz<=R*R+1e-9&&dx*arcDir.x+dz*arcDir.z>=-1e-9&&
          (!bounds||(p.x>=bounds.minX+r&&p.x<=bounds.maxX-r&&p.z>=bounds.minZ+r&&p.z<=bounds.maxZ-r))&&
          !(state.balls||[]).some(b=>b.n>0&&active(b)&&dist(p,b)<r+radius(b)+1e-5);
      });
    }
    function isOpening(state) {
      const rules=state.rules||{},reds=(state.balls||[]).filter(b=>b.n===1&&active(b));
      if(!(rules.inHand>0)||rules.ballOn!==2||!(Number.isFinite(rules.nRounds)&&rules.nRounds<=1)||reds.length!==15)return false;
      const seen=new Set([reds[0].i]);let changed=true;
      while(changed){changed=false;for(const b of reds)if(!seen.has(b.i)&&reds.some(a=>seen.has(a.i)&&dist(a,b)<=1.14*(radius(a)+radius(b)))){seen.add(b.i);changed=true;}}
      return seen.size===15;
    }
    function openingShots(state) {
      if(!isOpening(state))return [];
      const cue=(state.balls||[]).find(b=>b.n===0&&active(b));if(!cue)return [];
      const reds=geometry.targets(state),mean=reds.reduce((p,b)=>({x:p.x+b.x/reds.length,z:p.z+b.z/reds.length}),{x:0,z:0});
      const axis={x:mean.x-cue.x,z:mean.z-cue.z},length=Math.hypot(axis.x,axis.z);if(!length)return [];
      const transverse=b=>(b.x-mean.x)*(-axis.z/length)+(b.z-mean.z)*(axis.x/length);
      const sorted=[...reds].sort((a,b)=>transverse(a)-transverse(b)),result=[];
      for(const power of [.48,.53,.58,.63,.68])for(const thin of [.72,.80,.88])for(const [target,sign] of [[sorted[0],-1],[sorted.at(-1),1]]){
        const d=dist(cue,target),ux=(target.x-cue.x)/d,uz=(target.z-cue.z)/d,offset=(radius(cue)+radius(target))*thin*sign;
        const aim={x:target.x-uz*offset,z:target.z+ux*offset},travel=dist(cue,aim);
        if(!geometry.clear(state,cue,aim,radius(cue),[cue.i,target.i]))continue;
        result.push({kind:'safety',opening:true,targetIndex:target.i,label:'标准薄红球开球',priority:1,shot:{direction:{x:(aim.x-cue.x)/travel,z:(aim.z-cue.z)/travel},power,side:0,vertical:.25,elevation:0}});
      }
      return result;
    }
    function summarize(state) {
      const cue=(state.balls||[]).find(b=>b.n===0&&active(b)),on=geometry.targets(state);
      const bounds=state.bounds,scale=bounds?Math.hypot(bounds.maxX-bounds.minX,bounds.maxZ-bounds.minZ):2;
      const routes=cue?geometry.attackRoutes(state,cue,on):[];
      const qualities=routes.map(r=>Math.max(0,r.cut||0)**1.5/(1+2*(r.travel||0)/scale));
      const nominee=(state.balls||[]).find(b=>b.i===state.rules?.freeBallNominee&&active(b));
      const directMask=nominee?1<<nominee.n:state.rules?.ballOn===252&&state.rules?.nominatedColour?1<<state.rules.nominatedColour:state.rules?.ballOn;
      const direct=cue?core.hasDirectHit(state.balls,directMask,cue):{hasDirectHit:null};
      return {bestPotQuality:Math.max(0,...qualities),possibleTargets:on.length,potRoutes:routes.length,blocked:direct.hasDirectHit===false,directHit:direct.hasDirectHit,
        targetDistance:cue&&on.length?Math.min(...on.map(b=>dist(cue,b)))/scale:0,inHand:state.rules?.inHand>0};
    }
    function nominations(state) {
      const rules=state.rules||{},decline={id:'free-decline',nominee:null,rulesOverride:{freeBallNominee:null}};
      if(!rules.freeBallAvailable)return [decline];
      const on=new Set(geometry.targets({...state,rules:{...rules,freeBallNominee:null}}).map(b=>b.i));
      const candidates=(state.balls||[]).filter(b=>b.n>0&&active(b)&&!on.has(b.i)).map(b=>{
        const rulesOverride={freeBallNominee:b.i};
        const features=summarize({...state,rules:{...rules,...rulesOverride}});
        return {id:`free-${b.i}`,nominee:b.i,rulesOverride,features,preorder:features.bestPotQuality};
      }).sort((a,b)=>b.preorder-a.preorder);
      return [decline,...candidates.slice(0,6)];
    }
    function foulChoices(state,pending) {
      if(!pending)return [];
      const incoming=1-pending.offender,before=pending.before.context||pending.before.rules||{};
      return ['continue','again',...(pending.miss?['restore']:[])].map(action=>{
        const next=copy(state),rules=next.rules;
        if(action==='restore'){next.balls=(pending.before.balls||[]).map(b=>({...b}));Object.assign(rules,before);}
        rules.playerIndex=action==='continue'?incoming:pending.offender;
        rules.ballOn=action==='continue'?pending.result.nextBallOn:before.ballOn;
        if(action==='again'&&rules.ballOn===2&&!next.balls.some(b=>active(b)&&b.n===1))rules.ballOn=4;
        rules.inHand=action==='restore'?(before.inHand||0):(pending.result.requiresInHand?2:state.rules?.inHand||0);
        rules.freeBallAvailable=action==='continue'&&Boolean(state.rules?.freeBallAvailable);
        rules.freeBallNominee=null;rules.nominatedColour=null;rules.nominationSource=null;
        rules.freeBallReview=false;rules.freeBallDeclined=false;rules.scores=[...next.scores];
        const features=summarize(next);
        return {id:action,action,state:next,features,score:null};
      });
    }
    return {placements,isOpening,openingShots,nominations,foulChoices,summarize};
  }
  return {create};
})();

/* One pre-shot decision: adjudicated foul options, nomination and legal D placement. */
const PCOLTurnManager = (() => {
  function create({getState,getPending,getTrial,options,geometry,policy,skill,choose,commit,onError,onChange=()=>{},onEvent=()=>{},scheduler,cooperativeYield}) {
    const scheduling=scheduler||(typeof PCOLComputeScheduler!=='undefined'?PCOLComputeScheduler:require('./compute-scheduler')).create();
    let active=null,epoch=0,failed=false,lastResult=null;
    const status=()=>({busy:!!active,failed,phase:active?.phase||'idle',lastResult});
    const changed=()=>onChange(status());
    function cancel(){epoch++;if(active){active.schedule.cancel();getTrial().cancel();}active=null;failed=false;changed();}
    const available=(job,deadline=job.deadline)=>epoch===job.epoch&&!job.control.expired&&job.schedule.now()<deadline;
    async function simulate(job,trial,scenario,shot,nomination,deadline,maxWallMs) {
      if(!available(job,deadline)||!await job.schedule.checkpoint()||!available(job,deadline))return null;
      job.control.inFlight=true;
      try{return await job.schedule.wait(trial.simulateScenario(scenario,shot,{nominatedColour:nomination,
        maxWallMs:Math.min(maxWallMs,Math.max(1,deadline-job.schedule.now())),trace:false}));}
      catch(error){if(epoch!==job.epoch||job.control.expired)return null;throw error;}
      finally{job.control.inFlight=false;}
    }
    function variants(state) {
      const positions=state.rules.inHand>0?options.placements(state):[null];
      const result=[];
      for(const position of positions)for(const nomination of options.nominations(state)) {
        const balls=state.balls.map(b=>b.n===0&&position?{...b,...position,active:true}:{...b});
        const rules={...state.rules,...nomination.rulesOverride,freeBallReview:false,
          freeBallDeclined:nomination.nominee==null,nominationSource:state.rules.nominationSource};
        const next={...state,balls,rules},features=options.summarize(next);
        result.push({id:(position?.id||'current')+'-'+nomination.id,position,nominee:nomination.nominee,state:next,
          features,score:null,preorder:features.bestPotQuality});
      }
      return result.sort((a,b)=>b.preorder-a.preorder).slice(0,options.isOpening(state)?9:8);
    }
    function seeds(state) {
      const pool=options.isOpening(state)?options.openingShots(state):geometry.generate(state),picked=[],used=new Set();
      // Cycle kinds and spread targets/powers before revisiting a route family.
      for(let i=0;i<3;i++)for(const kind of ['attack','safety','escape']){
        const candidates=pool.filter(s=>s.kind===kind&&!picked.includes(s));
        const seed=candidates.find(s=>!used.has(s.targetIndex+'_'+s.shot.power))||candidates[0];
        if(seed){picked.push(seed);used.add(seed.targetIndex+'_'+seed.shot.power);}
      }
      if(options.isOpening(state))return pool.filter((_,i)=>[0,3,8,11,14,17,20,25,28].includes(i));
      return picked;
    }
    async function evaluateOption(option,trial,job,serial) {
      const state=option.state;
      const evaluate=policy.createEvaluator?policy.createEvaluator(state,geometry):(c,r)=>policy.evaluate(state,c,r,geometry);
      const nominalDeadline=job.schedule.now()+Math.max(0,job.deadline-job.schedule.now())*.65;
      const scenario={balls:state.balls,rules:state.rules,cuePosition:option.position};
      if(serial)scenario.serial=serial;
      let best=null,tested=0,legal=0,fouls=0;const finalists=[];
      const routes=seeds(state);
      for(const seed of routes) {
        if(!available(job,nominalDeadline))break;
        const r=await simulate(job,trial,scenario,seed.shot,seed.nominatedColour,nominalDeadline,2200);
        if(!r)break;tested++;
        if(r.stale)throw new Error('Position changed; AI decision is stale');
        if(r.status!=='complete'||!r.adjudication)continue;
        const evaluated=evaluate(seed,r);
        if(r.adjudication.foulCode){fouls++;continue;}
        legal++;
        const score=evaluated.score;
        finalists.push({score,seed,result:r,features:evaluated.features});
      }
      const testedFinalists=finalists.sort((a,b)=>b.score-a.score).slice(0,2);
      for(const candidate of testedFinalists) {
        const uncertainty=skill.describe(state,candidate.seed,state.skill);
        candidate.samples=[];
        for(let index=0;index<2;index++) {
          const values=skill.coordinates(index);
          if(!available(job))break;
          let i=0;const shot=skill.perturb(candidate.seed.shot,uncertainty,()=>values[i++]);
          const r=await simulate(job,trial,scenario,shot,candidate.seed.nominatedColour,job.deadline,2000);
          if(!r)break;
          if(r.stale)throw new Error('Position changed; AI decision is stale');
          if(r.status==='complete'&&r.adjudication){
            candidate.samples.push({index,value:evaluate(candidate.seed,r).score,foul:!!r.adjudication.foulCode});
          }
        }
      }
      const indices=[0,1].filter(i=>testedFinalists.every(c=>c.samples.some(row=>row.index===i)));
      for(const candidate of testedFinalists){
        const rows=candidate.samples.filter(row=>indices.includes(row.index));
        candidate.nominalScore=candidate.score;
        candidate.features={...candidate.features,executionSamples:rows.length,sampledFoulRate:rows.length?rows.filter(r=>r.foul).length/rows.length:null};
        if(rows.length){const value=policy.aggregate(state,rows.map(r=>r.value));candidate.score=value.score;
          candidate.features={...candidate.features,executionMean:value.mean,executionDownside:value.downside};}
        if(!best||candidate.score>best.score)best=candidate;
      }
      option.features={...option.features,tested,legal,fouls,verified:!!best,freeBallNominee:option.nominee,
        cuePosition:option.position&&{x:option.position.x,z:option.position.z}};
      if(best) {
        const r=best.result,v=r.adjudication,cue=r.nextBalls.find(b=>b.n===0);
        option.score=best.score;option.features={...option.features,...best.features};
        option.nominalScore=best.nominalScore;option.executionScores=best.samples;
        option.outcome={score:v.score,foulCode:0,nextBallOn:v.nextBallOn,cue:{x:cue.x,z:cue.z}};
        option.candidate={...best.seed,score:best.score,features:best.features,stroke:r.stroke,actual:r.compiled.actual,
          skill:skill.describe(state,best.seed,state.skill),outcome:{...option.outcome,nominatedColour:v.ballOnUsed}};
      } else {option.score=null;option.features.assessment='unknown';}
      return option;
    }
    async function run() {
      if(active||failed)return;
      const started=performance.now(),schedule=scheduling.start({cooperativeYield}),workStarted=schedule.now();
      const wallLimitMs=37000,job=active={epoch,schedule,phase:'turn-search',deadline:workStarted+18000,control:{expired:false,inFlight:false}};changed();
      const expire=()=>{job.control.expired=true;schedule.cancel();if(job.control.inFlight)getTrial().cancel();};
      const clearDeadline=schedule.setDeadline(job.deadline,expire),wallTimer=setTimeout(expire,wallLimitMs);
      try {
        const trial=getTrial(),before=JSON.stringify(trial.snapshot()),state=getState(),pending=getPending();
        let choices=[],kind;
        if(pending) {
          kind='foul';
          const actions=options.foulChoices(state,pending);
          for(let actionIndex=0;actionIndex<actions.length;actionIndex++) {
            const action=actions[actionIndex];let best=null;
            const actionDeadline=schedule.now()+Math.max(0,job.deadline-schedule.now())/(actions.length-actionIndex);
            const places=variants(action.state).slice(0,3);
            for(let i=0;i<places.length;i++) {
              const deadline=schedule.now()+Math.max(0,actionDeadline-schedule.now())/(places.length-i);
              const tested=await evaluateOption(places[i],trial,{...job,deadline},action.action==='restore'?pending.before.serial:null);
              if(tested.candidate&&(!best||tested.score>best.score))best=tested;
            }
            action.features={...action.features,verified:!!best,assessment:best?'trial':'unknown',actingPlayer:action.state.rules.playerIndex};
            action.score=null;
            if(best){action.features={...action.features,...best.features};
              const sign=action.action==='continue'?1:-1;
              action.score=sign*best.score;action.nominalScore=sign*best.nominalScore;
              action.executionScores=best.executionScores.map(row=>({...row,value:sign*row.value}));action.outcome=best.outcome;}
            choices.push({...action,label:{continue:'接手当前球形',again:'让对手从现位再打',restore:'复位后让对手重打'}[action.action]});
          }
          const verified=choices.filter(c=>c.features.verified);
          choices=verified.length?verified:choices.filter(c=>c.action==='continue');
        } else {
          kind=options.isOpening(state)?'opening':state.rules.freeBallAvailable?'free-ball':state.rules.inHand>0?'placement':'colour';
          let places=variants(state);
          // Touching colours need an explicit declaration, even for a play-away.
          if(state.touching?.requiresColourDeclaration)places=state.balls.filter(b=>b.active&&b.n>1).map(b=>({
            id:'colour-'+b.n,nominee:null,state:{...state,rules:{...state.rules,nominatedColour:b.n,nominationSource:'manual'}},
            score:null,features:{nominatedColour:b.n}}));
          for(let i=0;i<places.length;i++) {
            const place=places[i];
            if(!available(job))break;
            const deadline=schedule.now()+Math.max(0,job.deadline-schedule.now())/(places.length-i);
            await evaluateOption(place,trial,{...job,deadline});
            place.label=kind==='opening'?'D区薄红球开球':kind==='free-ball'?(place.nominee==null?'不选自由球':'指定自由球'):'安排本杆球位与目标';
            choices.push(place);
          }
          const verified=choices.filter(c=>c.candidate);
          choices=verified.length?verified:choices.slice(0,1);
        }
        if(epoch!==job.epoch)return;
        if(!choices.length)throw new Error('No legal turn choices available for AI');
        const shared=[0,1].filter(i=>choices.every(c=>c.executionScores?.some(row=>row.index===i)));
        for(const choice of choices){
          if(choice.nominalScore==null)continue;
          choice.score=shared.length?policy.aggregate(state,choice.executionScores.filter(row=>shared.includes(row.index)).map(row=>row.value)).score:choice.nominalScore;
          choice.features.comparisonBasis=shared.length?'common-execution':'common-nominal';choice.features.comparedSampleIndices=shared;
        }
        choices.sort((a,b)=>b.score-a.score);choices=choices.slice(0,6);
        clearDeadline();clearTimeout(wallTimer);
        try {onEvent('turn.search',{kind,elapsedMs:performance.now()-started,budgetMs:18000,scheduling:{...schedule.stats(),wallLimitMs},choices:choices.map(c=>({id:c.id,action:c.action,score:c.score,features:c.features,outcome:c.outcome,position:c.position,nominee:c.nominee}))});}catch(_){}
        job.phase='turn-selection';changed();
        const selected=await choose({kind,state:{ballOn:state.rules.ballOn,playerIndex:state.rules.playerIndex,
          scores:state.scores,remainingPoints:state.remainingPoints,skill:state.skill},choices,
          timeoutMs:Math.max(1000,90000-(schedule.now()-workStarted)),wallTimeoutMs:Math.max(1,180000-(performance.now()-started)),schedulerSession:schedule});
        if(epoch!==job.epoch)return;
        if(JSON.stringify(trial.snapshot())!==before)throw new Error('Position changed; AI decision is stale');
        lastResult={kind,choiceId:selected.choice.id,reason:selected.reason,options:choices.map(c=>({id:c.id,score:c.score,features:c.features}))};
        commit(selected.choice,kind,selected.reason,selected.source);
      } catch(error) {if(epoch===job.epoch){failed=true;onError(error);}}
      finally {clearDeadline();clearTimeout(wallTimer);schedule.close();if(active===job)active=null;changed();}
    }
    return {run,cancel,getStatus:status};
  }
  return {create};
})();

/* Local search shares one work budget; deliberate UI yields have a separate wall limit. */
const PCOLSearch=(()=>{
  const limit=(v,d,a,b)=>Number.isFinite(v)?Math.max(a,Math.min(b,v)):d;
  const key=s=>[s.nominatedColour||0,Math.atan2(s.shot.direction.z,s.shot.direction.x),s.shot.power,s.shot.vertical||0,s.shot.side||0,s.shot.elevation||0].map(x=>Math.round(x*100000)).join(':');
  function create({getTrial,getState,geometry,policy,skill,continuation,development,brain,scheduler}) {
    const scheduling=scheduler||(typeof PCOLComputeScheduler!=='undefined'?PCOLComputeScheduler:require('./compute-scheduler')).create();
    let active=null,lastResult=null;
    const stop=reason=>{if(active){active.reason=reason;active.schedule.cancel();if(active.inFlight)active.trial.cancel();}};
    function preparePlan(previous,context={}) {
      const snapshot=getTrial().snapshot(),state=getState(snapshot),brief=brain.analyze(state,geometry),actor=state.rules.playerIndex;
      const planCompliance=brain.compliance(state,previous?.expectedNext,geometry),last=context.lastOutcome;
      let reason=!previous?'new-visit':previous.actor!==actor?'actor-changed':
        !last||last.actor!==actor||!(last.score>0)||last.foulCode?'turn-changed':
        previous.objective!=='need-snookers'&&brief.task==='need-snookers'?'need-snookers':
        previous.lastWasDevelopment?'after-development':
        previous.coverageInsufficient&&(!planCompliance.met||!previous.expectedNext?.intent)?'coverage-insufficient':
        !planCompliance.met?'position-lost':!previous.expectedNext?.intent?'transition-not-covered':null;
      const continuedPlan=reason?null:{...previous,...brain.normalizePlan({primaryIntent:previous.expectedNext.intent,
        fallbackIntent:previous.fallbackIntent,reason:previous.reason},brief)};
      if(continuedPlan?.primaryIntent.task==='develop')reason='prepare-development';
      return {brief,preparedRoot:{fingerprint:JSON.stringify(snapshot),brief,style:state.style},needsReplan:!!reason,reason,planCompliance,continuedPlan};
    }
    async function run(options={}) {
      if(active)throw new Error('A candidate search is already running');
      const started=performance.now(),trial=options.trial||getTrial();
      if(trial.getStatus?.().busy)throw new Error('Wait for the current trial before searching');
      const before=options.snapshot||trial.snapshot(),fingerprint=JSON.stringify(before);
      const liveFingerprint=trial.fingerprint?.(),checkedRoots=new WeakSet();
      const state={...(options.state||getState(before))};state.rules={...state.rules};
      state.rootPlayerIndex=state.rules.playerIndex??0;state.style='unified';
      if(options.skill)state.skill=options.skill;
      const rules=state.rules,reviewReasons=[];
      if(!rules.ballOn||rules.ballOn===65535)reviewReasons.push('Search requires standard snooker rules');
      if(rules.freeBallReview||(rules.freeBallAvailable&&rules.freeBallNominee==null&&!rules.freeBallDeclined))reviewReasons.push('Resolve the free-ball choice first');
      if(state.touching?.requiresColourDeclaration&&rules.nominationSource!=='manual')reviewReasons.push('Declare the touching colour first');
      if(reviewReasons.length)return {status:'needs-ruling',reviewReasons,candidates:[],elapsedMs:performance.now()-started};
      const budgetMs=limit(options.budgetMs,45000,100,90000);
      const maxCandidates=Math.floor(limit(options.maxCandidates,96,1,288)),maxResults=Math.floor(limit(options.maxResults,4,1,4));
      const samples=Math.floor(limit(options.riskSamples,2,0,6)),branchCap=Math.floor(limit(options.continuationTrials,6,0,12));
      const riskCap=samples*8;
      const schedule=options.schedulerSession||scheduling.start({cooperativeYield:options.cooperativeYield});
      const initialScheduling=schedule.stats(),workStarted=schedule.now()-(performance.now()-started),deadline=workStarted+budgetMs;
      const job=active={trial,schedule,inFlight:false,reason:null,phase:'routes'};
      // The absolute guard is separate from effective compute time. Its margin
      // accommodates the normal 6 ms / 4 ms cadence without cutting search work.
      const wallLimitMs=Math.max(1000,budgetMs*2+1000);
      const clearDeadline=schedule.setDeadline(deadline,()=>stop('budget-exhausted'));
      const wallTimer=setTimeout(()=>stop('budget-exhausted'),Math.max(0,started+wallLimitMs-performance.now()));
      const cooperate=()=>job.reason?false:schedule.checkpoint();
      const accepted=[],cache=new Map(),outcomes=new Map(),evaluations=new Map(),sampled=new Map(),durations=[],stages=[];
      const counts={generated:0,tried:0,completed:0,incomplete:0,rejected:0,reused:0,recovery:0,refined:0,development:0,riskTrials:0,boundaryTrials:0,branchTrials:0,reasons:{ruling:0,foul:0,miss:0}};
      const current=()=>{try{return liveFingerprint!==undefined?trial.fingerprint()===liveFingerprint:JSON.stringify(trial.snapshot())===fingerprint;}catch(_){return false;}};
      const available=(reserve=0)=>!job.reason&&deadline-schedule.now()>reserve;
      const prepared=options.preparedRoot;
      const brief=brain&&(prepared&&!options.state&&prepared.fingerprint===fingerprint?prepared.brief:brain.analyze(state,geometry)),plan=brain?brain.normalizePlan(options.plan||{},brief):null;
      const searchIntent={primaryIntent:plan?.primaryIntent,fallbackIntent:plan?.fallbackIntent,used:'unified',fallbackTriggered:false,reason:'compare-independent-opportunities'};
      const intentFor=seed=>{
        if(!plan)return null;
        const edge=brief.transitionGraph?.find(e=>e.fromId===seed.targetIndex);
        return {task:seed.development?'develop':seed.kind==='attack'?'position':seed.kind==='escape'?'escape':brief.task==='need-snookers'?'need-snookers':'contain',
          targetId:seed.targetIndex,nextBallId:edge?.toId??null,sectorId:edge?.sectorId??null,preserveIds:(brief.preserveIds||[]).filter(i=>i!==seed.targetIndex)};
      };
      const intentWorks=c=>c.intentMet&&
        (!skill||!samples||(sampled.get(c.id)?.length||0)>=samples)&&
        !(sampled.get(c.id)||[]).some(row=>!row.evidence.legal||row.evidence.planCompliance?.intentMet===false);
      const policySession=policy?.createSession?.(geometry);
      const evaluatePolicy=policySession?((candidate,r)=>policySession.evaluate(state,candidate,r)):policy?.createEvaluator?.(state,geometry);
      const evaluate=(candidate,r,expectedNext=false)=>{
        const e=evaluatePolicy?evaluatePolicy(candidate,r):policy?policy.evaluate(state,candidate,r,geometry):geometry.evaluate(state,candidate,r);
        const assessment=brain&&candidate.intent?brain.assess(state,candidate,r,candidate.intent,geometry,brief,{expectedNext}):null;
        return {...e,score:e.score,features:{...e.features,...assessment?.features},assessment};
      };
      function evidence(r,e) {
        const v=r.adjudication,actor=state.rules.playerIndex??0;
        return {actor,nextActor:e.features?.nextPlayerIndex??r.nextContext?.playerIndex??r.nextSnapshot?.rules?.playerIndex??(v.continueBreak?actor:1-actor),
          legal:!v.foulCode,potted:r.potted||[],foulCode:v.foulCode||0,penalty:v.foulCode?Math.max(0,-(v.score||0)):0,
          points:v.score||0,components:{netPoints:e.netPoints??e.features?.netPoints??null,immediateCost:e.immediateCost??e.features?.immediateCost??null,
            futureValue:e.futureValue??e.features?.futureValue??null,terminalValue:e.terminalValue??e.features?.terminalValue??null},
          opponentSnookered:e.features?.opponentSnookered??null,selfSnookered:e.features?.selfSnookered??null,
          scoreBeforeBranches:e.score,branchDelta:0,scoreAfterBranches:e.score,continuation:{status:'unassessed',trials:0}};
      }
      const context=policy?.analyze(state);
      const aggregate=values=>policy?.aggregate?policy.aggregate(state,values):{score:values.reduce((a,b)=>a+b,0)/values.length,mean:values.reduce((a,b)=>a+b,0)/values.length,downside:0,riskPreference:0};
      const descriptor=c=>skill?.describe(state,c,options.skill||state.skill||'strong');
      const powerWindow=c=>Math.sqrt(3)*(c.skill||descriptor(c))?.powerSigma||0;
      const bufferedPower=(c,reachedPower,observedShortfall=0)=>{
        let power=reachedPower;
        for(let i=0;i<4;i++)power=reachedPower+Math.max(observedShortfall,powerWindow({...c,skill:null,shot:{...c.shot,power}}));
        return Math.min(.85,power+1e-5);
      };
      const sameDirection=(a,b)=>a&&b&&Math.abs(Math.atan2(a.x*b.z-a.z*b.x,a.x*b.x+a.z*b.z))<=.006;
      // The caller supplies only failures from this exact restored layout. Match the
      // stroke as well, so a failure cannot contaminate another ball, pocket or spin.
      const failuresFor=c=>(options.failureEvidence||[]).filter(f=>f.targetIndex===c.targetIndex&&
        (f.nominatedColour||0)===(c.nominatedColour||0)&&
        (c.kind!=='attack'||f.pocketIndex===c.pocketIndex)&&f.shot&&sameDirection(f.shot.direction,c.shot.direction)&&
        Math.abs((f.shot.vertical||0)-(c.shot.vertical||0))<=.08&&
        Math.abs(f.shot.power-c.shot.power)<=Math.max(.025,powerWindow(c))&&
        ((f.result?.firstHits?.length===0)||(c.kind==='attack'&&!(f.result?.score>0))));
      async function simulate(shot,nomination,parent=null) {
        if(!available())return null;
        if(!await cooperate()||!available())return null;
        if(!current()){job.reason='stale';return null;}
        job.inFlight=true;const t=performance.now();
        try {
          const opts={nominatedColour:nomination,maxWallMs:Math.min(5000,Math.max(1,deadline-schedule.now())),trace:brain?'cue':false};
          const pending=parent?trial.simulateFrom(parent,shot,opts):trial.simulate(shot,opts);
          const r=await schedule.wait(pending);
          if(r.stale||r.snapshot&&!checkedRoots.has(r.snapshot)&&JSON.stringify(r.snapshot)!==fingerprint){job.reason='stale';return null;}
          if(r.snapshot)checkedRoots.add(r.snapshot);
          return r;
        }catch(error){if(!current())job.reason='stale';if(job.reason)return null;throw error;}
        finally{durations.push(performance.now()-t);job.inFlight=false;}
      }
      async function stage(name,work) {
        job.phase=name;const t=performance.now(),n=durations.length,r=counts.rejected;
        await work();await cooperate();stages.push({name,elapsedMs:Math.round(performance.now()-t),trials:durations.length-n,rejected:counts.rejected-r});
      }
      async function explore(seeds,cap,reserve=0,stopAfterLegal=false) {
        counts.generated+=seeds.length;let used=0;
        for(const input of seeds) {
          const seedIntent=input.intent||intentFor(input);
          const seed=seedIntent?{...input,intent:seedIntent,intentSource:job.phase}:input;
          if(!available(reserve)||used>=cap||counts.tried>=maxCandidates)break;
          const k=key(seed);let r=cache.get(k);
          if(r){counts.reused++;if(accepted.some(c=>key(c)===k))continue;}
          else {used++;counts.tried++;r=await simulate(seed.shot,seed.nominatedColour);if(!r)break;}
          if(r.status!=='complete'){counts.incomplete++;continue;}
          counts.completed++;cache.set(k,r);
          if(!r.adjudication||!r.nextBalls){counts.rejected++;counts.reasons.ruling++;continue;}
          // Only settled legal nominal strokes may be executed; sampled fouls still count as risk.
          if(r.adjudication.foulCode){counts.rejected++;counts.reasons.foul++;continue;}
          if(seed.kind==='attack'&&!r.potted?.some(i=>i===seed.targetIndex||i===seed.potTargetIndex))counts.reasons.miss++;
          const e=evaluate(seed,r),cue=r.nextBalls.find(b=>b.n===0),v=r.adjudication;
          let effect=e.features?.effect||policy?.classify?.(state,seed,r,geometry)||(v.score>0?'attack':'contain');
          if(e.assessment?.features.problemHandled)effect='development';
          else if(v.score>0&&e.assessment?.features.cueSectorReached&&e.assessment?.features.nextRouteAvailable)
            effect=e.assessment.features.arrivalAligned?'position':'attack';
          const c={...seed,id:'shot-'+accepted.length,effect,expectedNext:e.assessment?.expectedNext,
            intentMet:e.assessment?.met??false,score:e.score,nominalScore:e.score,features:e.features,evidence:{nominal:{...evidence(r,e),planCompliance:e.assessment?.features},samples:[]},
            skill:descriptor(seed),stroke:r.stroke,actual:r.compiled?.actual,
            outcome:{score:v.score,foulCode:v.foulCode,potted:r.potted,firstHits:r.firstHits,nextBallOn:v.nextBallOn,
              continueBreak:v.continueBreak,nominatedColour:rules.ballOn===252?v.ballOnUsed:rules.nominatedColour,
              cue:cue&&{x:cue.x,y:cue.y,z:cue.z},simulatedSeconds:r.simulatedSeconds}};
          c.evidence.nominal.delivery={firstContactMade:r.firstHits?.includes(seed.targetIndex)??false,
            targetPotted:!!r.potted?.some(i=>i===seed.targetIndex||i===seed.potTargetIndex)};
          if(c.executionRepair)c.executionRepair={...c.executionRepair,lowErrorPower:Math.max(0,c.shot.power-powerWindow(c)),
            goalVerified:c.kind==='attack'?c.evidence.nominal.delivery.targetPotted:c.evidence.nominal.delivery.firstContactMade};
          accepted.push(c);outcomes.set(c.id,r);evaluations.set(c.id,e);
          if(stopAfterLegal)break;
        }
      }
      const routeKey=c=>geometry.routeKey?geometry.routeKey(c):[c.kind,c.targetIndex,c.pocketIndex,c.nominatedColour].join(':');
      function shortlist(count,fresh=false) {
        // This is a proposal queue, not a ranking of sampled and nominal values.
        const sorted=accepted.filter(c=>!fresh||(sampled.get(c.id)?.length||0)<samples).sort((a,b)=>b.nominalScore-a.nominalScore);
        const preferred=new Map();
        for(const c of sorted)if(c.executionRepair?.goalVerified&&!preferred.has(routeKey(c)))preferred.set(routeKey(c),c);
        const proposed=[...new Set(sorted.map(c=>preferred.get(routeKey(c))||c))];
        const chosen=[],routes=new Set(),targets=new Set();
        const add=c=>{if(c&&chosen.length<count&&!routes.has(routeKey(c))){chosen.push(c);routes.add(routeKey(c));targets.add(c.targetIndex);}};
        add(proposed[0]);add(proposed.find(c=>c.outcome.score>0));
        add(proposed.find(c=>['snooker','contain'].includes(c.effect)));
        for(const c of proposed)if(!targets.has(c.targetIndex))add(c);
        for(const c of proposed)add(c);
        // Once independent routes are covered, a refinement can challenge its parent.
        for(const c of sorted)if(chosen.length<count&&!chosen.includes(c))chosen.push(c);
        return chosen;
      }
      function updateRisk(c,indices=null) {
        const rows=(sampled.get(c.id)||[]).filter(row=>!indices||indices.includes(row.evidence.sampleIndex)),values=rows.map(r=>r.value),n=values.length;
        if(!n)return;
        const combined=aggregate(values),{mean,downside,riskPreference}=combined;
        const safeMisses=rows.filter(r=>r.features?.safeMiss===true).length;
        const costlyMisses=rows.filter(r=>r.features?.costlyMiss===true).length;
        const hasFoul=rows.some(r=>r.result.adjudication.foulCode);
        const twoWay=!!(rows.some(row=>row.result.adjudication.score>0)&&!hasFoul&&costlyMisses===0&&safeMisses>0);
        const effectiveDownside=downside,twoWayBonus=0;
        c.score=combined.score;
        c.features={...c.features,twoWay,safeMissRate:safeMisses/n,costlyMissRate:costlyMisses/n,twoWayBonus};
        c.evidence.samples=(sampled.get(c.id)||[]).map(r=>r.evidence);
        c.evidence[indices?'comparisonExecution':'execution']={score:c.score,sampleCount:n,sampleIndices:rows.map(row=>row.evidence.sampleIndex),availableSamples:sampled.get(c.id).length,coverage:n>=samples?'complete':'partial',sampleDesign:'common stratified three-axis pairs; additional pairs change error direction'};
        c.evidence.aggregation={source:'execution-samples',mean,downside,effectiveDownside,twoWayBonus,riskPreference,finalScore:c.score};
        c.risk={...c.risk,samples:n,incomplete:sampled.get(c.id).incomplete||0,legalRate:rows.filter(r=>!r.result.adjudication.foulCode).length/n,
          potRate:rows.filter(r=>r.result.adjudication.score>0).length/n,foulRate:rows.filter(r=>r.result.adjudication.foulCode).length/n,
          safeMissRate:safeMisses/n,costlyMissRate:costlyMisses/n,twoWay,
          meanScore:mean,downside,confidence:'limited',interpretation:'execution samples, not calibrated probabilities'};
      }
      async function risk(finalists,reserve,targetSamples=samples) {
        if(!skill||!samples)return;
        for(let n=0;n<targetSamples&&available(reserve);n++) {
          const values=skill.coordinates?skill.coordinates(n):(n%2?[.75,.75,.25]:[.25,.25,.75]);
          for(const c of finalists){if(!available(reserve)||counts.riskTrials>=riskCap)break;if(sampled.get(c.id)?.some(row=>row.evidence.sampleIndex===n))continue;let i=0;counts.riskTrials++;
            const r=await simulate(skill.perturb(c.shot,c.skill,()=>values[i++%3]),c.nominatedColour);
            const rows=sampled.get(c.id)||[];sampled.set(c.id,rows);
            if(r?.status!=='complete'||!r.adjudication||!r.nextBalls){rows.incomplete=(rows.incomplete||0)+1;continue;}
            const e=evaluate(c,r,false);rows.push({result:r,evaluated:e,value:e.score,features:e.features,evidence:{sampleIndex:n,powerUniformCoordinate:values[1],...evidence(r,e),
              delivery:{firstContactMade:r.firstHits?.includes(c.targetIndex)??false,targetPotted:!!r.potted?.some(i=>i===c.targetIndex||i===c.potTargetIndex)},planCompliance:e.assessment?.features}});
            if(values[1]<.5&&(!r.firstHits?.includes(c.targetIndex)||c.kind==='attack'&&!r.potted?.some(i=>i===c.targetIndex||i===c.potTargetIndex)))c.executionConcern={source:'sampled-low-power-failure'};
            updateRisk(c);
          }
        }
      }
      async function continuations(finalists,commonIndices) {
        if(!continuation||typeof trial.simulateFrom!=='function'||!branchCap)return;
        // Preserve the old total ceiling (four finalists times branchCap), shared by the entire verified pool.
        const commonSamples=commonIndices.length,continuationSession=continuation.createSession?.({policySession})||continuation;
        let remaining=4*branchCap;
        const branchCache=new Map();
        const trialBranch=async(parent,seed)=>{let hits=branchCache.get(parent);if(!hits){hits=new Map();branchCache.set(parent,hits);}const k=key(seed);if(hits.has(k))return hits.get(k);if(remaining<=0)return null;counts.branchTrials++;remaining--;const r=await simulate(seed.shot,seed.nominatedColour,parent);hits.set(k,r);return r;};
        const assessed=finalists.slice().sort((a,b)=>b.score-a.score).slice(0,4);
        for(const c of finalists)if(!assessed.includes(c)){
          c.horizon='unknown';c.evidence.continuation={score:null,coverage:'unknown',depth:0,samples:0};
        }
        const roots=assessed.reduce((n,c)=>n+(commonSamples||1),0);
        const capPerRoot=Math.min(branchCap,Math.floor(remaining/Math.max(1,roots)));
        for(const c of assessed) {
          c.shallowScore=c.score;
          const rows=sampled.get(c.id),branches=commonSamples?rows.filter(row=>commonIndices.includes(row.evidence.sampleIndex)):[{result:outcomes.get(c.id),evaluated:evaluations.get(c.id),value:c.score,evidence:c.evidence.nominal}];
          for(let i=0;i<branches.length&&remaining>0&&available();i++) {
            const row=branches[i];
            const planned=await continuationSession.evaluate({state,candidate:c,result:row.result,policySession,preparedEvaluation:row.evaluated,maxTrials:Math.min(capPerRoot,remaining),canContinue:()=>available(),
              simulateFrom:trialBranch});
            Object.assign(row.evidence,{branchDelta:planned.scoreDelta,scoreAfterBranches:row.value+planned.scoreDelta,continuation:planned.summary});
            if(i===0)c.plan={...planned.summary,source:commonSamples?'execution-sample':'nominal',sampleIndex:commonSamples?row.evidence.sampleIndex:null};
          }
          const depth=branches[0]?.evidence.continuation.depth;
          const covered=branches.every(row=>row.evidence.continuation.coverage==='covered'&&row.evidence.continuation.depth===depth);
          c.horizon=covered?'covered':'unknown';
          if(covered){
            c.continuationScore=aggregate(branches.map(row=>row.evidence.scoreAfterBranches)).score;
          }
          c.evidence.continuation={score:c.continuationScore??null,coverage:covered?'complete':branches.some(row=>row.evidence.continuation.trials>0)?'partial':'unknown',depth,samples:branches.length};
          c.evidence.comparison={...c.evidence.comparison,horizon:c.horizon};
        }
        // With one child per error endpoint, selectively extend two leading independent routes.
        // Reuse their first layer and deepen every sample, including misses; no best-sample cherry-picking.
        if(capPerRoot===1&&remaining>0){
          const ordered=finalists.filter(c=>c.horizon==='covered').sort((a,b)=>b.continuationScore-a.continuationScore),seen=new Set();let probed=0;
          for(const c of ordered){
            if(probed>=2||remaining<(commonSamples||1)||!available())break;
            if(c.horizon!=='covered'||seen.has(routeKey(c)))continue;seen.add(routeKey(c));probed++;
            const rows=sampled.get(c.id),branches=commonSamples?rows.filter(row=>commonIndices.includes(row.evidence.sampleIndex)):[{result:outcomes.get(c.id),evaluated:evaluations.get(c.id),value:c.score,evidence:c.evidence.nominal}];
            const probes=[];
            for(const row of branches){const p=await continuationSession.evaluate({state,candidate:c,result:row.result,policySession,preparedEvaluation:row.evaluated,maxTrials:2,depth:2,breadth:1,canContinue:()=>available(),simulateFrom:trialBranch});
              probes.push({...p,score:row.value+p.scoreDelta});}
            c.evidence.secondLayer=probes.map(p=>({score:p.score,summary:p.summary}));
            c.evidence.secondLayerComparison={basis:'diagnostic-only',reason:'second layer is not shared by the comparison pool'};
          }
        }
      }
      async function softControls(reserveMs) {
        for(const seed of geometry.softContacts?.(state)||[]) {
          let low=0,high=.28,reached=false;
          // Native contact, not a distance-to-power guess, brackets the least force that reaches this ball.
          for(let i=0;i<3&&available(reserveMs)&&counts.tried<maxCandidates;i++) {
            const candidate={...seed,shot:{...seed.shot,power:(low+high)/2}};
            await explore([candidate],1,reserveMs);
            const r=cache.get(key(candidate));
            if(r?.firstHits?.includes(seed.targetIndex)){high=candidate.shot.power;reached=true;}
            else low=candidate.shot.power;
          }
          if(reached&&skill&&available(reserveMs)&&counts.tried<maxCandidates){
            const power=bufferedPower(seed,high),candidate={...seed,shot:{...seed.shot,power},
              executionRepair:{source:'native-contact-bracket',failedPower:low,reachedPower:high,
                lowErrorPower:power-powerWindow({...seed,shot:{...seed.shot,power}})}};
            await explore([candidate],1,reserveMs);
          }
        }
      }
      async function boundaryProbe(c,reserveMs) {
        const window=powerWindow(c);if(!window||!available(reserveMs)||counts.tried>=maxCandidates)return;
        const candidate={...c,shot:{...c.shot,power:Math.max(0,c.shot.power-window)}},k=key(candidate);
        let r=cache.get(k);
        if(r)counts.reused++;
        else {counts.tried++;counts.generated++;counts.boundaryTrials++;r=await simulate(candidate.shot,c.nominatedColour);if(r?.status==='complete')cache.set(k,r);}
        const settled=r?.status==='complete'&&r.adjudication&&r.nextBalls;
        if(settled)counts.completed++;else counts.incomplete++;
        const goal=settled&&!r.adjudication.foulCode&&(c.kind==='attack'?r.potted?.some(i=>i===c.targetIndex||i===c.potTargetIndex):r.firstHits?.includes(c.targetIndex));
        c.evidence.robustness={basis:'isolated-power-support-boundary',status:settled?'complete':'incomplete',
          testedPower:candidate.shot.power,goalVerified:!!goal,score:r?.adjudication?.score,foulCode:r?.adjudication?.foulCode,
          firstHits:r?.firstHits,potted:r?.potted,interpretation:'boundary diagnostic, excluded from execution mean'};
        if(settled&&!goal&&c.evidence.nominal.delivery[c.kind==='attack'?'targetPotted':'firstContactMade'])
          c.executionBoundary={source:'native-power-boundary',failedPower:candidate.shot.power,reachedPower:c.shot.power,
            repairPower:bufferedPower(c,c.shot.power)};
      }
      try {
        const useFixedReserve=budgetMs>=4000&&(skill&&samples>0||continuation);
        const finalReserveMs=useFixedReserve?Math.min(9000,budgetMs*.20):0;
        const coverageReserveMs=useFixedReserve?Math.min(15000,budgetMs*.32):0;
        const fallbackReserveMs=useFixedReserve?Math.min(24000,budgetMs*.46):0;
        const reserve=(phase='default')=>{
          const dynamic=Math.min(12000,Math.max(0,deadline-schedule.now())*.3);
          if(!useFixedReserve)return dynamic;
          if(phase==='primary')return Math.max(fallbackReserveMs,dynamic);
          if(phase==='fallback')return Math.max(coverageReserveMs,dynamic*.8);
          return finalReserveMs;
        };
        const baseSeeds=geometry.generate(state);
        const intentSeeds=intent=>{
          const developed=intent.task==='develop'&&development?development.generate(state,geometry):[];
          const directed=brain.directed(state,developed.length?developed:baseSeeds,intent,geometry,brief);
          return directed.concat(developed,baseSeeds.filter(c=>c.targetIndex===intent.targetId));
        };
        // Cover real opportunities before spending on a visit plan's refinements.
        await stage('coverage',()=>explore(baseSeeds,Math.min(36,maxCandidates),reserve('primary')));
        if(plan&&available(reserve('fallback'))){
          const intents=[plan.primaryIntent,plan.fallbackIntent];
          for(const c of shortlist(3))if(c.intent&&!intents.some(i=>i.task===c.intent.task&&i.targetId===c.intent.targetId))intents.push(c.intent);
          const groups=intents.map(intent=>intentSeeds(intent).map(c=>({...c,intent:{...intent,targetId:c.targetIndex}})));
          const directed=[];
          for(let i=0;i<Math.max(0,...groups.map(g=>g.length));i++)for(const group of groups)if(group[i])directed.push(group[i]);
          await stage('position-options',()=>explore(directed,18,reserve('fallback')));
        }
        // Validate early proposals before refinement; their evidence stays eligible.
        await stage('route-evidence',()=>risk(shortlist(4),reserve('coverage')));
        if(development&&available(reserve()))await stage('development',async()=>{const seeds=development.generate(state,geometry);counts.development=seeds.length;await explore(geometry.diverse?geometry.diverse(seeds):seeds,8,reserve());});
        if(geometry.softContacts&&available(reserve()))await stage('soft-control',()=>softControls(reserve()));
        if(!accepted.some(c=>!c.outcome.foulCode)&&geometry.generateRecovery&&available(reserve()))await stage('recovery',async()=>{const seeds=geometry.generateRecovery(state);counts.recovery=seeds.length;await explore(seeds,18,reserve());});
        if(!accepted.length&&geometry.generateRecovery&&available())await stage('multi-cushion-recovery',async()=>{const seeds=geometry.generateRecovery(state,{multiCushion:true});counts.recovery+=seeds.length;await explore(seeds,maxCandidates-counts.tried,0,true);});
        if(geometry.refine&&available(reserve('coverage')))await stage('refinement',async()=>{
          const parents=[],routes=new Set();
          for(const c of accepted.filter(c=>failuresFor(c).length).concat(shortlist(3))){
            if(parents.length===3)break;if(routes.has(routeKey(c)))continue;parents.push(c);routes.add(routeKey(c));
          }
          for(const c of parents){
            const failures=failuresFor(c),count=failures.reduce((sum,f)=>sum+Math.max(1,f.count||1),0);
            if(count)c.evidence.restoredFailures={count,source:'same-layout-delivery',matching:'target, nomination, pocket and stroke'};
            if(c.evidence.nominal.delivery[c.kind==='attack'?'targetPotted':'firstContactMade']&&
              (c.kind==='attack'||c.softContact||count||c.executionConcern)&&!c.executionRepair)await boundaryProbe(c,reserve('coverage'));
            const shortfall=Math.max(0,...failures.map(f=>f.shot.power-(f.actualShot?.power??f.shot.power)));
            if(count>=2&&shortfall>0&&c.evidence.nominal.delivery[c.kind==='attack'?'targetPotted':'firstContactMade'])
              c.executionBoundary={...c.executionBoundary,source:c.executionBoundary?.source||'repeated-delivery-failure',
                reachedPower:c.shot.power,repairPower:bufferedPower(c,c.shot.power,shortfall),failureCount:count};
          }
          const groups=parents.map(c=>geometry.refine(state,{...c,contacts:outcomes.get(c.id)?.contacts})),seeds=[];
          // Spend the existing twelve refinements across routes before second variants.
          for(let i=0;i<Math.max(0,...groups.map(g=>g.length));i++)for(const group of groups)if(group[i])seeds.push(group[i]);
          counts.refined=seeds.length;await explore(seeds,12,reserve('coverage'));});
        const riskReserve=continuation?Math.min(5000,Math.max(0,deadline-schedule.now())*.2):0;
        let contenders=accepted.filter(c=>(sampled.get(c.id)?.length||0)>=samples&&samples>0).sort((a,b)=>b.score-a.score);
        // A new independent route or repaired stroke may challenge the tested pool.
        const fresh=shortlist(2,true).filter(c=>!contenders.length||c.nominalScore>=contenders[0].score||c.executionRepair?.goalVerified);
        if(fresh.length)await stage('risk',()=>risk(fresh,riskReserve));
        contenders=accepted.filter(c=>(sampled.get(c.id)?.length||0)>=samples&&samples>0).sort((a,b)=>b.score-a.score);
        let comparedPair=[];
        if(contenders.length>1&&available(riskReserve)){
          const pair=contenders.slice(0,2),gap=pair[0].score-pair[1].score;
          const spread=Math.max(...pair.map(c=>{const v=sampled.get(c.id).map(r=>r.value);return Math.max(...v)-Math.min(...v);}));
          if(gap<=Math.max(1,spread)||pair.some(c=>c.executionConcern||c.development)){
            const extra=2*Math.floor((riskCap-counts.riskTrials)/4),target=Math.min(6,samples+extra);
            if(target>samples){comparedPair=pair;await stage('decision-evidence',()=>risk(pair,riskReserve,target));}
          }
        }
        // Every earlier verified stroke stays eligible, even if its refined replacement fails.
        const verified=accepted.filter(c=>(sampled.get(c.id)?.length||0)>0);
        const comparable=verified.length?verified:shortlist(4);
        const commonIndices=verified.length?sampled.get(verified[0].id).map(row=>row.evidence.sampleIndex).filter(i=>i<samples&&verified.every(c=>sampled.get(c.id).some(row=>row.evidence.sampleIndex===i))):[];
        for(const c of comparable) {
          if(commonIndices.length)updateRisk(c,commonIndices);else {c.score=c.nominalScore;c.evidence.aggregation={source:'common-nominal',finalScore:c.score};}
          c.evidence.comparison={basis:commonIndices.length?'common-shallow':'common-nominal',sampleIndices:commonIndices,shallowScore:c.score};
          const n=sampled.get(c.id)?.length||0;
          c.risk={...c.risk,samples:commonIndices.length,availableSamples:n,comparedSamples:commonIndices.length,coverage:!samples||!skill?'disabled':n>=samples?'complete':n?'partial':'unassessed'};
        }
        await stage('continuations',()=>continuations(comparable,commonIndices));
        for(const c of comparable)if(!c.evidence.aggregation)c.evidence.aggregation={source:'nominal',finalScore:c.score};
        let status=job.reason||(schedule.now()>=deadline?'budget-exhausted':counts.tried>=maxCandidates?'candidate-limit':'complete');
        if(!current())status='stale';
        if(!comparable.length&&!['stale','cancelled'].includes(status))status='no-candidates';
        const sorted=durations.slice().sort((a,b)=>a-b),quantile=q=>sorted.length?Math.round(sorted[Math.min(sorted.length-1,Math.floor((sorted.length-1)*q))]):null;
        counts.trialMs={count:sorted.length,median:quantile(.5),p90:quantile(.9)};
        const ranking=(a,b)=>Number(!!a.features?.mathematicallyDead)-Number(!!b.features?.mathematicallyDead)||b.score-a.score;
        comparable.sort(ranking);
        // Incomplete horizons are barriers, not zero-valued rivals. Reorder only adjacent
        // fully covered peers at the same depth, preserving the common shallow order elsewhere.
        for(let i=0;i<comparable.length;){
          if(comparable[i].horizon!=='covered'){i++;continue;}
          const depth=comparable[i].evidence.continuation.depth;let j=i+1;
          while(j<comparable.length&&comparable[j].horizon==='covered'&&comparable[j].evidence.continuation.depth===depth&&
            !!comparable[j].features?.mathematicallyDead===!!comparable[i].features?.mathematicallyDead)j++;
          if(j-i>1){const peers=comparable.slice(i,j).sort((a,b)=>b.continuationScore-a.continuationScore);
            for(const c of peers)c.evidence.comparison.basis='common-bounded-horizon';comparable.splice(i,j-i,...peers);}
          i=j;
        }
        if(comparedPair.length===2&&comparedPair.every(c=>comparable.slice(0,2).includes(c))){
          const indices=sampled.get(comparedPair[0].id).map(r=>r.evidence.sampleIndex).filter(i=>sampled.get(comparedPair[1].id).some(r=>r.evidence.sampleIndex===i));
          // Do not replace a completed continuation comparison with a shallower one.
          if(indices.length>commonIndices.length&&!comparedPair.every(c=>c.horizon==='covered')){
            for(const c of comparedPair){const value=aggregate(sampled.get(c.id).filter(r=>indices.includes(r.evidence.sampleIndex)).map(r=>r.value));
              c.evidence.pairedExecution={...value,sampleIndices:indices,peerId:comparedPair.find(p=>p!==c).id};}
            const peers=comparedPair.slice().sort((a,b)=>Number(!!a.features?.mathematicallyDead)-Number(!!b.features?.mathematicallyDead)||b.evidence.pairedExecution.score-a.evidence.pairedExecution.score);
            comparable.splice(0,2,...peers);for(const c of peers)c.evidence.comparison.basis='common-paired-execution';
          }
        }
        const chosen=comparable[0],categoryBest={};
        // Next-visit plans do not affect this shot's score, coverage or ranking.
        // Build them only for the returned candidates, after comparison is complete.
        const finalists=comparable.slice(0,maxResults);
        if(brain)for(const c of finalists)if(c.intent)
          c.expectedNext=brain.assess(state,c,outcomes.get(c.id),c.intent,geometry,brief,{expectedNext:true}).expectedNext;
        searchIntent.selected=chosen?.intentSource||null;
        searchIntent.achieved=!!chosen&&intentWorks(chosen);
        for(const c of accepted.slice().sort((a,b)=>b.score-a.score))if(!categoryBest[c.effect])categoryBest[c.effect]={
          id:c.id,effect:c.effect,targetIndex:c.targetIndex,score:c.score,selected:comparable.includes(c),
          cue:c.outcome.cue,points:c.outcome.score,intentMet:c.intentMet,opponentChance:c.features.opponentChance,
          nextRouteAvailable:c.features.nextRouteAvailable,snookered:c.features.opponentSnookered};
        const activePlan=plan&&{...plan,actor:rules.playerIndex,round:rules.nRounds,objective:context?.objective,
          expectedNext:chosen?.expectedNext,lastWasDevelopment:chosen?.effect==='development'||chosen?.intent?.task==='develop',
          coverageInsufficient:!chosen||(!intentWorks(chosen)&&!(chosen.outcome?.score>0&&chosen.outcome?.continueBreak&&chosen.expectedNext?.intent)),
          selectedIntent:chosen?.intent};
        const elapsedMs=performance.now()-started,metrics=schedule.stats(),waitMs=metrics.waitMs-initialScheduling.waitMs;
        lastResult={status,budgetMs,elapsedMs,scheduling:{enabled:metrics.enabled,yields:metrics.yields-initialScheduling.yields,waitMs,budgetElapsedMs:elapsedMs-waitMs,wallLimitMs},counts,stages,tactical:policy?.analyze(state),selected:chosen,
          activePlan,searchIntent,categoryBest,planCompliance:chosen?.evidence.nominal.planCompliance,
          position:{evolution:before.serial?.evolution,round:rules.nRounds,playerIndex:rules.playerIndex},
          riskCoverage:comparable.map(c=>({id:c.id,samples:c.risk.samples,coverage:c.risk.coverage})),
          candidates:['stale','cancelled'].includes(status)?[]:finalists};
        lastResult.shortlist=lastResult.candidates.map(c=>({id:c.id,kind:c.kind,targetIndex:c.targetIndex,pocketIndex:c.pocketIndex,score:c.score,samples:c.risk?.samples||0,plan:c.plan?.status}));
        // Opt-in complete local evidence. Never expose hidden ranking to the model player.
        if(typeof options.onAudit==='function')options.onAudit(structuredClone({
          selected:chosen||null,ranking:comparable,accepted,
          outcomes:[...outcomes].map(([id,result])=>({id,result})),status,counts,stages
        }));
        return lastResult;
      }finally{clearDeadline();clearTimeout(wallTimer);if(!options.schedulerSession)schedule.close();active=null;}
    }
    return {run,preparePlan,cancel:()=>stop('cancelled'),getStatus:()=>({busy:!!active,phase:active?.phase,lastResult:lastResult&&{status:lastResult.status,elapsedMs:lastResult.elapsedMs,count:lastResult.candidates.length,counts:lastResult.counts}})};
  }
  return {create};
})();

const PCOLLocalAI = (() => {
  const failure=(code,message)=>Object.assign(new Error(message),{code});
  const ballNames=['白球','红球','黄球','绿球','棕球','蓝球','粉球','黑球'];
  const describeBall=b=>b&&({id:b.i,name:ballNames[b.n],points:b.n});
  const round=value=>{
    if(typeof value==='number')return Number.isFinite(value)?Math.round(value*1000)/1000:null;
    if(Array.isArray(value))return value.map(round);
    if(value&&typeof value==='object')return Object.fromEntries(Object.entries(value).map(([k,v])=>[k,round(v)]));
    return value;
  };
  function create({getSearch,getTrial,getContext,onEvent=()=>{},onChange=()=>{},scheduler}) {
    const scheduling=scheduler||(typeof PCOLComputeScheduler!=='undefined'?PCOLComputeScheduler:require('./compute-scheduler')).create();
    let activePlan=null,active=null,state={busy:false,phase:'idle',lastDecision:null};
    let delivery=null,failurePosition=null,failures=[];
    // A restored table changes the round and scores, but retains its geometry and legal targets.
    const positionKey=snapshot=>JSON.stringify([snapshot.sceneId||null,
      ...['ballOn','playerIndex','inHand','nominatedColour','freeBallNominee','freeBallAvailable','freeBallDeclined','respottedBlack'].map(k=>snapshot.rules?.[k]??null),
      (snapshot.balls||[]).filter(b=>b.active!==false).slice().sort((a,b)=>a.i-b.i).map(b=>[b.i,b.n,b.x,b.y,b.z,b.r])]);
    const failureEvidence=snapshot=>failurePosition===positionKey(snapshot)?structuredClone(failures):[];
    function rememberDelivery(snapshot,candidate,actualShot) {
      const position=positionKey(snapshot);
      if(position!==failurePosition){failures=[];failurePosition=position;}
      delivery=structuredClone({shot:candidate.shot,kind:candidate.kind,targetIndex:candidate.targetIndex,
        pocketIndex:candidate.pocketIndex,nominatedColour:candidate.nominatedColour,actualShot});
    }
    function recordOutcome(result) {
      const played=delivery;delivery=null;if(!played)return;
      if(!result.foulCode&&(result.score>0||played.kind!=='attack')){failures=[];return;}
      const evidence={...played,result:{score:result.score,foulCode:result.foulCode,firstHits:result.firstHits||[]},count:1};
      failures.push(evidence);if(failures.length>8)failures.shift();
      emit('execution.feedback',{...evidence,retained:failures.length});
    }
    const emit=(kind,data)=>{try{onEvent(kind,round(data));}catch(_){}};
    const update=patch=>{state={...state,...patch};try{onChange({...state});}catch(_){}};
    const fingerprint=()=>JSON.stringify(getTrial().snapshot());
    const compact=list=>[...list].sort((a,b)=>String(a.id).localeCompare(String(b.id))).slice(0,12).map(c=>round({id:c.id,kind:c.kind,label:c.label,targetIndex:c.targetIndex,
      target:describeBall(getContext().balls?.find(b=>b.i===c.targetIndex)),score:c.score,features:c.features,risk:c.risk,plan:c.plan,evidence:c.evidence,outcome:c.outcome,action:c.action}));
    const score=c=>Number.isFinite(c.score)?c.score:0;
    function guard(job,before) {
      if(job.cancelled)throw failure('cancelled','AI decision cancelled');
      const activeWait=(job.schedule?.stats().waitMs||0)-(job.waitStarted||0);
      if(job.timedOut||Date.now()-activeWait>=job.deadline||Date.now()>=job.wallDeadline)throw failure('timeout','AI decision deadline exceeded');
      if(fingerprint()!==before)throw failure('stale','Position changed; AI decision is stale');
    }
    function cancellable(promise,signal) {
      return new Promise((resolve,reject)=>{
        const abort=()=>reject(failure('cancelled','AI decision cancelled'));
        if(signal.aborted)return abort();signal.addEventListener('abort',abort,{once:true});
        Promise.resolve(promise).then(resolve,reject).finally(()=>signal.removeEventListener('abort',abort));
      });
    }
    async function decide(options={}) {
      if(active)throw failure('busy','An AI decision is already running');
      const started=Date.now(),schedule=scheduling.start({cooperativeYield:options.cooperativeYield});
      const job={controller:new AbortController(),search:getSearch(),schedule,deadline:started+90000,wallDeadline:started+180000,cancelled:false};
      active=job;update({busy:true,phase:'search',lastDecision:null,error:null,errorClassification:null});
      const timeout=()=>{job.timedOut=true;job.controller.abort();job.search.cancel();schedule.cancel();};
      const clearDeadline=schedule.setDeadline(schedule.now()+90000,timeout),wallTimer=setTimeout(timeout,180000);
      let search;
      try {
        const before=fingerprint(),context=round(getContext());
        const {plan:unusedPlan,...localOptions}=options;
        const preparation=job.search.preparePlan
          ?await cancellable(job.search.preparePlan(activePlan,{lastOutcome:context.lastOutcome}),job.controller.signal)
          :{brief:{},needsReplan:true,reason:'missing-preparation'};
        guard(job,before);
        emit('plan.check',{needsReplan:preparation.needsReplan,reason:preparation.reason,planCompliance:preparation.planCompliance,previousPlan:activePlan});
        const defaultPlan=preparation.brief?.defaultPlan||(preparation.brief?.defaultPrimary&&preparation.brief?.defaultFallback?{primaryIntent:preparation.brief.defaultPrimary,fallbackIntent:preparation.brief.defaultFallback}:null);
        const continued=preparation.needsReplan===false;
        const plan=continued?(preparation.continuedPlan||activePlan||defaultPlan):defaultPlan;
        const source=continued?'continued-plan':'local-plan',reason=preparation.reason||'';
        const planningElapsedMs=Date.now()-started;
        const feedback=failureEvidence(getTrial().snapshot());
        search=await cancellable(job.search.run({...localOptions,schedulerSession:schedule,fastPlan:continued,preparedRoot:preparation.preparedRoot,failureEvidence:feedback,
          budgetMs:Math.max(1,Math.min(Number(options.budgetMs)||65000,65000,job.deadline-Date.now()+schedule.stats().waitMs-500)),plan}),job.controller.signal);
        emit('search.complete',{status:search.status,elapsedMs:search.elapsedMs,totalElapsedMs:Date.now()-started,budgetMs:search.budgetMs,scheduling:search.scheduling,counts:search.counts,stages:search.stages||search.counts,position:search.position,activePlan:search.activePlan,searchIntent:search.searchIntent,planCompliance:search.planCompliance,categoryBest:search.categoryBest,candidates:compact(search.candidates||[])});
        guard(job,before);
        if(['stale','cancelled','needs-ruling'].includes(search.status))throw failure(search.status,'AI search '+search.status);
        if(!search.candidates?.length)throw failure('no-candidates','No legal AI candidates available');
        const candidate=search.selected||search.candidates[0];
        activePlan=search.activePlan||(plan?{...plan,actor:context.playerIndex,round:search.position?.round??context.nRounds,
          objective:search.tactical?.objective,expectedNext:candidate.expectedNext||null,lastWasDevelopment:candidate.intent?.task==='develop',
          coverageInsufficient:search.planCompliance?.coverageInsufficient===true}:null);
        const result={candidate,reason,source,shortlist:compact(search.candidates),activePlan,
          search:{status:search.status,elapsedMs:search.elapsedMs,scheduling:search.scheduling,counts:search.counts,stages:search.stages,searchIntent:search.searchIntent,planCompliance:search.planCompliance,categoryBest:search.categoryBest}};
        emit('selection.complete',{kind:'shot',id:candidate.id,source,reason,score:candidate.score,
          elapsedMs:planningElapsedMs,totalElapsedMs:Date.now()-started});
        update({phase:'ready',lastDecision:{candidateId:result.candidate.id,source:result.source,reason:result.reason}});return result;
      }catch(error){
        if(job.timedOut&&!job.cancelled)error=failure('timeout','AI decision deadline exceeded');
        if(!search)emit('search.complete',{status:error.code||'error',elapsedMs:Date.now()-started,candidates:[],error:error.message});
        update({phase:error.code==='cancelled'?'idle':'error',error:error.message,errorClassification:error.code||'search-failure'});
        emit('decision.failure',{classification:error.code||'search-failure',error:error.message});throw error;
      }finally{clearDeadline();clearTimeout(wallTimer);schedule.close();active=null;update({busy:false});}
    }
    async function chooseTurn({kind,choices,timeoutMs=90000,wallTimeoutMs=180000,schedulerSession}) {
      if(active)throw failure('busy','An AI decision is already running');
      if(!Array.isArray(choices)||!choices.length)throw failure('no-candidates','No legal turn choices available');
      const started=Date.now(),job={controller:new AbortController(),schedule:schedulerSession,waitStarted:schedulerSession?.stats().waitMs||0,
        deadline:started+Math.max(1,Math.min(90000,Number(timeoutMs)||90000)),wallDeadline:started+Math.max(1,Math.min(180000,Number(wallTimeoutMs)||180000)),cancelled:false};
      activePlan=null;active=job;update({busy:true,phase:'selection',error:null,errorClassification:null,lastDecision:null});
      try {
        const before=fingerprint();
        const choice=[...choices].sort((a,b)=>score(b)-score(a))[0];
        await Promise.resolve();
        guard(job,before);
        const source='local',reason='Local search selected the highest-scoring legal option.';
        emit('selection.complete',{kind,id:choice.id,source,reason,score:choice.score,localBestId:choice.id,
          changedLocalChoice:false,elapsedMs:Date.now()-started,candidateIds:choices.map(c=>c.id)});
        update({phase:'ready',lastDecision:{choiceId:choice.id,source,reason}});
        return {choice,reason,source};
      }catch(error){
        update({phase:error.code==='cancelled'?'idle':'error',error:error.message,errorClassification:error.code||'turn-failure'});
        emit('decision.failure',{kind,classification:error.code||'turn-failure',error:error.message});throw error;
      }finally{active=null;update({busy:false});}
    }
    return {decide,chooseTurn,rememberDelivery,recordOutcome,failureEvidence,
      resetExperience:()=>{delivery=null;failurePosition=null;failures=[];},
      clearPlan:()=>{activePlan=null;},getPlan:()=>activePlan&&JSON.parse(JSON.stringify(activePlan)),setPlan:plan=>{activePlan=plan&&JSON.parse(JSON.stringify(plan));},cancel:()=>{
      if(!active)return;active.cancelled=true;active.controller.abort();active.search?.cancel();active.schedule?.cancel();
    },getStatus:()=>({...state,lastDecision:state.lastDecision&&{...state.lastDecision}})};
  }
  return {create};
})();

const PCOLDecisionWorkerSource = "/* Per-stroke Float64 trajectory. Native ball identity/radius are immutable;\n * every physics/contact sample retains position and active state unchanged.\n * Object rows are materialized only for explicit external trace exports. */\nconst PCOLShotTrace = (() => {\n  function create(nativeBalls, {cap = 15000, seconds = false, chunkSize = 128} = {}) {\n    const metadata = nativeBalls.map(b => ({i:b.index,n:b.number,r:b.radius}));\n    const slots = new Map();\n    for(let i=0;i<metadata.length;i++)if(!slots.has(metadata[i].i))slots.set(metadata[i].i,i);\n    const stride = 1 + 4*metadata.length, chunks = [];\n    const last = {t:0,x:0,y:0,z:0};\n    let length = 0;\n    function sample(balls, time) {\n      if(length >= cap)return null;\n      const chunkIndex = Math.floor(length/chunkSize), offset = (length%chunkSize)*stride;\n      let data = chunks[chunkIndex];\n      if(!data)data=chunks[chunkIndex]=new Float64Array(Math.min(chunkSize,cap-chunkIndex*chunkSize)*stride);\n      data[offset]=time;\n      for(let i=0;i<metadata.length;i++) {\n        const b=balls[i],p=b.position,k=offset+1+i*4;\n        data[k]=p.x;data[k+1]=p.y;data[k+2]=p.z;data[k+3]=b.active===false?0:1;\n      }\n      last.t=length++;last.x=data[offset+1];last.y=data[offset+2];last.z=data[offset+3];\n      return last;\n    }\n    function readCue(index, out = {}) {\n      const data=chunks[Math.floor(index/chunkSize)],offset=(index%chunkSize)*stride;\n      out.t=index;out.x=data[offset+1];out.y=data[offset+2];out.z=data[offset+3];\n      if(seconds)out.seconds=data[offset];\n      return out;\n    }\n    function readBall(index, fallback, out = {}) {\n      const slot=slots.get(fallback.i);\n      if(slot===undefined){Object.assign(out,fallback);out.active=false;return out;}\n      const data=chunks[Math.floor(index/chunkSize)],offset=(index%chunkSize)*stride+1+slot*4;\n      const m=metadata[slot];\n      out.i=m.i;out.n=m.n;out.r=m.r;\n      out.x=data[offset];out.y=data[offset+1];out.z=data[offset+2];out.active=data[offset+3]!==0;\n      return out;\n    }\n    function toArray() {\n      const rows=new Array(length);\n      for(let i=0;i<length;i++) {\n        const row=readCue(i);\n        row.balls=metadata.map(b=>readBall(i,b));rows[i]=row;\n      }\n      return rows;\n    }\n    function toCueArray() {\n      const rows=new Array(length),point={};\n      for(let i=0;i<length;i++) {\n        readCue(i,point);rows[i]={t:point.t,x:point.x,z:point.z};\n      }\n      return rows;\n    }\n    return {get length(){return length;},sample,readCue,readBall,toArray,toCueArray,toJSON:toArray};\n  }\n  return {create};\n})();\n\n/* PCOL rule helpers. x/z are cloth coordinates; y is height. No game mutation.\n * WPBSA 2024-25: definitions 17/20, play 3/4/7/8/11/12.\n * https://wpbsa.com/wp-content/uploads/2198_WPBSA-Rulebook-2024-25.pdf\n */\nconst PCOLCore = (() => {\n  'use strict';\n  const RADIUS = 0.02625;\n  const RED = 2, COLOUR_ALL = 252;\n  const FOUL = Object.freeze({MISS:1, FIRST_HIT:2, POTTING:4, CUE_POTTED:8, OFF_TABLE:16, JUMP:32, FREE_BALL_SNOOKER:64, PUSH:128, DOUBLE_HIT:256});\n  // Referee tolerance: the observed 0.188 mm resting gap counts as touching.\n  // Keep physical spotting clearance independent of this judgement tolerance.\n  const CONTACT_EPS = 1e-5, TOUCH_EPS = 2e-4;\n  const unique = a => [...new Set(a)];\n  const radius = (b, fallback = RADIUS) => b.r > 0 ? b.r : fallback;\n  const hypot2 = (a, b) => Math.hypot(a.x - b.x, a.z - b.z);\n  const active = b => b.active !== false;\n  const ballOnNumbers = mask => [1,2,3,4,5,6,7].filter(n => (mask & (1 << n)) !== 0);\n\n  // PCOL's x axis runs from Baulk to the black end. Leave a small gap beyond\n  // the touching tolerance, and only consider Baulk after the top side is full.\n  function pinkRespotX(balls, pink, minX, maxX) {\n    const intervals=[];\n    for(const b of balls){\n      if(!active(b)||b.i===pink.i)continue;\n      const rr=radius(pink)+radius(b)+2*CONTACT_EPS;\n      const across=(b.y-pink.y)**2+(b.z-pink.z)**2;\n      if(across>=rr*rr)continue;\n      const half=Math.sqrt(rr*rr-across);\n      intervals.push([b.x-half,b.x+half]);\n    }\n    intervals.sort((a,b)=>a[0]-b[0]);\n    const blocked=[];\n    for(const range of intervals){\n      const last=blocked[blocked.length-1];\n      if(last&&range[0]<last[1])last[1]=Math.max(last[1],range[1]);\n      else blocked.push(range);\n    }\n    let x=pink.x;\n    for(const [left,right] of blocked){\n      if(x<=left)break;\n      if(x<right)x=right;\n    }\n    if(x<=maxX)return x;\n    x=pink.x;\n    for(let i=blocked.length-1;i>=0;i--){\n      const [left,right]=blocked[i];\n      if(x>=right)break;\n      if(x>left)x=left;\n    }\n    return x>=minX?x:null;\n  }\n\n  function touchingStatus({balls,ballOn,nominatedColour=null,freeBallNominee=null}) {\n    const cue=balls.find(b=>b.n===0 && active(b));\n    const touched=cue?balls.filter(b=>b.n>0 && active(b) && Math.hypot(cue.x-b.x,cue.y-b.y,cue.z-b.z)<=radius(cue)+radius(b)+TOUCH_EPS):[];\n    const on=ballOn===COLOUR_ALL?(nominatedColour?[nominatedColour]:[]):ballOnNumbers(ballOn);\n    const eligible=freeBallNominee!=null?touched.filter(b=>b.i===freeBallNominee):touched.filter(b=>on.includes(b.n));\n    return {indices:touched.map(b=>b.i),eligibleIndices:eligible.map(b=>b.i),deemedHit:eligible.length>0,requiresColourDeclaration:ballOn===COLOUR_ALL && touched.some(b=>b.n>=2),tolerance:TOUCH_EPS};\n  }\n\n  function remainingPoints(balls, ballOn, {freeBall = false} = {}) {\n    if (!ballOn || ballOn === 65535) return 0;\n    const live = balls.filter(b => active(b) && b.n > 0);\n    const reds = live.filter(b => b.n === 1).length;\n    let maximum = reds || ballOn === COLOUR_ALL ? reds * 8 + 27 + (ballOn === COLOUR_ALL ? 7 : 0) : live.filter(b => b.n >= 2).reduce((sum,b) => sum+b.n,0);\n    if (freeBall) maximum += ballOn === RED ? 8 : ballOn === COLOUR_ALL ? 7 : ballOnNumbers(ballOn)[0] || 0;\n    return maximum;\n  }\n\n  // User-requested optional concession threshold, not a mandatory match rule.\n  function concessionStatus({balls, ballOn, scores, playerIndex, freeBall = false, threshold = 1}) {\n    const maximum = remainingPoints(balls,ballOn,{freeBall});\n    const valid = scores.length === 2 && (playerIndex === 0 || playerIndex === 1) && ballOn > 0 && ballOn !== 65535;\n    const deficit = valid ? scores[1-playerIndex]-scores[playerIndex] : 0;\n    const excess = deficit-maximum;\n    return {eligible:valid && excess >= threshold,playerIndex,remaining:maximum,deficit,excess,threshold};\n  }\n\n  /** User-customised early finish, separate from the official final-black rule.\n   * Supply settled post-stroke balls/scores, including foul penalties and respots.\n   * A known free-ball opportunity adds its possible points; unresolved review\n   * cannot establish an early finish. Omit actor/continueBreak for a stable turn.\n   * At 17 over only the leader's legal scoring break may continue. The separate\n   * blackLeadThreshold is a score lead (default 8), not points over the table.\n   * On the last Black, playerIndex is the incoming player: the leader keeps\n   * their shot, including after potting Pink; the trailing player's turn ends it.\n   */\n  function earlyFrameOutcome({balls,ballOn,scores,playerIndex=null,actor=null,continueBreak=false,freeBall=false,freeBallReview=false,threshold=17,blackLeadThreshold=8}) {\n    if(!Array.isArray(balls)||!Array.isArray(scores)||scores.length!==2||!scores.every(Number.isFinite)||\n      !ballOn||ballOn===65535||freeBallReview||freeBall==null||scores[0]===scores[1])return null;\n    const winner=scores[0]>scores[1]?0:1,loser=1-winner;\n    const deficit=scores[winner]-scores[loser],remaining=remainingPoints(balls,ballOn,{freeBall}),excess=deficit-remaining;\n    const live=balls.filter(b=>b.n>0&&active(b));\n    if(ballOn===128&&live.length===1&&live[0].n===7&&Number.isFinite(blackLeadThreshold)&&deficit>=blackLeadThreshold)\n      return playerIndex===loser?{winner,loser,deficit,remaining,excess,threshold:blackLeadThreshold,reason:'black-lead'}:null;\n    if(Number.isFinite(threshold)&&excess>=threshold&&!(actor===winner&&continueBreak===true))\n      return {winner,loser,deficit,remaining,excess,threshold,reason:'excess-threshold'};\n    return null;\n  }\n\n  // Earliest intersection of a cue-centre ray with a ball's expanded disc.\n  function rayBlocker(cue, direction, length, b, cueRadius, eps) {\n    const dx = b.x - cue.x, dz = b.z - cue.z;\n    const projection = dx * direction.x + dz * direction.z;\n    const rr = cueRadius + radius(b);\n    const perpendicular2 = dx * dx + dz * dz - projection * projection;\n    if (perpendicular2 >= rr * rr - eps || projection + rr < 0) return false;\n    const enter = projection - Math.sqrt(Math.max(0, rr * rr - perpendicular2));\n    return enter < length - eps && projection + Math.sqrt(Math.max(0, rr * rr - perpendicular2)) > eps;\n  }\n\n  /** Both extreme physical contacts must be available on at least one ball on.\n   * Cushions and other balls on cannot cause a snooker under definition 17.\n   * options.inHand requires an all-positions proof which this helper does not\n   * attempt: it returns null, never true based on a finite sample of the D.\n   * Effective blockers are returned for the free-ball safety restriction.\n   */\n  function isSnookered(balls, ballOn, cuePosition, options = {}) {\n    if (options.inHand) return {snookered:null, indeterminate:true, clearTargets:[], details:[], effectiveSnookeringBalls:[], reason:'All legal cue positions in the D must be considered.'};\n    const cue = cuePosition || balls.find(b => b.n === 0 && active(b));\n    const on = ballOnNumbers(ballOn);\n    const targets = balls.filter(b => active(b) && on.includes(b.n));\n    if (!cue || targets.length === 0) return {snookered:null, indeterminate:true, clearTargets:[], details:[], effectiveSnookeringBalls:[], reason:'Cue position or ball on unavailable.'};\n    const rc = radius(cue, options.radius || RADIUS), eps = options.epsilon || 1e-8;\n    const blockers = balls.filter(b => active(b) && b.n > 0 && !on.includes(b.n));\n    const details = targets.map(target => {\n      const distance = hypot2(cue, target), rr = rc + radius(target);\n      if (distance <= rr + eps) return {target:target.i, indeterminate:true, leftBlockedBy:[], rightBlockedBy:[], effective:[]};\n      const angle = Math.atan2(target.z - cue.z, target.x - cue.x);\n      const halfAngle = Math.asin(Math.min(1, rr / distance));\n      const travel = Math.sqrt(distance * distance - rr * rr);\n      const edge = sign => {\n        const theta = angle + sign * halfAngle;\n        const direction = {x:Math.cos(theta), z:Math.sin(theta)};\n        return blockers.filter(b => rayBlocker(cue, direction, travel, b, rc, eps)).map(b => b.i);\n      };\n      const leftBlockedBy = edge(1), rightBlockedBy = edge(-1);\n      const both = unique([...leftBlockedBy, ...rightBlockedBy]);\n      const nearest = Math.min(...both.map(i => hypot2(cue, balls.find(b => b.i === i))));\n      const effective = both.filter(i => Math.abs(hypot2(cue, balls.find(b => b.i === i)) - nearest) <= eps);\n      return {target:target.i, leftBlockedBy, rightBlockedBy, effective, clear:both.length === 0};\n    });\n    const clearTargets = details.filter(d => d.clear).map(d => d.target);\n    const indeterminate = !clearTargets.length && details.some(d => d.indeterminate);\n    const snookered = clearTargets.length ? false : indeterminate ? null : true;\n    let effectiveSnookeringBalls = snookered ? details[0].effective.slice() : [];\n    for (const d of details) effectiveSnookeringBalls = effectiveSnookeringBalls.filter(i => d.effective.includes(i));\n    return {snookered, indeterminate, clearTargets, details, effectiveSnookeringBalls};\n  }\n\n  /** Proves visibility of any part of a legal ball, not both extreme edges.\n   * Ray collision order can only change at disc tangent angles or the angles\n   * of expanded-disc intersections. Test each angular cell plus its boundaries.\n   * This handles arbitrarily narrow positive gaps without a fixed angle grid.\n   */\n  function hasDirectHit(balls, ballOn, cuePosition, options = {}) {\n    const unknown=reason=>({hasDirectHit:null,indeterminate:true,target:null,direction:null,reason});\n    if(options.inHand) return unknown('All legal cue positions in the D must be considered.');\n    const cue=cuePosition || balls.find(b=>b.n===0 && active(b));\n    if(!cue) return unknown('Cue position unavailable.');\n    const on=ballOnNumbers(ballOn), rc=radius(cue,options.radius || RADIUS),eps=options.epsilon || 1e-9;\n    const objects=balls.filter(b=>b.n>0 && active(b));\n    if(!objects.some(b=>on.includes(b.n))) return unknown('Ball on unavailable.');\n    const circles=objects.map(b=>({b,x:b.x-cue.x,z:b.z-cue.z,r:rc+radius(b)}));\n    const tau=2*Math.PI,normal=a=>(a%tau+tau)%tau;\n    const angles=[];\n    let touching=false;\n    for(const c of circles) {\n      const d=Math.hypot(c.x,c.z);\n      if(d<=c.r+eps){touching=true;continue;}\n      const angle=Math.atan2(c.z,c.x),h=Math.asin(c.r/d);\n      angles.push(normal(angle-h),normal(angle+h),normal(angle));\n    }\n    for(let i=0;i<circles.length;i++) for(let j=i+1;j<circles.length;j++) {\n      const a=circles[i],b=circles[j],dx=b.x-a.x,dz=b.z-a.z,d=Math.hypot(dx,dz);\n      if(d<=eps || d>a.r+b.r+eps || d<Math.abs(a.r-b.r)-eps)continue;\n      const along=(a.r*a.r-b.r*b.r+d*d)/(2*d),height=Math.sqrt(Math.max(0,a.r*a.r-along*along));\n      const x=a.x+along*dx/d,z=a.z+along*dz/d;\n      angles.push(normal(Math.atan2(z+height*dx/d,x-height*dz/d)),normal(Math.atan2(z-height*dx/d,x+height*dz/d)));\n    }\n    angles.sort((a,b)=>a-b);\n    const candidates=angles.slice();\n    for(let i=0;i<angles.length;i++)candidates.push(normal((angles[i]+(i+1<angles.length?angles[i+1]:angles[0]+tau))/2));\n    for(const angle of candidates) {\n      const direction={x:Math.cos(angle),z:Math.sin(angle)};\n      const entries=[];\n      for(const c of circles) {\n        const projection=c.x*direction.x+c.z*direction.z;\n        const discriminant=c.r*c.r-(c.x*c.x+c.z*c.z-projection*projection);\n        if(discriminant < -eps) continue;\n        const root=Math.sqrt(Math.max(0,discriminant)),near=projection-root,far=projection+root;\n        if(far<eps)continue;\n        entries.push({i:c.b.i,n:c.b.n,t:Math.max(0,near)});\n      }\n      if(!entries.length)continue;\n      const nearest=Math.min(...entries.map(e=>e.t));\n      const first=entries.filter(e=>Math.abs(e.t-nearest)<=eps);\n      if(first.every(e=>on.includes(e.n)) && nearest>eps) {\n        const point={x:cue.x+direction.x*nearest,y:cue.y,z:cue.z+direction.z*nearest};\n        if(options.isPathClear && !options.isPathClear(cue,point))continue;\n        return {hasDirectHit:true,indeterminate:false,target:first[0].i,direction,contactPoint:point,reason:'Direct first contact with a ball on is available.'};\n      }\n    }\n    if(touching) return unknown('Cue is touching or overlapping an object; touching-ball ruling required.');\n    return {hasDirectHit:false,indeterminate:false,target:null,direction:null,reason:'Every straight ray to a ball on first meets a ball not on.'};\n  }\n\n  // Nominate BEFORE the stroke from the current horizontal aim, never from its\n  // eventual outcome. A farther ball on the same ray cannot obscure the intent\n  // to hit the nearer ball. Touching/tangent/tied contacts need a declaration.\n  function inferColour(balls, direction) {\n    const unknown = reason => ({colour:null,ballIndex:null,reason});\n    const cue = balls.find(b => b.n === 0 && active(b));\n    const length = Math.hypot(direction?.x, direction?.z);\n    if (!cue || !Number.isFinite(length) || length < 1e-9) return unknown('invalid-aim');\n    const dx = direction.x / length, dz = direction.z / length, entries = [];\n    for (const b of balls) {\n      if (!active(b) || b.n < 1) continue;\n      const x = b.x-cue.x, z = b.z-cue.z, rr = radius(cue)+radius(b);\n      if (Math.hypot(x,z) <= rr+1e-8) return unknown('touching');\n      const projection = x*dx+z*dz;\n      const disc = rr*rr-(x*x+z*z-projection*projection);\n      if (projection <= 0 || disc < -1e-12) continue;\n      entries.push({b,t:projection-Math.sqrt(Math.max(0,disc)),tangent:disc <= 1e-12});\n    }\n    entries.sort((a,b) => a.t-b.t);\n    if (!entries.length) return unknown('no-direct-target');\n    const first = entries[0];\n    if (first.tangent || entries[1] && entries[1].t-first.t < 1e-7) return unknown('ambiguous');\n    if (first.b.n < 2) return unknown('blocked-by-red');\n    return {colour:first.b.n,ballIndex:first.b.i,reason:'direct'};\n  }\n\n  function lerp(a, b, u) { return {x:a.x+(b.x-a.x)*u, y:a.y+(b.y-a.y)*u, z:a.z+(b.z-a.z)*u}; }\n  function sampleBall(sample, b, indexed) {\n    if (!sample.balls) return b;\n    // Only rows whose IDs exactly match every array index may bypass find.\n    // Other rows retain its first-match behavior, including duplicate IDs.\n    const found = indexed && Number.isInteger(b.i) && b.i>=0 && b.i<sample.balls.length ? sample.balls[b.i] : sample.balls.find(v => v.i === b.i);\n    return found || {...b,active:false};\n  }\n  function traceReader(trace) {\n    if(typeof trace.readCue==='function' && typeof trace.readBall==='function')\n      return {length:trace.length,cue:(k,out)=>trace.readCue(k,out),ball:(k,b,out)=>trace.readBall(k,b,out),hasBalls:()=>true};\n    // Validate legacy object rows locally. Non-indexed/duplicate IDs retain\n    // the original first-match lookup and missing-ball behavior.\n    const indexedRows=new Uint8Array(trace.length);\n    for(let k=0;k<trace.length;k++) {\n      const row=trace[k].balls;\n      if(!row)continue;\n      let indexed=true;\n      for(let i=0;i<row.length;i++)if(!row[i] || row[i].i!==i){indexed=false;break;}\n      if(indexed)indexedRows[k]=1;\n    }\n    return {length:trace.length,cue:k=>trace[k],ball:(k,b)=>sampleBall(trace[k],b,indexedRows[k]),hasBalls:k=>!!trace[k].balls};\n  }\n  function ballAt(reader, b, t) {\n    const a={},next={},objectA={},objectB={};\n    let j = 0;\n    while (j + 1 < reader.length && reader.cue(j+1,next).t < t) j++;\n    if (j + 1 === reader.length) return reader.ball(j,b,objectA);\n    const current=reader.cue(j,a),following=reader.cue(j+1,next);\n    const u = Math.max(0, Math.min(1, (t-current.t) / (following.t-current.t || 1)));\n    return lerp(reader.ball(j,b,objectA),reader.ball(j+1,b,objectB),u);\n  }\n\n  // Relative swept-disc overlap, retaining only points with the cue above\n  // the object's surface. Merely lifting the cue/using masse is not a foul.\n  function sweptOver(a, b, objectA, objectB, rr, eps) {\n    const py=a.y-objectA.y,vy=b.y-objectB.y-py,endY=py+vy;\n    // Use the same relative-height interpolation as below, including its\n    // rounded endpoint. A finite linear segment cannot rise above both ends.\n    // Non-finite inputs retain the original conservative geometry path.\n    if(Number.isFinite(py)&&Number.isFinite(vy)&&Number.isFinite(endY)&&py<=eps&&endY<=eps)return null;\n    const px=a.x-objectA.x,pz=a.z-objectA.z;\n    const vx=b.x-objectB.x-px,vz=b.z-objectB.z-pz;\n    const limit2=(rr-eps)*(rr-eps);\n    const A = vx*vx+vz*vz, B = 2*(px*vx+pz*vz), C = px*px+pz*pz-limit2;\n    let lo = 0, hi = 1;\n    if (A < eps*eps) { if (C >= 0) return null; }\n    else {\n      const D = B*B-4*A*C;\n      if (D <= 0) return null;\n      lo = Math.max(0,(-B-Math.sqrt(D))/(2*A));\n      hi = Math.min(1,(-B+Math.sqrt(D))/(2*A));\n      if (lo > hi) return null;\n    }\n    // Total distance squared is convex. Endpoints and horizontal closest\n    // approach catch above-surface passage without treating overlap caused\n    // by the collision solver's penetration tolerance as an illegal jump.\n    const near = A > 0 ? Math.max(lo,Math.min(hi,-B/(2*A))) : (lo+hi)/2;\n    for (let i=0;i<4;i++) {\n      const u=i===0?near:i===1?(lo+hi)/2:i===2?lo+(hi-lo)*1e-4:hi-(hi-lo)*1e-4;\n      const qx=px+u*vx, qy=py+u*vy, qz=pz+u*vz;\n      const horizontal2 = qx*qx+qz*qz;\n      if (qy > eps && horizontal2 < limit2 && horizontal2+qy*qy >= limit2) return {u,position:lerp(a,b,u)};\n    }\n    return null;\n  }\n\n  /** Physics-step trace; optional trace[k].balls records moving object centres.\n   * contactEvents: {t,ballIndex,legal?}; cushions: {t,kind:'cushion'}.\n   * legal is only needed for exception 20(c). Missing legal metadata is treated\n   * conservatively; other rule checks still reject an illegal first hit.\n   * Borderline/unfinished airborne paths are indeterminate, not auto-penalised.\n   */\n  function evaluateJump(trace, ballsAtStart, contactEvents = [], fallbackRadius = RADIUS) {\n    if (!trace || trace.length < 2) return {foul:false, offendingBalls:[], reason:'Insufficient trajectory.', indeterminate:true, details:[]};\n    const reader=traceReader(trace);\n    const cue = ballsAtStart.find(b => b.n === 0) || {r:fallbackRadius,...reader.cue(0,{})};\n    const rc = radius(cue,fallbackRadius), eps = Math.max(1e-6,rc*0.002);\n    const groundY = cue.y;\n    const events = contactEvents.slice().sort((a,b) => a.t-b.t);\n    const objects = ballsAtStart.filter(b => b.n > 0 && active(b));\n    const touching = new Set(objects.filter(b => Math.hypot(cue.x-b.x,cue.y-b.y,cue.z-b.z) <= rc+radius(b,fallbackRadius)+eps).map(b => b.i));\n    const contacts = events.filter(e => e.ballIndex != null && objects.some(b => b.i === e.ballIndex));\n    const first = contacts[0];\n    const offendingBalls = [], details = [];\n    let indeterminate = false;\n    const cueA={},cueB={},objectA={},objectB={},takeoff={},landing={};\n    for (const object of objects) {\n      const passages=[];\n      let wasOver=false;\n      let previous=reader.ball(0,object,objectA);\n      for (let k=0;k<trace.length-1;k++) {\n        const a=reader.cue(k,cueA),b=reader.cue(k+1,cueB),oa=previous,ob=reader.ball(k+1,object,k%2?objectA:objectB);\n        previous=ob;\n        if (oa.active === false || ob.active === false) {wasOver=false;continue;}\n        const over=sweptOver(a,b,oa,ob,rc+radius(object,fallbackRadius),eps);\n        if (over && !wasOver) passages.push({k,t:a.t+(b.t-a.t)*over.u,position:over.position});\n        wasOver=!!over;\n      }\n      for(const passage of passages) {\n      const detail = {ballIndex:object.i,t:passage.t};\n      if (first && first.t <= passage.t && first.ballIndex !== object.i && !touching.has(first.ballIndex)) {\n        details.push({...detail,exception:'20(a): first hit another non-touching object ball.'});\n        continue;\n      }\n      const prior = contacts.find(e => e.ballIndex===object.i && e.t<=passage.t && !touching.has(e.ballIndex));\n      if (prior && prior.legal !== false && events.some(e => e.t > prior.t && e.t < passage.t && (e.kind==='cushion' || (e.ballIndex!=null && e.ballIndex!==object.i)))) {\n        details.push({...detail,exception:'20(c): returned after object/cushion contact.'});\n        continue;\n      }\n      // Find the takeoff and landing belonging to this airborne passage.\n      let start=passage.k;\n      while(start>0 && reader.cue(start,takeoff).y>groundY+eps) start--;\n      let land=passage.k+1;\n      while(land<trace.length && reader.cue(land,landing).y>groundY+eps) land++;\n      const startPoint=reader.cue(start,takeoff),landPoint=land<trace.length?reader.cue(land,landing):null;\n      const hitDuringFlight = contacts.find(e => e.ballIndex===object.i && e.t>=startPoint.t && (!landPoint || e.t<=landPoint.t));\n      if (hitDuringFlight && !touching.has(object.i)) {\n        if (land===trace.length) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball; landing not yet recorded.'});continue;}\n        if(!reader.hasBalls(land)) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball current position at landing is unavailable.'});continue;}\n        const objectAtLanding=ballAt(reader,object,landPoint.t);\n        const approach=ballAt(reader,object,passage.t);\n        const vx=approach.x-startPoint.x,vz=approach.z-startPoint.z;\n        const length=Math.hypot(vx,vz);\n        const far=length ? ((landPoint.x-objectAtLanding.x)*vx+(landPoint.z-objectAtLanding.z)*vz)/length : 0;\n        if (far <= eps) {details.push({...detail,exception:'20(b): hit airborne, landed on near side of the ball current position.'});continue;}\n        if (far < rc+radius(object,fallbackRadius)+eps) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Landing close to dividing plane; manual decision required.'});continue;}\n      }\n      offendingBalls.push(object.i);\n      details.push({...detail,foul:true,reason:'Cue passed above an object ball without a recorded exception.'});\n      }\n    }\n    return {foul:offendingBalls.length>0,offendingBalls:unique(offendingBalls),reason:offendingBalls.length?'Illegal jump over an object ball.':indeterminate?'Some airborne contact needs review.':'No illegal jump found.',indeterminate,details};\n  }\n\n  // Section 3.4: assess the scores after the final Black's pot or foul.\n  function blackFrameOutcome({ballOn,balls,score,scores,respottedBlack=false}) {\n    if(ballOn!==128 || score===0 || scores.length!==2)return null;\n    const remaining=balls.filter(b=>b.n>0 && active(b));\n    if(remaining.length!==1 || remaining[0].n!==7)return null;\n    return !respottedBlack && scores[0]===scores[1]?'respot':'end';\n  }\n\n  /** Indices identify firstHits (simultaneous), potted, outOfBounds and nominee.\n   * nominatedColour is a number 2..7. balls contains final positions and all\n   * objects including inactive entries. Removed indices are also excluded when\n   * callers supply pre-stroke active flags. Colours to respot are indices.\n   * This pure function does not decide discretionary Foul and a Miss, restore\n   * positions, choose colour spot geometry, or decide a tied-frame re-spot.\n   */\n  function adjudicate({ballOn,nominatedColour=null,freeBallNominee=null,balls,firstHits=[],potted=[],outOfBounds=[],jumpFoul=false,touchingAtStart=[],pushedTouching=[],cueStrikes=1}) {\n    const byIndex=new Map(balls.map(b=>[b.i,b]));\n    const hits=unique(firstHits).map(i=>byIndex.get(i)).filter(b=>b && b.n>0);\n    const pots=unique(potted).map(i=>byIndex.get(i)).filter(Boolean);\n    const outs=unique(outOfBounds).map(i=>byIndex.get(i)).filter(Boolean);\n    const removed=new Set([...potted,...outOfBounds]);\n    const onNumbers=ballOnNumbers(ballOn), colourChoice=ballOn===COLOUR_ALL;\n    const nominee=freeBallNominee==null?null:byIndex.get(freeBallNominee);\n    let on=onNumbers.length===1?onNumbers[0]:null;\n    if(colourChoice) on=nominatedColour>=2 && nominatedColour<=7?nominatedColour:(hits.length===1 && hits[0].n>=2?hits[0].n:null);\n    let foulCode=0,penalty=0;\n    const reasons=[];\n    const penalise=(code,value,reason)=>{foulCode|=code;penalty=Math.max(penalty,4,value||0);reasons.push(reason);};\n    const baseValue=on || (colourChoice?7:4);\n    const validNominee=nominee && nominee.n>0 && nominee.n!==on;\n    const value=b=>validNominee && b.i===nominee.i?baseValue:b.n;\n    const touching=unique(touchingAtStart).map(i=>byIndex.get(i)).filter(b=>b && b.n>0);\n    const deemedHit=validNominee?touching.some(b=>b.i===nominee.i):on!=null && touching.some(b=>b.n===on);\n    if(freeBallNominee!=null && !validNominee) penalise(FOUL.FIRST_HIT,baseValue,'Invalid free-ball nomination.');\n    if(!deemedHit && hits.length===0) penalise(FOUL.MISS,baseValue,'No object ball contacted.');\n    else if(!deemedHit) {\n      const firstLegal=validNominee?hits.some(b=>b.i===nominee.i) && hits.every(b=>b.i===nominee.i || b.n===on):on!=null && hits.every(b=>b.n===on);\n      if(!firstLegal) penalise(FOUL.FIRST_HIT,Math.max(baseValue,...hits.map(value)),'First contact was not on.');\n    }\n    for(const i of unique(pushedTouching)) {\n      const b=touching.find(b=>b.i===i);\n      if(b) penalise(FOUL.PUSH,Math.max(baseValue,value(b)),'Striking the cue caused an initially touching ball to move before playing away.');\n    }\n    if(cueStrikes>1)penalise(FOUL.DOUBLE_HIT,baseValue,'The cue tip struck the cue ball more than once in this stroke.');\n    for(const b of pots) {\n      if(b.n===0) penalise(FOUL.CUE_POTTED,baseValue,'Cue ball pocketed.');\n      else if(b.n!==on && !(validNominee && b.i===nominee.i)) penalise(FOUL.POTTING,Math.max(baseValue,value(b)),'Ball not on pocketed.');\n    }\n    for(const b of outs) penalise(FOUL.OFF_TABLE,Math.max(baseValue,value(b)),'Ball forced off the table.');\n    if(jumpFoul===true || jumpFoul && jumpFoul.foul) penalise(FOUL.JUMP,baseValue,'Illegal jump.');\n    let points=on===1?pots.filter(b=>b.n===1 || validNominee && b.i===nominee.i).length:pots.some(b=>b.n===on || validNominee && b.i===nominee.i)?(on||0):0;\n    const finalBalls=balls.map(b=>removed.has(b.i)?{...b,active:false}:b);\n    let freeBallSafety=null;\n    if(validNominee && !foulCode && points===0) {\n      const remaining=finalBalls.filter(b=>b.n>0 && active(b));\n      const twoColoursWithBlack=remaining.length===2 && remaining.every(b=>b.n>=2) && remaining.some(b=>b.n===7);\n      if(!twoColoursWithBlack) {\n        freeBallSafety=isSnookered(finalBalls,1<<on);\n        if(freeBallSafety.snookered && freeBallSafety.effectiveSnookeringBalls.includes(nominee.i)) penalise(FOUL.FREE_BALL_SNOOKER,baseValue,'Nominated free ball left an effective snooker after a non-scoring stroke.');\n      }\n    }\n    const score=foulCode?-penalty:points;\n    const redsRemain=finalBalls.some(b=>b.n===1 && active(b));\n    const canonicalPotted=pots.some(b=>b.n===on && !(validNominee && b.i===nominee.i));\n    let nextBallOn=ballOn;\n    if(score>0) {\n      if(ballOn===RED) nextBallOn=COLOUR_ALL;\n      else if(colourChoice) nextBallOn=redsRemain?RED:4;\n      else if(canonicalPotted) nextBallOn=on===7?0:1<<(on+1);\n    } else if(ballOn===RED || colourChoice) nextBallOn=redsRemain?RED:4;\n    // The host retains responsibility for tied scores and re-spotted black.\n    if(on===7 && !colourChoice && score<0 && !validNominee) nextBallOn=0;\n    const respots=unique([...pots,...outs].filter(b=>b.n>=2 && (foulCode || ballOn===RED || colourChoice || validNominee && b.i===nominee.i)).map(b=>b.i)).sort((a,b)=>byIndex.get(b).n-byIndex.get(a).n);\n    const cueBall=balls.find(b=>b.n===0);\n    const requiresInHand=!!cueBall && (removed.has(cueBall.i) || !active(cueBall));\n    return {score,foulCode,nextBallOn,respots,requiresInHand,ballOnUsed:on,penalty:foulCode?penalty:0,freeBallNominee:validNominee?nominee.i:null,reasons,freeBallSafety,canonicalPotted,continueBreak:score>0,cueStrikes,touching:{indices:touching.map(b=>b.i),deemedHit,pushedIndices:unique(pushedTouching)}};\n  }\n  return Object.freeze({RADIUS,RED,COLOUR_ALL,FOUL,CONTACT_EPS,TOUCH_EPS,ballOnNumbers,pinkRespotX,touchingStatus,remainingPoints,concessionStatus,earlyFrameOutcome,isSnookered,hasDirectHit,inferColour,evaluateJump,blackFrameOutcome,adjudicate});\n})();\n\n/* Compile a native stroke without touching the live controller or physics world. */\nconst PCOLTrialShot = (() => {\n  const finite = (value, name) => {\n    if (typeof value !== 'number' || !Number.isFinite(value)) throw new TypeError(`${name} must be finite`);\n    return value;\n  };\n  const clamp = (n, lo, hi) => Math.max(lo, Math.min(hi, n));\n  // Public main-thread compilation owns one detached cushion graph. The\n  // decision worker reconstructs the native cushion once from exported bounds.\n  function clone(value, seen = new Map()) {\n    if (value === null || typeof value !== 'object') return value;\n    if (seen.has(value)) return seen.get(value);\n    if (ArrayBuffer.isView(value)) {\n      const buffer = clone(value.buffer, seen);\n      const copy = value instanceof DataView\n        ? new DataView(buffer, value.byteOffset, value.byteLength)\n        : new value.constructor(buffer, value.byteOffset, value.length);\n      seen.set(value, copy);\n      return copy;\n    }\n    if (value instanceof ArrayBuffer) {\n      const copy = value.slice(0);\n      seen.set(value, copy);\n      return copy;\n    }\n    const copy = Array.isArray(value) ? [] : Object.create(Object.getPrototypeOf(value));\n    seen.set(value, copy);\n    for (const key of Reflect.ownKeys(value)) {\n      if (Array.isArray(value) && key === 'length') continue;\n      const descriptor = Object.getOwnPropertyDescriptor(value, key);\n      if (!('value' in descriptor)) throw new Error('Unsupported accessor in native geometry');\n      descriptor.value = clone(descriptor.value, seen);\n      Object.defineProperty(copy, key, descriptor);\n    }\n    return copy;\n  }\n  function resetCushion(cushion) {\n    if(Array.isArray(cushion.actives))cushion.actives.length=0;\n    cushion.crtCushion=null;\n    for(let segment=cushion.head;segment;segment=segment.next) {\n      segment.toi=0;\n      const point=segment.tp;\n      if(point) {\n        point.x=point.y=point.z=0;\n        // Native near-plane detection calls copyFrom on a physics Vec3.\n        if(typeof point.copyFrom!=='function' && typeof point.copy==='function')point.copyFrom=point.copy;\n      }\n    }\n  }\n  const contexts=new WeakMap();\n  function compile(game, shot, overrideBalls) {\n    const live=game?._fpc?._stickCtl,props=live?._state1?._cachedProps;\n    const sourceBalls=game?._simulator?.getBalls?.();\n    if(!props || !sourceBalls?.length || typeof live.getStrokeSpdWithPower!=='function')throw new Error('Native PCOL shot controller is unavailable');\n    const source=live._state1._cushionBody;\n    if(!source)throw new Error('Native cushion geometry is unavailable');\n    let context=contexts.get(live);\n    if(!context || context.source!==source) {\n      context={source,cushion:clone(source)};contexts.set(live,context);\n    }\n    const balls=overrideBalls==null\n      ? sourceBalls.map(b=>({number:b.number,radius:b.radius,active:b.active,position:clone(b.position)}))\n      : overrideBalls.map(b=>{\n        const original=sourceBalls.find(source=>source.index===b.i);\n        if(!original || original.number!==b.n || !(b.r>0))throw new Error('Invalid detached ball configuration');\n        const position=clone(original.position);\n        for(const key of ['x','y','z'])position[key]=finite(b[key],`ball.${key}`);\n        return {number:b.n,radius:b.r,active:b.active,position};\n      });\n    return compilePrepared({Stick:live.constructor,props,cushion:context.cushion},shot,balls);\n  }\n\n  function compilePrepared({Stick,props,cushion}, { direction, power, side = 0, vertical = 0, elevation = 0 } = {}, balls) {\n    const x = finite(direction?.x, 'direction.x'), z = finite(direction?.z, 'direction.z');\n    const length = Math.hypot(x, z);\n    if (!Number.isFinite(length) || length === 0) throw new RangeError('direction must have nonzero finite length');\n    const requested = { direction: { x, z }, power: finite(power, 'power'),\n      side: finite(side, 'side'), vertical: finite(vertical, 'vertical'), elevation: finite(elevation, 'elevation') };\n    for (const key of ['ballRadius', 'tipRadius', 'midRadius', 'stickLen']) finite(props[key], `stick.${key}`);\n    if (!props.stickName || props.tipRadius <= 0 || props.stickLen <= 0) throw new Error('Native stick is not bound');\n    const cue = balls.find(b => b.number === 0 && b.active);\n    if (!cue) throw new Error('Active cue ball is unavailable');\n    // These are all native Cushion filter/detect caches. A fresh Stick keeps\n    // every aim, dirty flag and potential-touch cache private to this shot.\n    resetCushion(cushion);\n    const stick = new Stick(), state = stick._state1;\n    if (!state || typeof state.bind !== 'function') throw new Error('Unsupported native stick constructor');\n    state.onKissPropsChanged = () => {};\n    state.bind({ stickName: props.stickName, specs: { tipRadius: props.tipRadius,\n      buttRadius: 2 * props.midRadius - props.tipRadius, len: props.stickLen } }, balls, cushion);\n    const dx = x / length, dz = z / length;\n    state.resetAimPoint(cue.position);\n    state.setCtlPoint(cue.position.x - dx, cue.position.z - dz);\n    // The native initial slope sentinel (999) can skip exact matching slopes.\n    // Initialize only this detached state, also handling opposite azimuths.\n    const cx = state._worCtlPoint.x - cue.position.x, cz = state._worCtlPoint.z - cue.position.z;\n    state._angleH = Math.atan2(-cz, cx) + Math.PI;\n    state._cachedSlopeH = Number.isFinite(cz / cx) ? Infinity : 0;\n    const radial = Math.max(1, Math.hypot(side, vertical));\n    state.setLocTip(side / radial * state.maxTipOffset, vertical / radial * state.maxTipOffset, false);\n    const normalizedPower = clamp(power, 0, 1);\n    state.setAngleV(clamp(elevation, 0, Math.PI / 4));\n    const point = state.getKissPoint(), dir = state.getKissDir();\n    const stroke = Array.from(new Float32Array([point.x, point.y, point.z, dir.x, dir.y, dir.z,\n      stick.getStrokeSpdWithPower(normalizedPower), props.tipRadius]));\n    if (!stroke.every(Number.isFinite)) throw new Error('Native stroke geometry is non-finite');\n    return { stroke, requested, actual: {\n      direction: { x: stroke[3], y: stroke[4], z: stroke[5] },\n      contactPoint: { x: stroke[0], y: stroke[1], z: stroke[2] },\n      elevation: Math.asin(clamp(-stroke[4] / Math.hypot(...stroke.slice(3, 6)), -1, 1)),\n      power: normalizedPower, side: state._locTipPoint.z / state.maxTipOffset,\n      vertical: state._locTipPoint.y / state.maxTipOffset, speed: stroke[6], tipRadius: stroke[7],\n      maxTipOffset: state.maxTipOffset\n    } };\n  }\n  function exportCompiler(game, source) {\n    const live=game?._fpc?._stickCtl,state=live?._state1,cushion=state?._cushionBody;\n    if(!state || !live._state0 || !cushion || typeof source!=='string')throw new Error('Native compiler source is unavailable');\n    // PCOL 1.0.0 inlines these classes in module 10. Preserve their complete\n    // original closure, without executing its renderer, DOM or game startup.\n    const section=(start,end)=>{\n      const from=source.indexOf(start),to=from<0?-1:source.indexOf(end,from+start.length);\n      if(from<0 || to<0)throw new Error('Unsupported native compiler closure: '+start);\n      return source.slice(from,to);\n    };\n    if(live.constructor.name!=='Ei' || state.constructor.name!=='Ci' || live._state0.constructor.name!=='hi' || cushion.constructor.name!=='E')throw new Error('Unsupported native compiler classes');\n    const native=section('const E=function(t,e){',';var w=E;')+';'+\n      section('const G=1e-6,q=','class W extends')+\n      section('class hi{','const wi=-.9');\n    if(!native.includes(live.constructor.toString()) || !native.includes(state.constructor.toString()))throw new Error('Native compiler source does not match the live controller');\n    const Vector=state._worTargetPoint.constructor,methods={},statics={};\n    for(const key of ['equals','copyFrom','copyFromFloats','subtractToRef','normalize','length','lengthSquared']) {\n      if(typeof Vector.prototype[key]!=='function')throw new Error('Missing native Vector3.'+key);\n      methods[key]=Vector.prototype[key].toString();\n    }\n    for(const key of ['Dot','DistanceSquared']) {\n      if(typeof Vector[key]!=='function')throw new Error('Missing native Vector3.'+key);\n      statics[key]=Vector[key].toString();\n    }\n    const props={};\n    for(const key of ['stickName','ballRadius','tipRadius','midRadius','stickLen'])props[key]=state._cachedProps[key];\n    const bounds=[];\n    for(let segment=cushion.head;segment;segment=segment.next)bounds.push(segment.a.x,segment.a.z);\n    if(bounds.length<6 || !bounds.every(Number.isFinite) || !Number.isFinite(cushion.boundsY))throw new Error('Invalid native cushion bounds');\n    return {native,vector:{constructor:Vector.toString(),methods,statics},props,cushion:{id:cushion.id,y:cushion.boundsY,bounds}};\n  }\n\n  function createCompiler(payload,req) {\n    if(!payload?.vector || typeof payload.native!=='string' || typeof req!=='function')throw new Error('Invalid native compiler payload');\n    const restore=source=>new Function('return ('+source+')')();\n    const Vector=restore(payload.vector.constructor);\n    for(const [key,source] of Object.entries(payload.vector.methods))Vector.prototype[key]=restore(source);\n    for(const [key,source] of Object.entries(payload.vector.statics))Vector[key]=restore(source);\n    const native=new Function('req','Vector','const A={a:req(13)},I={a:req(18)},s={Vector3:Vector};'+payload.native+';return {Stick:Ei,Cushion:E};')(req,Vector);\n    const data=payload.cushion,cushion=new native.Cushion(data.id,{y:data.y,bounds:data.bounds});\n    const context={Stick:native.Stick,props:{...payload.props},cushion};\n    return {compile(shot,sourceBalls) {\n      if(!Array.isArray(sourceBalls) || !sourceBalls.length)throw new Error('Detached compiler balls are required');\n      const balls=sourceBalls.map(b=>{\n        if(!Number.isInteger(b.i) || !Number.isInteger(b.n) || !(b.r>0))throw new Error('Invalid detached ball configuration');\n        const position=new Vector(finite(b.x,'ball.x'),finite(b.y,'ball.y'),finite(b.z,'ball.z'));\n        return {number:b.n,radius:b.r,active:b.active,position};\n      });\n      return compilePrepared(context,shot,balls);\n    }};\n  }\n  return { compile,exportCompiler,createCompiler };\n})();\n\n/* Isolated full-shot runner. This function is stringified into a dedicated worker. */\nfunction PCOLTrialWorker(options) {\n  'use strict';\n  const listen=options?.listen!==false;\n  let setup = null;\n  const requireModules = sources => {\n    const cache = Object.create(null);\n    function req(id) {\n      if (cache[id]) return cache[id].exports;\n      if (typeof sources[id] !== 'string') throw new Error('Missing physics module ' + id);\n      const mod = cache[id] = {exports:{}};\n      new Function('return (' + sources[id] + ')')()(mod, mod.exports, req);\n      return mod.exports;\n    }\n    req.o = (object, key) => Object.prototype.hasOwnProperty.call(object, key);\n    req.d = (exports, key, getter) => {\n      if (!req.o(exports,key)) Object.defineProperty(exports,key,{enumerable:true,get:getter});\n    };\n    req.r = exports => {\n      if (typeof Symbol !== 'undefined' && Symbol.toStringTag) Object.defineProperty(exports,Symbol.toStringTag,{value:'Module'});\n      Object.defineProperty(exports,'__esModule',{value:true});\n    };\n    req.n = mod => {\n      const getter = mod && mod.__esModule ? () => mod.default : () => mod;\n      req.d(getter,'a',getter); return getter;\n    };\n    return req;\n  };\n  const clock = () => performance.now();\n  const centres = world => world.balls.map(b => ({i:b.index,n:b.number,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,r:b.radius}));\n\n  function init(message) {\n    if(!message.modules || !message.geometry || !message.geometry.data || !(message.stepSize>0) || !Number.isFinite(message.stepSize) || !Number.isInteger(message.maxIter) || message.maxIter<1 || message.maxIter>100)throw new Error('Invalid worker initialization');\n    const req=requireModules(message.modules),MeshBody=req(84),mesh=new MeshBody(message.geometry.data);\n    mesh.id=message.geometry.id;\n    for(const group of mesh.groups) {\n      const nt=message.geometry.data[group.name].nt;\n      if(nt) {\n        const uv=req(80),table=uv.createNTableWithImgData({width:0,height:0,data:[]});\n        Object.assign(table,nt);uv.extendPolyGroup(group,table);\n      }\n    }\n    // Native collision/contact state belongs to each World, not MeshBody.\n    // Polygon._size is only a deterministic lazy geometry cache. Reuse this\n    // worker-owned geometry, but keep balls, solver and all contacts per shot.\n    setup={req,mesh,compiler:message.compiler,stepSize:message.stepSize,maxIter:message.maxIter};\n    return {ready:true};\n  }\n\n  function createCompiler() {\n    if(!setup || !setup.compiler)throw new Error('Native trial compiler is not initialized');\n    return PCOLTrialShot.createCompiler(setup.compiler,setup.req);\n  }\n\n  function preservePinkRespot(ref) {\n    const original=ref._liveRespotColorBalls;\n    ref._liveRespotColorBalls=function(list,sim) {\n      if(!list.some(b=>b.number===6))return original.call(this,list,sim);\n      const clearance=1.05*sim.ballRadius,reserved=new Set();\n      for(let i=list.length-1;i>=0;i--) {\n        const b=list[i];reserved.add(b.number);\n        if(!sim.touchBalls(b.index,b.spot,clearance)){list.splice(i,1);sim.respotIndexDefault(b.index);}\n      }\n      list.sort((a,b)=>a.number-b.number);\n      const colours=sim.getBalls().filter(b=>b.number>=2).sort((a,b)=>b.number-a.number);\n      for(const spotBall of colours) {\n        if(!list.length)break;\n        const b=list[list.length-1];\n        if(!reserved.has(spotBall.number)&&!sim.touchBalls(b.index,spotBall.spot,clearance))sim.resetBallPosition(list.pop(),spotBall.spot);\n      }\n      while(list.length) {\n        const b=list.pop();\n        if(b.number!==6){original.call(this,[b],sim);continue;}\n        const ground=sim.ground,margin=sim.ballRadius+2*PCOLCore.CONTACT_EPS;\n        const minX=ground.centerPosition.x-ground.size.x/2+margin,maxX=ground.centerPosition.x+ground.size.x/2-margin;\n        const bs=sim.getBalls().map(b=>({i:b.index,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,r:b.radius}));\n        const x=PCOLCore.pinkRespotX(bs,{i:b.index,...b.spot,r:b.radius},minX,maxX);\n        if(x===null)throw new Error('No legal pink-ball respot position');\n        sim.resetBallXYZ(b,x,b.spot.y,b.spot.z);\n      }\n    };\n  }\n\n  function simulate(message) {\n    if (!setup) throw new Error('Worker is not initialized');\n    const {snapshot,stroke} = message, options = message.options || {};\n    if (!snapshot || !snapshot.serial || !Array.isArray(snapshot.balls) || !snapshot.rules) throw new Error('Invalid trial snapshot');\n    if ((!Array.isArray(stroke) && !ArrayBuffer.isView(stroke)) || stroke.length !== 8 || !Array.from(stroke).every(Number.isFinite)) throw new Error('Invalid trial stroke');\n    const started = clock(), req = setup.req;\n    const World=req(39), Ball=req(49), Simulator=req(50), Solver=req(21);\n    const world = new World();\n    world.stepSize=setup.stepSize;\n    world.solver=new Solver();\n    world.solver.maxIter=setup.maxIter;\n    world.setMeshBody(setup.mesh);\n    for (const b of snapshot.balls) {\n      if (b.i !== world.balls.length || !(b.r>0) || !(b.mass>0) || !b.spot) throw new Error('Invalid ball configuration');\n      world.addBall(new Ball(b.n,b.r,b.mass,b.spot.x,b.spot.y,b.spot.z,b.i));\n    }\n    world.reset();\n    world.deserialize(snapshot.serial);\n    for(const source of snapshot.balls) {\n      const transient=source.transient;\n      if(!transient)continue;\n      const ball=world.balls[source.i];\n      for(const key of ['rfPower','penetration','collisionMask']) {\n        if(transient[key]!==undefined)ball[key]=transient[key];\n      }\n      for(const key of ['rfDir','peneOffset']) {\n        if(transient[key])ball[key].copy(transient[key]);\n      }\n    }\n    const sim=new Simulator('trial',world,null);\n    sim._syncList.ballRadius=world.balls[0].radius;\n    sim._sceneId=snapshot.sceneId || 'tigerClubSno';\n    sim._spotY=sim.ground.centerPosition.y+sim.ballRadius;\n    if(options.scenarioBalls)for(const b of options.scenarioBalls){\n      const ball=world.balls[b.i];\n      if(b.active!==false)sim.respotIndexXYZ(b.i,b.x,b.y,b.z);\n      else ball.active=false;\n    }\n    if (options.cuePosition != null) {\n      const position=options.cuePosition;\n      if (!['x','y','z'].every(key=>Number.isFinite(position[key]))) throw new Error('Invalid trial cue position');\n      sim.respotIndexXYZ(0,position.x,position.y,position.z);\n    }\n    const before=centres(world), rules={...snapshot.rules},custom=rules.ballOn===65535;\n    // A banked colour shot must declare its target before physics, rather than\n    // trying to infer a colour from the initial ray toward a cushion.\n    if (options.nominatedColour != null) {\n      const colour=options.nominatedColour;\n      if(rules.ballOn!==252 || !Number.isInteger(colour) || colour<2 || colour>7 ||\n        (rules.nominatedColour && rules.nominatedColour!==colour) ||\n        !before.some(b=>b.active && b.n===colour)) throw new Error('Invalid trial colour nomination');\n      rules.nominatedColour=colour;rules.nominationSource='manual';\n    }\n    const reviewReasons=[];\n    let touching=PCOLCore.touchingStatus({balls:before,...rules});\n    if(!custom) {\n      if(rules.freeBallReview)reviewReasons.push('Free-ball decision requires review.');\n      if(rules.freeBallAvailable && rules.freeBallNominee==null && !rules.freeBallDeclined)reviewReasons.push('Nominate or decline the available free ball.');\n      if(touching.requiresColourDeclaration && rules.nominationSource!=='manual')reviewReasons.push('Touching colour requires manual nomination.');\n      if(rules.ballOn===252 && !rules.nominatedColour && !touching.requiresColourDeclaration) {\n        const inferred=PCOLCore.inferColour(before,{x:stroke[3],z:stroke[5]});\n        if(inferred.colour) {\n          rules.nominatedColour=inferred.colour;rules.nominationSource='auto';\n          touching=PCOLCore.touchingStatus({balls:before,...rules});\n        } else reviewReasons.push('Colour nomination is ambiguous.');\n      }\n    }\n    const watches=new Map(touching.indices.map(i=>[i,{initial:true}]));\n    const trace=PCOLShotTrace.create(world.balls,{cap:15000,seconds:true}), contacts=[], pushedTouching=[];\n    let overflow=false,recording=false,steps=0,simulatedSeconds=0,cueStrikes=0;\n    function sample() {\n      const row=trace.sample(world.balls,simulatedSeconds);\n      if(!row){overflow=true;return null;}\n      const cue=world.balls[0],q=cue.position;\n      for(const [i,watch] of watches) {\n        const b=world.balls[i],p=b.position;\n        if(watch.initial && (!b.active || Math.hypot(q.x-p.x,q.y-p.y,q.z-p.z)>cue.radius+b.radius+PCOLCore.TOUCH_EPS*2)) watch.initial=false;\n      }\n      return row;\n    }\n    function record(contact,vix,viy,viz,vjx,vjy,vjz,closeSpeed) {\n      if (!(closeSpeed < -1e-6)) return;\n      const q=contact.bi.number===0?contact.bi:contact.isSS && contact.bj.number===0?contact.bj:null;\n      if (!contact.isSS) {\n        const normal=contact.normal || contact.bj.normal;\n        if(!q || contact.bj.end || contact.bj.tunnel || !normal || Math.abs(normal.y)>=.7)return;\n        if(!((q.v.x-vix)*normal.x+(q.v.y-viy)*normal.y+(q.v.z-viz)*normal.z>1e-7))return;\n        const row=sample();if(!row)return;\n        contacts.push({t:row.t,kind:'cushion',evolution:world.evolution,x:row.x,y:row.y,z:row.z});\n        for(const watch of watches.values())watch.initial=false;\n        return;\n      }\n      if(!q) {\n        if(!watches.size)return;\n        const bi=contact.bi,bj=contact.bj;\n        if(Math.hypot(bi.v.x-vix,bi.v.y-viy,bi.v.z-viz)>1e-7) {\n          const watch=watches.get(bi.index);if(watch)watch.initial=false;\n        }\n        if(Math.hypot(bj.v.x-vjx,bj.v.y-vjy,bj.v.z-vjz)>1e-7) {\n          const watch=watches.get(bj.index);if(watch)watch.initial=false;\n        }\n        return;\n      }\n      const cueIsI=q===contact.bi,obj=cueIsI?contact.bj:contact.bi;\n      const vx=cueIsI?vjx:vix,vy=cueIsI?vjy:viy,vz=cueIsI?vjz:viz;\n      const dx=obj.position.x-q.position.x,dy=obj.position.y-q.position.y,dz=obj.position.z-q.position.z;\n      const distance=Math.hypot(dx,dy,dz);\n      if(!distance || !(((obj.v.x-vx)*dx+(obj.v.y-vy)*dy+(obj.v.z-vz)*dz)/distance>1e-7))return;\n      const row=sample();if(!row)return;\n      const initialPush=watches.get(obj.index)?.initial;\n      if(initialPush && !pushedTouching.includes(obj.index))pushedTouching.push(obj.index);\n      const target=rules.ballOn===252 && rules.nominatedColour?2**rules.nominatedColour:rules.ballOn;\n      const allowed=touching.deemedHit || obj.index===rules.freeBallNominee || PCOLCore.ballOnNumbers(target).includes(obj.number);\n      const firstLegal=!contacts.some(c=>c.ballIndex!=null && c.legal===false);\n      contacts.push({t:row.t,ballIndex:obj.index,evolution:world.evolution,x:row.x,y:row.y,z:row.z,legal:allowed && firstLegal});\n      if(!initialPush)for(const watch of watches.values())watch.initial=false;\n    }\n    const solve=world.solver.solveContact;\n    world.solver.solveContact=function(contact) {\n      if(contact===world.tipContact&&contact.getCloseSpeed() < -1e-6)cueStrikes++;\n      const capture=recording && (contact.isSS || contact.bi.number===0);\n      // These pre-solve values are used only by this synchronous call. Scalars\n      // avoid temporary vector objects without sharing mutable contact state.\n      let vix,viy,viz,vjx,vjy,vjz;\n      if(capture) {\n        vix=contact.bi.v.x;viy=contact.bi.v.y;viz=contact.bi.v.z;\n        if(contact.isSS){vjx=contact.bj.v.x;vjy=contact.bj.v.y;vjz=contact.bj.v.z;}\n      }\n      const speed=capture?contact.getCloseSpeed():0;\n      const result=solve.call(this,contact);\n      if(capture)record(contact,vix,viy,viz,vjx,vjy,vjz,speed);\n      return result;\n    };\n    const internal=world.internalStep;\n    world.internalStep=function(){const result=internal.call(this);sample();return result;};\n    sim.stroke(Array.from(stroke));\n    recording=true;\n    const cue=world.balls[0];\n    for(const [i,watch] of watches) {\n      const obj=world.balls[i],dx=obj.position.x-cue.position.x,dy=obj.position.y-cue.position.y,dz=obj.position.z-cue.position.z;\n      const distance=Math.hypot(dx,dy,dz);\n      if(distance && (cue.v.x*dx+cue.v.y*dy+cue.v.z*dz)/distance < -1e-6)watch.initial=false;\n    }\n    sample();\n    const maxSteps=Number.isFinite(options.maxSteps)?Math.max(1,Math.min(100000,Math.floor(options.maxSteps))):12000;\n    const maxWallMs=Number.isFinite(options.maxWallMs)?Math.max(1,Math.min(60000,options.maxWallMs)):5000;\n    let reason=null;\n    do {\n      if(clock()-started>=maxWallMs){reason='wall-time limit';break;}\n      simulatedSeconds+=sim.step(setup.stepSize);steps++;\n      if(overflow){reason='trajectory limit';break;}\n      if(!world.balls.some(b=>b.active && !b.asleep))break;\n      if(steps>=maxSteps){reason='step limit';break;}\n    } while(true);\n    const balls=centres(world),status=reason?'incomplete':'complete';\n    const first=contacts.find(c=>c.ballIndex!=null);\n    const firstHits=first?[...new Set(contacts.filter(c=>c.ballIndex!=null && c.evolution===first.evolution && Math.hypot(c.x-first.x,c.y-first.y,c.z-first.z)<1e-5).map(c=>c.ballIndex))]:[];\n    const jump=PCOLCore.evaluateJump(trace,before,contacts,sim.ballRadius);\n    if(reason) {jump.indeterminate=true;jump.reason=reason;}\n    const potted=[...sim.result.pottedIndices],outOfBounds=[...sim.result.outOfBoundsIndices];\n    if(!custom && jump.indeterminate)reviewReasons.push('Jump assessment requires review.');\n    const adjudication=!custom && status==='complete' && !reviewReasons.length?PCOLCore.adjudicate({...rules,balls,firstHits,potted,outOfBounds,jumpFoul:jump.foul,touchingAtStart:touching.indices,pushedTouching,cueStrikes}):null;\n    const afterScores=(rules.scores||[]).map((score,index)=>score+(adjudication?.score>0 && index===rules.playerIndex?adjudication.score:adjudication?.score<0 && index!==rules.playerIndex?-adjudication.score:0));\n    const blackFrame=adjudication?PCOLCore.blackFrameOutcome({ballOn:rules.ballOn,balls:before,score:adjudication.score,scores:afterScores,respottedBlack:rules.respottedBlack}):null;\n    if(blackFrame){adjudication.frameOutcome=blackFrame;adjudication.continueBreak=false;}\n    const result={status,steps,simulatedSeconds,elapsedMs:clock()-started,balls,potted,outOfBounds,firstHits,contacts,stroke:Array.from(stroke),adjudication,jump};\n    if(reviewReasons.length)result.reviewReasons=reviewReasons;\n    if(status==='complete' && (custom || adjudication)) {\n      const Ref=req(54),ref=new Ref();\n      ref.syncAreaWithSimulator(sim);\n      preservePinkRespot(ref);\n      if(custom) {\n        if(!world.balls[0].active)ref._liveRespotCueBall(sim);\n      } else {\n        ref._liveRespot(adjudication.respots,[],sim);\n        if(adjudication.requiresInHand)ref._liveRespotCueBall(sim);\n        if(blackFrame==='respot'){\n          ref._liveRespotCueBall(sim);\n          sim.respotIndexDefault(world.balls.find(b=>b.number===7).index);\n        }\n      }\n      result.nextBalls=centres(world);\n      result.nextContext={ballOn:custom?65535:adjudication.nextBallOn,inHand:custom?1:adjudication.requiresInHand?2:0};\n      if(blackFrame==='respot')Object.assign(result.nextContext,{ballOn:128,inHand:2,respottedBlack:true,requiresDraw:true});\n      if(blackFrame==='end')Object.assign(result.nextContext,{ballOn:0,inHand:0});\n      // Only adjudicated legal continuations have an automatic next player/state.\n      // Fouls, cue placement and a drawn black decider require human decisions.\n      if(!custom && !adjudication.foulCode && !adjudication.requiresInHand && !result.nextContext.requiresDraw) {\n        const nextRules={...rules,...result.nextContext,scores:afterScores,\n          nRounds:(rules.nRounds || 0)+1,\n          playerIndex:adjudication.continueBreak?rules.playerIndex:(rules.playerIndex+1)%Math.max(1,afterScores.length),\n          nominatedColour:null,nominationSource:null,freeBallNominee:null,\n          freeBallAvailable:false,freeBallReview:false,freeBallDeclined:false,\n          respottedBlack:blackFrame==='end'?false:!!rules.respottedBlack};\n        result.nextSnapshot={sceneId:snapshot.sceneId,serial:world.serialize({balls:[]}),rules:nextRules,\n          balls:snapshot.balls.map(source=>{\n            const b=world.balls[source.i];\n            return {...source,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,spot:{...source.spot},transient:{rfPower:b.rfPower,\n              rfDir:{x:b.rfDir.x,y:b.rfDir.y,z:b.rfDir.z},penetration:b.penetration,\n              peneOffset:{x:b.peneOffset.x,y:b.peneOffset.y,z:b.peneOffset.z},collisionMask:b.collisionMask}};\n          })};\n      }\n    }\n    if(reason)result.reason=reason;\n    if(options.trace)result.trace=options.trace==='cue'?trace.toCueArray():trace.toArray();\n    return result;\n  }\n  if(listen)self.onmessage = event => {\n    const message=event.data;\n    try {\n      let result;\n      if(message.type==='init') result=init(message);\n      else if(message.type==='simulate') result=simulate(message);\n      else throw new Error('Unknown worker request');\n      self.postMessage({id:message.id,result});\n    } catch(error) {self.postMessage({id:message && message.id,error:String(error && error.message || error)});}\n  };\n  return {init,simulate,createCompiler};\n}\n\n/* Bounded geometric seeds and terminal-position heuristics; legality belongs to the trial. */\nconst PCOLSearchGeometry = (() => {\n  const distance = (a,b) => Math.hypot(a.x-b.x,a.z-b.z);\n  const unit = (a,b) => { const d=distance(a,b); return d>1e-9?{x:(b.x-a.x)/d,z:(b.z-a.z)/d}:null; };\n  const radius = b => Number.isFinite(b.r)&&b.r>0?b.r:.026;\n  const active = b => b.active!==false && Number.isFinite(b.x) && Number.isFinite(b.z);\n  function targets(state, mask=state.rules?.ballOn, nominee=state.rules?.freeBallNominee) {\n    const nomination=mask===252?state.rules?.nominatedColour:null;\n    const effectiveMask=Number.isInteger(nomination)&&nomination>=2&&nomination<=7?1<<nomination:mask;\n    return (state.balls||[]).filter(b=>active(b)&&b.n>0&&(nominee!=null?b.i===nominee:((effectiveMask||0)&(1<<b.n))));\n  }\n  function clear(state,a,b,movingRadius,excluded=[]) {\n    const dx=b.x-a.x,dz=b.z-a.z,l2=dx*dx+dz*dz;\n    if(l2<1e-12)return false;\n    for(const ball of state.balls||[]){\n      if(!active(ball)||excluded.includes(ball.i))continue;\n      const t=Math.max(0,Math.min(1,((ball.x-a.x)*dx+(ball.z-a.z)*dz)/l2));\n      const x=ball.x-a.x-t*dx,z=ball.z-a.z-t*dz,limit=movingRadius+radius(ball)-1e-5;\n      // Component bounds reject distant balls without changing the contact comparison.\n      if(Math.abs(x)>=limit||Math.abs(z)>=limit)continue;\n      if(Math.hypot(x,z)<limit)return false;\n    }\n    return true;\n  }\n  function pocketAccepts(target,pocket) {\n    const d=unit(target,pocket),n=pocket.normal;\n    if(!d)return false;\n    if(!n||!Number.isFinite(n.x)||!Number.isFinite(n.z))return true;\n    // Native normals face into the table; maxHalfOpen is a dot threshold.\n    const dot=d.x*n.x+d.z*n.z;\n    return !Number.isFinite(pocket.maxHalfOpen)||dot<=pocket.maxHalfOpen;\n  }\n  function plantRoutes(state,cue,on=targets(state)) {\n    if(!cue||!Array.isArray(on)||on.length<2)return [];\n    const routes=[],pockets=state.pockets||[];\n    for(const potBall of on)for(let p=0;p<pockets.length;p++){\n      const pocket=pockets[p],d2=unit(potBall,pocket);\n      if(!d2||!pocketAccepts(potBall,pocket)||!clear(state,potBall,pocket,radius(potBall),[cue.i,potBall.i]))continue;\n      const g2={x:potBall.x-d2.x*(radius(potBall)*2),z:potBall.z-d2.z*(radius(potBall)*2)};\n      for(const hitBall of on){\n        if(hitBall.i===potBall.i)continue;\n        const pairDist=distance(hitBall,potBall);if(pairDist>.42)continue;\n        const d12=unit(hitBall,g2);if(!d12)continue;\n        const plantCut=d12.x*d2.x+d12.z*d2.z;if(plantCut<.45)continue;\n        if(!clear(state,hitBall,g2,radius(hitBall),[cue.i,hitBall.i,potBall.i]))continue;\n        const g1={x:hitBall.x-d12.x*(radius(cue)+radius(hitBall)),z:hitBall.z-d12.z*(radius(cue)+radius(hitBall))};\n        const direction=unit(cue,g1);if(!direction)continue;\n        const cueCut=direction.x*d12.x+direction.z*d12.z;if(cueCut<.25)continue;\n        if(!clear(state,cue,g1,radius(cue),[cue.i,hitBall.i,potBall.i]))continue;\n        const gap=distance(hitBall,g2),travel=distance(cue,g1)+gap+distance(potBall,pocket);\n        const deadPlant=plantCut>=.96&&pairDist<=.14;\n        const cut=Math.min(.95,cueCut*(plantCut**1.15)*(deadPlant?1.08:1/(1+gap*1.1)));\n        routes.push({kind:'attack',targetIndex:hitBall.i,potTargetIndex:potBall.i,pocketIndex:p,\n          priority:(deadPlant?1.15:.92)/(.1+travel),label:deadPlant?'死传球进攻':'组合传球进攻',\n          direction,travel,cut,plant:true,deadPlant,plantCut,cueCut});\n      }\n    }\n    return routes.sort((a,b)=>b.priority-a.priority);\n  }\n  function doubleRoutes(state,cue,on=targets(state)) {\n    const b=state.bounds,pockets=state.pockets||[];\n    if(!cue||!b||pockets.length<2||!Array.isArray(on)||!on.length)return [];\n    const routes=[];\n    for(const target of on){\n      const r=radius(target),walls=[\n        ['z',b.minZ+r,pk=>pk.z>0],\n        ['z',b.maxZ-r,pk=>pk.z<0],\n        ['x',b.minX+r,pk=>pk.x>-.2],\n        ['x',b.maxX-r,pk=>pk.x<.2]\n      ];\n      for(let p=0;p<pockets.length;p++){\n        const pocket=pockets[p];\n        for(const [axis,value,validPocket] of walls){\n          if(!validPocket(pocket))continue;\n          const other=axis==='x'?'z':'x';\n          const denom=Math.abs(target[axis]-value)+Math.abs(pocket[axis]-value);\n          if(denom<=1e-5)continue;\n          const tRatio=Math.abs(target[axis]-value)/denom;\n          const bounceNominal={x:target.x,z:target.z};\n          bounceNominal[axis]=value;\n          bounceNominal[other]=target[other]+(pocket[other]-target[other])*tRatio;\n          if(pockets.some(q=>distance(bounceNominal,q)<.14))continue;\n          const d1=distance(target,bounceNominal),d2=distance(bounceNominal,pocket);\n          if(d1<=.08||d2<=.08)continue;\n          const incidenceCos=Math.abs(bounceNominal[axis]-target[axis])/d1;\n          if(incidenceCos<.35||!pocketAccepts(bounceNominal,pocket))continue;\n          if(!clear(state,target,bounceNominal,r,[cue.i,target.i])||!clear(state,bounceNominal,pocket,r,[cue.i,target.i]))continue;\n          const makeVariant=comp=>{\n            const bounce={...bounceNominal};\n            bounce[other]=bounceNominal[other]+(pocket[other]-bounceNominal[other])*comp;\n            const d1Vec=unit(target,bounce);if(!d1Vec)return null;\n            const ghost={x:target.x-d1Vec.x*(radius(cue)+r),z:target.z-d1Vec.z*(radius(cue)+r)};\n            const direction=unit(cue,ghost);if(!direction)return null;\n            const cueCut=direction.x*d1Vec.x+direction.z*d1Vec.z;\n            return {bounce,ghost,direction,cueCut,travel:distance(cue,ghost)+d1+d2};\n          };\n          const primary=makeVariant(.05);\n          if(!primary||primary.cueCut<.32||!clear(state,cue,primary.ghost,radius(cue),[cue.i,target.i]))continue;\n          const aimVariants=[0,.05,.1].map(makeVariant).filter(v=>v&&v.cueCut>=.28&&clear(state,cue,v.ghost,radius(cue),[cue.i,target.i]));\n          const cut=Math.min(.78,primary.cueCut*incidenceCos*.68);\n          routes.push({kind:'attack',targetIndex:target.i,pocketIndex:p,priority:.72/(.1+primary.travel),\n            label:'翻袋进攻',direction:primary.direction,aimVariants,travel:primary.travel,cut,doubleShot:true,cushionAxis:axis});\n        }\n      }\n    }\n    return routes.sort((a,b)=>b.priority-a.priority);\n  }\n  function attackRoutes(state,cue,on) {\n    const routes=[];\n    for(const target of on)for(let p=0;p<(state.pockets||[]).length;p++){\n      const pocket=state.pockets[p],d=unit(target,pocket);\n      if(!d||!pocketAccepts(target,pocket))continue;\n      const ghost={x:target.x-d.x*(radius(cue)+radius(target)),z:target.z-d.z*(radius(cue)+radius(target))};\n      const direction=unit(cue,ghost);\n      const cut=direction?direction.x*d.x+direction.z*d.z:0;\n      if(!direction||cut<.15)continue;\n      if(!clear(state,target,pocket,radius(target),[cue.i,target.i])||!clear(state,cue,ghost,radius(cue),[cue.i,target.i]))continue;\n      const travel=distance(cue,ghost)+distance(target,pocket);\n      routes.push({kind:'attack',targetIndex:target.i,pocketIndex:p,priority:1/(.1+travel),label:'直线进攻',direction,travel,cut});\n    }\n    if(Array.isArray(on)&&on.length>=2)routes.push(...plantRoutes(state,cue,on));\n    return routes.sort((a,b)=>b.priority-a.priority);\n  }\n  function banks(state,cue,target) {\n    const b=state.bounds;if(!b)return [];\n    const r=radius(cue),routes=[];\n    const walls=[['x',b.minX+r],['x',b.maxX-r],['z',b.minZ+r],['z',b.maxZ-r]];\n    for(const [axis,value] of walls){\n      const other=axis==='x'?'z':'x',mirror={x:target.x,z:target.z};mirror[axis]=2*value-target[axis];\n      const denom=mirror[axis]-cue[axis],t=(value-cue[axis])/denom;\n      if(!Number.isFinite(t)||t<=0||t>=1)continue;\n      const contact={x:cue.x+t*(mirror.x-cue.x),z:cue.z+t*(mirror.z-cue.z)};\n      const lo=other==='x'?b.minX+r:b.minZ+r,hi=other==='x'?b.maxX-r:b.maxZ-r;\n      if(contact[other]<lo||contact[other]>hi)continue;\n      if(!clear(state,cue,contact,r,[cue.i])||!clear(state,contact,target,r,[cue.i,target.i]))continue;\n      routes.push({kind:'escape',targetIndex:target.i,priority:.5/(.1+distance(cue,contact)+distance(contact,target)),label:'一库解球',direction:unit(cue,contact)});\n    }\n    return routes;\n  }\n  function roundRobin(items,key) {\n    const groups=new Map();for(const item of items){const k=key(item);if(!groups.has(k))groups.set(k,[]);groups.get(k).push(item);}\n    const out=[];for(let i=0;out.length<items.length;i++)for(const group of groups.values())if(group[i])out.push(group[i]);\n    return out;\n  }\n  const routeKey=c=>[c.kind,c.targetIndex,c.potTargetIndex??c.targetIndex,c.pocketIndex??null,c.development?'development':c.doubleShot?'double':c.plant?'plant':'direct'].join(':');\n  function diverse(items) { return roundRobin(roundRobin(items,routeKey),c=>c.targetIndex); }\n  function softContacts(state) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue)return [];\n    return targets(state).filter(t=>clear(state,cue,t,radius(cue),[cue.i,t.i])).sort((a,b)=>distance(cue,a)-distance(cue,b)).slice(0,2).map(t=>({\n      kind:'safety',targetIndex:t.i,...nomination(state,t.i),softContact:true,label:'物理校准轻贴',\n      shot:{direction:unit(cue,t),power:.14,vertical:0,side:0,elevation:0}}));\n  }\n  function generate(state) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue)return [];\n    const on=targets(state),direct=attackRoutes(state,cue,on),doubles=doubleRoutes(state,cue,on).slice(0,4);\n    const doubleExpanded=doubles.flatMap(r=>(r.aimVariants?.length?r.aimVariants:[{direction:r.direction,travel:r.travel}]).map(v=>({...r,direction:v.direction,travel:v.travel,aimVariants:undefined})));\n    const groups={attack:direct.concat(doubleExpanded),safety:[],escape:[]};\n    for(const target of on){\n      const d=unit(cue,target);if(!d)continue;\n      if(clear(state,cue,target,radius(cue),[cue.i,target.i])){\n        groups.escape.push({kind:'escape',targetIndex:target.i,priority:1/(.1+distance(cue,target)),label:'直接解球',direction:d});\n      }\n        for(const thin of [0,-.45,.45,-.8,.8,-.94,.94]){\n          const aim={x:target.x-d.z*thin*(radius(cue)+radius(target)),z:target.z+d.x*thin*(radius(cue)+radius(target))};\n          if(clear(state,cue,aim,radius(cue),[cue.i,target.i]))groups.safety.push({kind:'safety',targetIndex:target.i,priority:1/(.1+distance(cue,target)),label:thin?'薄球防守':'直接防守',direction:unit(cue,aim)});\n        }\n      groups.escape.push(...banks(state,cue,target));\n    }\n    // Rotate target balls before thickness variants; obstruction decides escape allocation.\n    groups.attack=diverse(groups.attack);groups.safety=roundRobin(groups.safety,c=>c.targetIndex);\n    const blocked=!groups.escape.some(c=>c.label==='直接解球');\n    groups.escape=roundRobin(groups.escape,c=>c.targetIndex);\n    if(!blocked)groups.escape=groups.escape.filter(c=>c.label!=='直接解球').slice(0,2);\n    // Explore independent routes before parameter variants.\n    const result=[],kinds=['attack','safety','escape'];\n    const longest=Math.max(...kinds.map(k=>groups[k].length));\n    for(let variant=0;variant<5&&result.length<96;variant++){\n      for(let i=0;i<longest&&result.length<96;i++)for(const kind of kinds){\n        const route=groups[kind][i];if(!route||result.length>=96)continue;\n        const base=kind==='attack'?Math.max(.20,Math.min(.55,.20+.045*route.travel+.10*(1-route.cut))):kind==='safety'?.28:.48;\n        const {direction,...meta}=route;\n        const draw=kind==='attack'&&variant===1;\n        const vertical=draw?-.35:[0,-.35,.3,-.5,.5][variant];\n        result.push({...meta,...nomination(state,route.targetIndex),shot:{direction,power:Math.max(.08,Math.min(.85,draw?base*.9:base+[0,-.1,.1,.2,.04][variant])),side:0,vertical,elevation:vertical<0?.025*Math.PI:0}});\n      }\n    }\n    return result;\n  }\n  function nomination(state,index) {\n    if(state.rules?.ballOn!==252)return {};\n    const explicit=state.rules?.nominatedColour;\n    const target=(state.balls||[]).find(b=>b.i===index);\n    // A free ball may stand for an explicitly nominated colour; never overwrite it.\n    return {nominatedColour:explicit>=2&&explicit<=7?explicit:target?.n>=2&&target.n<=7?target.n:2};\n  }\n  function refine(state,candidate) {\n    if(!candidate.shot)return [];\n    const boundary=candidate.executionBoundary,repairPower=boundary?.repairPower;\n    if(candidate.kind!=='attack')return Number.isFinite(repairPower)?[{...candidate,parentCandidateId:candidate.id,label:'到球力度修正',\n      executionRepair:{...boundary,referenceReachedPower:boundary.reachedPower},shot:{...candidate.shot,power:repairPower}}]:[];\n    // Compare adequate speed with stun, a modest draw and a deeper draw before\n    // reducing speed for position. Native outcomes decide which spin is useful.\n    const minimumDelta=Number.isFinite(repairPower)?Math.max(0,repairPower-candidate.shot.power):0,seen=new Set();\n    return [[Math.max(.06,minimumDelta),0],[Math.max(.10,minimumDelta),-.2],[Math.max(.12,minimumDelta),-.5],\n      [-.06,0],[.06,0],[-.03,-.5],[.04,-.5],[-.03,.5],[.04,.5]].flatMap(([delta,vertical],index)=>{\n      const power=Math.max(.08,Math.min(.85,candidate.shot.power+delta)),signature=[power,vertical].join(':');\n      if(seen.has(signature))return [];seen.add(signature);\n      return [{...candidate,...nomination(state,candidate.targetIndex),parentCandidateId:candidate.id,label:'进攻走位微调',\n        executionRepair:index<3&&boundary?{...boundary,referenceReachedPower:boundary.reachedPower}:undefined,\n        shot:{...candidate.shot,power,side:0,vertical,elevation:vertical<0?.025*Math.PI:0}}];\n    });\n  }\n  function multiBanks(state,cue,on) {\n    const b=state.bounds;if(!b)return [];\n    const r=radius(cue),walls=[['x',b.minX+r],['x',b.maxX-r],['z',b.minZ+r],['z',b.maxZ-r]],routes=[];\n    function trace(target,sequence) {\n      const mirror={x:target.x,z:target.z};\n      for(const index of sequence.slice().reverse()){const [axis,value]=walls[index];mirror[axis]=2*value-mirror[axis];}\n      const direction=unit(cue,mirror);if(!direction)return;\n      let point=cue,ray={...direction},travel=0;\n      for(const index of sequence){\n        const [axis,value]=walls[index],other=axis==='x'?'z':'x';\n        const t=(value-point[axis])/ray[axis];if(!Number.isFinite(t)||t<=1e-6)return;\n        const contact={x:point.x+t*ray.x,z:point.z+t*ray.z};\n        const lo=other==='x'?b.minX+r:b.minZ+r,hi=other==='x'?b.maxX-r:b.maxZ-r;\n        if(contact[other]<=lo+1e-5||contact[other]>=hi-1e-5||!clear(state,point,contact,r,[cue.i]))return;\n        travel+=t;point=contact;ray[axis]*=-1;\n      }\n      if(!clear(state,point,target,r,[cue.i,target.i]))return;\n      travel+=distance(point,target);\n      routes.push({kind:'escape',targetIndex:target.i,label:sequence.length===2?'两库解球':'三库解球',direction,travel,priority:1/(.1+travel)});\n    }\n    for(const depth of [2,3]){\n      function enumerate(sequence){\n        if(sequence.length===depth){for(const target of on)trace(target,sequence);return;}\n        for(let w=0;w<4;w++)if(w!==sequence[sequence.length-1])enumerate([...sequence,w]);\n      }\n      enumerate([]);if(routes.length)break;\n    }\n    return routes.sort((a,b)=>b.priority-a.priority).slice(0,32);\n  }\n  function generateRecovery(state,options={}) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue)return [];\n    const routes=options.multiCushion?multiBanks(state,cue,targets(state)):[];\n    for(const target of options.multiCushion?[]:targets(state)){\n      const d=unit(cue,target);if(!d)continue;\n      for(const thin of [0,-.92,.92]){\n        const aim={x:target.x-d.z*thin*(radius(cue)+radius(target)),z:target.z+d.x*thin*(radius(cue)+radius(target))};\n        if(clear(state,cue,aim,radius(cue),[cue.i,target.i]))routes.push({kind:'escape',targetIndex:target.i,label:thin?'薄球解球微调':'直接解球微调',direction:unit(cue,aim)});\n      }\n      routes.push(...banks(state,cue,target));\n    }\n    const result=[],seen=new Set();\n    const variants=options.multiCushion?[.67,.85,.39].flatMap(power=>routes.map(route=>({route,power}))):routes.flatMap(route=>[.19,.39,.67].map(power=>({route,power})));\n    for(const offset of [0,-.003,.003])for(const {route,power} of variants){\n      if(result.length>=96)return result;\n      const a=Math.atan2(route.direction.z,route.direction.x)+offset;\n      const key=[a.toFixed(5),power,route.targetIndex].join(':');if(seen.has(key))continue;seen.add(key);\n      const {direction,...meta}=route;\n      result.push({...meta,...nomination(state,route.targetIndex),shot:{direction:{x:Math.cos(a),z:Math.sin(a)},power,side:0,vertical:0,elevation:0}});\n    }\n    return result;\n  }\n  function opportunity(state,mask) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);\n    if(!cue||!mask)return {chance:0,lanes:0};\n    const routes=attackRoutes(state,cue,targets(state,mask,null));\n    return {chance:routes.length?Math.max(...routes.map(r=>r.priority)):0,lanes:routes.length};\n  }\n  function evaluate(state,candidate,trialResult) {\n    const adjudication=trialResult.adjudication;\n    const scoreDelta=Number.isFinite(adjudication.score)?adjudication.score:0;\n    const next={...state,balls:trialResult.nextBalls||[],rules:{ballOn:adjudication.nextBallOn}};\n    const cue=next.balls.find(b=>active(b)&&b.n===0),on=targets(next,adjudication.nextBallOn,null);\n    const scale=state.bounds?Math.hypot(state.bounds.maxX-state.bounds.minX,state.bounds.maxZ-state.bounds.minZ):1;\n    const separation=cue&&on.length?Math.min(...on.map(b=>distance(cue,b)))/Math.max(scale,1e-9):0;\n    const incoming=opportunity(next,adjudication.nextBallOn);\n    const root=state.rootPlayerIndex??state.rules?.playerIndex??0,actor=state.rules?.playerIndex??0;\n    const nextActor=trialResult.nextContext?.playerIndex??trialResult.nextSnapshot?.rules?.playerIndex??(adjudication.continueBreak?actor:1-actor);\n    const stays=nextActor===root;\n    const features={scoreDelta,cueSafety:separation,targetSeparation:separation,\n      opponentChance:stays?0:incoming.chance,nextChance:stays?incoming.chance:0,\n      laneAvailability:incoming.lanes};\n    const netPoints=scoreDelta*(actor===root?1:-1),futureValue=Math.min(7,incoming.chance*3)*(stays?1:-1);\n    Object.assign(features,{netPoints,futureValue,nextPlayerIndex:nextActor});\n    return {score:netPoints+futureValue,netPoints,futureValue,terminalValue:0,features};\n  }\n  function positionSectors(state,target,limit=4,ignoredIds=[]) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);if(!cue||!target)return [];\n    const out=[],b=state.bounds;\n    for(let p=0;p<(state.pockets||[]).length;p++){\n      const pocket=state.pockets[p],toward=unit(target,pocket);if(!toward||!pocketAccepts(target,pocket)||!clear(state,target,pocket,radius(target),[cue.i,target.i,...ignoredIds]))continue;\n      for(const offset of [0,-.35,.35])for(const length of [.24,.42]){\n        const angle=Math.atan2(-toward.z,-toward.x)+offset,axis={x:Math.cos(angle),z:Math.sin(angle)};\n        const centre={x:target.x+axis.x*length,z:target.z+axis.z*length};\n        if(b&&(centre.x<b.minX+radius(cue)||centre.x>b.maxX-radius(cue)||centre.z<b.minZ+radius(cue)||centre.z>b.maxZ-radius(cue)))continue;\n        const ghost={x:target.x+axis.x*(radius(cue)+radius(target)),z:target.z+axis.z*(radius(cue)+radius(target))};\n        if(!clear(state,centre,ghost,radius(cue),[cue.i,target.i,...ignoredIds]))continue;\n        out.push({id:`sector-${target.i}-${p}-${length}-${offset}`,targetId:target.i,pocketIndex:p,origin:{x:target.x,z:target.z},axis,centre,distance:length,minDistance:Math.max(.09,length-.12),maxDistance:length+.12,angleTolerance:.15,arrivalTolerance:.75,priority:1/(.2+distance(target,pocket)+length+Math.abs(offset)*.15)});\n      }\n    }\n    return out.sort((a,b)=>b.priority-a.priority).slice(0,limit);\n  }\n  function sectorCheck(cue,sector,trace) {\n    if(!cue||!sector)return {met:false,distance:null,angle:null,arrivalAligned:false};\n    const dx=cue.x-sector.origin.x,dz=cue.z-sector.origin.z,length=Math.hypot(dx,dz);\n    const angle=length>1e-9?Math.acos(Math.max(-1,Math.min(1,(dx*sector.axis.x+dz*sector.axis.z)/length))):Math.PI;\n    let arrivalAngle=null;\n    if(Array.isArray(trace))for(let j=trace.length-2;j>=0;j--){const a=trace[j];if(!Number.isFinite(a.x)||!Number.isFinite(a.z))continue;const d=Math.hypot(cue.x-a.x,cue.z-a.z);if(d<.015)continue;\n      arrivalAngle=Math.acos(Math.max(-1,Math.min(1,Math.abs(((cue.x-a.x)*sector.axis.x+(cue.z-a.z)*sector.axis.z)/d))));break;}\n    const inSector=length>=sector.minDistance&&length<=sector.maxDistance&&angle<=sector.angleTolerance;\n    const arrivalAligned=arrivalAngle!==null&&arrivalAngle<=sector.arrivalTolerance;\n    return {met:inSector,inSector,distance:length,angle,arrivalAngle,arrivalAligned};\n  }\n  function transitionGraph(state,limit=12) {\n    const balls=(state.balls||[]).filter(active),cue=balls.find(b=>b.n===0),allReds=balls.filter(b=>b.n===1),colours=balls.filter(b=>b.n>=2),edges=[];\n    const open=cue?attackRoutes(state,cue,allReds):[],openIds=new Set(open.map(r=>r.targetIndex));\n    const pocketableReds=allReds.filter(b=>(state.pockets||[]).some(p=>pocketAccepts(b,p)&&clear(state,b,p,radius(b),[cue?.i,b.i]))||openIds.has(b.i))\n      .sort((a,b)=>Number(openIds.has(b.i))-Number(openIds.has(a.i))||\n        Math.min(...(state.pockets||[{x:0,z:0}]).map(p=>distance(a,p)))-Math.min(...(state.pockets||[{x:0,z:0}]).map(p=>distance(b,p))));\n    const toReds=(pocketableReds.length?pocketableReds:allReds).slice(0,6);\n    const fromReds=state.rules?.ballOn===2&&openIds.size?allReds.filter(b=>openIds.has(b.i)).slice(0,5):toReds;\n    const poolReds=[...new Map([...fromReds,...toReds].map(b=>[b.i,b])).values()];\n    const sectorTargets=[...poolReds,...colours],ignoredIds=sectorTargets.map(b=>b.i);\n    const sectorsById=new Map(sectorTargets.map(b=>[b.i,positionSectors(state,b,24,ignoredIds)]));\n    // All sectors aimed at one pocket share this geometry; keep caches private to this call.\n    const pocketGeometry=new Map();\n    for(const from of [...fromReds,...colours])for(const to of from.n===1?colours:toReds){\n      const sectors=sectorsById.get(to.i);if(!sectors?.length)continue;\n      let byPocket=pocketGeometry.get(to);if(!byPocket){byPocket=new Map();pocketGeometry.set(to,byPocket);}\n      const pocketClear=new Map(),excluded=[cue.i,to.i,from.i];\n      for(const sector of sectors){\n        const p=sector.pocketIndex;let path=byPocket.get(p);\n        if(!path){const pocket=state.pockets[p],toward=unit(to,pocket);\n          path={pocket,ghost:{x:to.x-toward.x*(radius(cue)+radius(to)),z:to.z-toward.z*(radius(cue)+radius(to))}};byPocket.set(p,path);}\n        const {pocket,ghost}=path;\n        let laneClear=pocketClear.get(p);\n        if(laneClear===undefined){laneClear=clear(state,to,pocket,radius(to),excluded);pocketClear.set(p,laneClear);}\n        if(!laneClear||!clear(state,sector.centre,ghost,radius(cue),excluded))continue;\n        const travel=distance(from,sector.centre);edges.push({fromId:from.i,toId:to.i,sectorId:sector.id,sector,priority:sector.priority/(.2+travel)});}}\n    const ranked=edges.sort((a,b)=>b.priority-a.priority),out=[];\n    for(const from of [...fromReds,...colours])out.push(...ranked.filter(e=>e.fromId===from.i).slice(0,2));\n    for(const edge of out.filter(e=>fromReds.some(b=>b.i===e.fromId))){const successor=out.find(e=>e.fromId===edge.toId&&e.toId!==edge.fromId);edge.successor=successor?{fromId:successor.fromId,toId:successor.toId,sectorId:successor.sectorId}:null;}\n    return out.sort((a,b)=>b.priority-a.priority).slice(0,limit);\n  }\n  function shadowZones(state,on=targets(state)) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0),out=[],bounds=state.bounds;if(!cue)return out;\n    for(const blocker of (state.balls||[]).filter(b=>active(b)&&b.n>0&&!on.some(t=>t.i===b.i)))for(const target of on){\n      const axis=unit(target,blocker);if(!axis)continue;\n      let visibleTarget=null;\n      for(const length of [.10,.22,.36]){const centre={x:blocker.x+axis.x*length,z:blocker.z+axis.z*length};\n        if(bounds&&(centre.x<bounds.minX+radius(cue)||centre.x>bounds.maxX-radius(cue)||centre.z<bounds.minZ+radius(cue)||centre.z>bounds.maxZ-radius(cue)))continue;\n        const shadowCue={...cue,...centre};\n        let hidden=true;\n        if(visibleTarget&&edgeVisibility(state,shadowCue,visibleTarget,true)!==0)hidden=false;\n        else for(const t of on){if(t===visibleTarget)continue;if(edgeVisibility(state,shadowCue,t,true)!==0){visibleTarget=t;hidden=false;break;}}\n        if(hidden){out.push({id:`shadow-${blocker.i}-${target.i}-${length}`,hideBehindBallId:blocker.i,centre,radius:.045});if(out.length===12)return out;}}}\n    return out;\n  }\n  function edgeVisibility(state,cue,target,stopAtFirst) {\n    const length=distance(cue,target);if(!(length>1e-9))return 0;\n    const cueRadius=radius(cue),r=cueRadius+radius(target),excluded=[cue.i,target.i];\n    if(length<=r)return clear(state,cue,target,cueRadius,excluded)?2:0;\n    const tangent=Math.asin(Math.min(1,r/length)),angle=Math.atan2((target.z-cue.z)/length,(target.x-cue.x)/length),travel=Math.sqrt(length*length-r*r);\n    let visible=0;\n    for(let sign=-1;sign<=1;sign+=2){const a=angle+sign*tangent,contact={x:cue.x+Math.cos(a)*travel,z:cue.z+Math.sin(a)*travel};if(clear(state,cue,contact,cueRadius,excluded)){visible++;if(stopAtFirst)return visible;}}\n    return visible;\n  }\n  function visibleEdges(state,cue,target) { return edgeVisibility(state,cue,target,false); }\n\n  return {generate,generateRecovery,refine,roundRobin,routeKey,diverse,softContacts,targets,plantRoutes,doubleRoutes,attackRoutes,opportunity,clear,evaluate,positionSectors,transitionGraph,sectorCheck,shadowZones,visibleEdges};\n})();\nif(typeof module!=='undefined'&&module.exports)module.exports=PCOLSearchGeometry;\n\n\n/* Bounded geometric proxies, not calibrated pot probabilities or opponent trials. */\nconst PCOLTacticalPolicy = (() => {\n  const core=typeof PCOLCore!=='undefined'?PCOLCore:typeof require==='function'?require('./rules-core'):null;\n  const skill=()=>typeof PCOLShotSkill!=='undefined'?PCOLShotSkill:require('./shot-skill');\n  const active=b=>b.active!==false;\n  const dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);\n  const clamp=n=>Math.max(0,Math.min(1,n));\n  function analyze(state) {\n    const scores=state.scores||state.rules?.scores||[0,0],actor=state.rootPlayerIndex??state.rules?.playerIndex??0;\n    const deficit=(scores[1-actor]||0)-(scores[actor]||0);\n    const remaining=Number.isFinite(state.remainingPoints)?state.remainingPoints:null;\n    const liveReds=(state.balls||[]).filter(b=>active(b)&&b.n===1).length;\n    const snookersInHand=remaining!==null&&-deficit>remaining;\n    const shallowNeedSnookers=remaining!==null&&deficit>remaining&&(deficit-remaining)<=12&&liveReds>=3;\n    return {objective:remaining!==null&&deficit>remaining?'need-snookers':deficit<0&&remaining!==null&&-deficit>remaining*.55?'contain':'build',\n      style:'unified',deficit,remainingPoints:remaining,\n      snookersInHand,shallowNeedSnookers};\n  }\n  function routeQuality(route,scale) {\n    return clamp((route.cut||.15)**1.5/(1+2*(route.travel||0)/scale));\n  }\n  function aggregate(state,values) {\n    const context=analyze(state),mean=values.reduce((a,b)=>a+b,0)/values.length;\n    const downside=Math.max(0,mean-Math.min(...values));\n    const lead=-(context.deficit||0),remaining=Math.max(1,context.remainingPoints||1);\n    const riskPreference=.12+.18*clamp(lead/remaining);\n    return {score:mean-riskPreference*downside,mean,downside,riskPreference};\n  }\n  function layout(state,geometry) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0),on=geometry.targets(state,state.rules?.ballOn,null);\n    const b=state.bounds,scale=b?Math.hypot(b.maxX-b.minX,b.maxZ-b.minZ):2;\n    if(!cue)return {best:0,lanes:0,edgeVisibility:0,rail:1,access:0,buried:1,mobility:0};\n    const routes=geometry.attackRoutes(state,cue,on).map(r=>{\n      const potId=r.potTargetIndex??r.targetIndex;\n      const target=on.find(b=>b.i===potId)||on.find(b=>b.i===r.targetIndex),nominee=state.rules?.freeBallNominee===r.targetIndex;\n      const mask=state.rules?.ballOn||0,nominated=state.rules?.nominatedColour;\n      const points=nominee?(mask===2?1:mask===252?(nominated||target?.n||2):Math.max(0,...[2,3,4,5,6,7].filter(n=>mask&(1<<n)))):target?.n||0;\n      let quality=routeQuality(r,scale);\n      const level=state.rules?.playerIndex===(state.rootPlayerIndex??state.rules?.playerIndex)?state.skill:state.opponentSkill;\n      const pocket=state.pockets?.[r.pocketIndex];\n      if(level&&target&&pocket?.r&&r.direction&&!r.plant&&!r.doubleShot){\n        const shot={direction:r.direction,power:.3,vertical:0};\n        const uncertainty=skill().describe(state,{...r,shot},level);\n        const tolerance=Math.atan2(Math.max(0,pocket.r-(target.r||.026))*(r.cut||.15),Math.max(.01,r.travel||dist(cue,target)+dist(target,pocket)));\n        quality*=clamp(tolerance/(Math.sqrt(3)*uncertainty.angleSigma));\n      }\n      return {...r,quality,pointValue:quality*points};\n    }).sort((a,b)=>b.pointValue-a.pointValue);\n    const best=routes[0],alternative=routes.find(r=>r.targetIndex!==best?.targetIndex);\n    const third=routes.find(r=>r.targetIndex!==best?.targetIndex&&r.targetIndex!==alternative?.targetIndex);\n    const mobility=clamp((best?.quality||0)+.45*(alternative?.quality||0)+.2*(third?.quality||0));\n    let visible=0,total=0;\n    for(const target of on){\n      const d=dist(cue,target);if(!d)continue;\n      const dx=(target.x-cue.x)/d,dz=(target.z-cue.z)/d,offset=(cue.r||.026)+(target.r||.026);\n      for(const edge of [-.8,0,.8]){\n        total++;\n        if(geometry.clear(state,cue,{x:target.x-dz*offset*edge,z:target.z+dx*offset*edge},cue.r||.026,[cue.i,target.i]))visible++;\n      }\n    }\n    const rail=b?clamp(1-Math.min(cue.x-b.minX,b.maxX-cue.x,cue.z-b.minZ,b.maxZ-cue.z)/(.12*scale)):0;\n    const neighbours=(state.balls||[]).filter(ball=>active(ball)&&ball.n>0&&dist(cue,ball)<.13).length;\n    // Accessibility counts target/pocket lanes independently of the cue path.\n    let accessible=0;\n    for(const target of on)if((state.pockets||[]).some(p=>geometry.clear(state,target,p,target.r||.026,[cue.i,target.i])))accessible++;\n    const effectiveMask=state.rules?.ballOn===252&&state.rules?.nominatedColour?1<<state.rules.nominatedColour:state.rules?.ballOn;\n    const snooker=geometry.visibleEdges?null:core?.isSnookered(state.balls||[],effectiveMask,undefined,{inHand:!!state.rules?.inHand});\n    const direct=core?.hasDirectHit(state.balls||[],effectiveMask,undefined,{inHand:!!state.rules?.inHand});\n    return {best:best?.quality||0,pointValue:best?.pointValue||0,bestQuality:Math.max(0,...routes.map(r=>r.quality)),\n      snookered:geometry.visibleEdges?on.length>0&&on.every(target=>geometry.visibleEdges(state,cue,target)===0):snooker?.snookered??null,hasDirectHit:direct?.hasDirectHit??null,\n      bestTargetIndex:best?.targetIndex??null,alternative:alternative?.quality||0,\n      alternativeTargets:Math.max(0,new Set(routes.map(r=>r.targetIndex)).size-1),targets:on.length,mobility,\n      lanes:routes.length,edgeVisibility:total?visible/total:0,\n      rail,access:on.length?accessible/on.length:0,buried:clamp(neighbours/3)};\n  }\n  function accessibleReds(state,ids,geometry) {\n    const cue=(state.balls||[]).find(b=>active(b)&&b.n===0);\n    return new Set((state.balls||[]).filter(b=>active(b)&&b.n===1&&ids.has(b.i)&&\n      (state.pockets||[]).some(p=>geometry.clear(state,b,p,b.r||.026,[cue?.i,b.i]))).map(b=>b.i));\n  }\n  function blockerResources(state) {\n    const live=(state.balls||[]).filter(b=>active(b)&&b.n>0),on=core?.ballOnNumbers(state.rules?.ballOn||0)||[];\n    return live.filter(b=>!on.includes(b.n)).length;\n  }\n  function classify(state,candidate,result,geometry,prepared) {\n    const verdict=result.adjudication||{};\n    if(verdict.foulCode)return 'escape';\n    if(verdict.score>0)return 'attack';\n    const rules={...state.rules,...result.nextSnapshot?.rules,...result.nextContext};\n    rules.ballOn=result.nextContext?.ballOn??result.nextSnapshot?.rules?.ballOn??verdict.nextBallOn??state.rules?.ballOn;\n    const next={...state,balls:result.nextBalls||state.balls,rules};\n    const before=prepared?(prepared.root.before??=(prepared.root.layout?prepared.root.layout(state):layout(state,geometry))):layout(state,geometry);\n    // Classification retains declarations; evaluation clears them for the next turn.\n    const sameNext=prepared&&next.balls===prepared.next.balls&&\n      Object.keys(rules).every(k=>rules[k]===prepared.next.rules[k])&&\n      Object.keys(prepared.next.rules).every(k=>rules[k]===prepared.next.rules[k]);\n    const after=sameNext?prepared.after:prepared?.root.layout?prepared.root.layout(next):layout(next,geometry);\n    if(before.hasDirectHit===false&&after.hasDirectHit!==false)return 'escape';\n    if(after.snookered===true)return 'snooker';\n    if(after.bestQuality<.2&&after.pointValue<1)return 'contain';\n    return 'exposure';\n  }\n  function prepareRoot(state,geometry) {\n    const redIds=new Set((state.balls||[]).filter(b=>active(b)&&b.n===1).map(b=>b.i));\n    return {context:analyze(state),redIds,oldAccess:accessibleReds(state,redIds,geometry),\n      scale:state.bounds?Math.hypot(state.bounds.maxX-state.bounds.minX,state.bounds.maxZ-state.bounds.minZ):2,\n      blockersBefore:blockerResources(state),shadowBefore:geometry.shadowZones?geometry.shadowZones(state).length:0};\n  }\n  // A session belongs to one bounded search. Ordinary evaluate calls still accept mutable inputs.\n  function createSession(geometry) {\n    const roots=new WeakMap(),layouts=new WeakMap();\n    // Both unset declaration forms are geometric equivalents; an actual nomination is distinct.\n    const sameRules=(a={},b={})=>[...new Set([...Object.keys(a),...Object.keys(b)])].every(k=>\n      a[k]===b[k]||['nominatedColour','freeBallNominee'].includes(k)&&a[k]==null&&b[k]==null);\n    function cachedLayout(state) {\n      const balls=state.balls;\n      if(!balls||typeof balls!=='object')return layout(state,geometry);\n      let entries=layouts.get(balls);\n      const cached=entries?.find(e=>e.bounds===state.bounds&&e.pockets===state.pockets&&e.skill===state.skill&&e.opponentSkill===state.opponentSkill&&e.rootPlayerIndex===state.rootPlayerIndex&&sameRules(e.rules,state.rules));\n      if(cached)return cached.value;\n      const value=layout(state,geometry);\n      if(!entries){entries=[];layouts.set(balls,entries);}\n      entries.push({bounds:state.bounds,pockets:state.pockets,rules:state.rules,skill:state.skill,opponentSkill:state.opponentSkill,rootPlayerIndex:state.rootPlayerIndex,value});\n      return value;\n    }\n    return {layout:cachedLayout,evaluate(state,candidate,result){\n      let root=roots.get(state);\n      if(!root){root={...prepareRoot(state,geometry),layout:cachedLayout,results:new WeakMap()};roots.set(state,root);}\n      return evaluate(state,candidate,result,geometry,root);\n    }};\n  }\n  function createEvaluator(state,geometry) {\n    const session=createSession(geometry);\n    return (candidate,result)=>session.evaluate(state,candidate,result);\n  }\n  function evaluate(state,candidate,result,geometry,preparedRoot) {\n    const verdict=result.adjudication||{},points=Number.isFinite(verdict.score)?verdict.score:0;\n    const root=state.rootPlayerIndex??state.rules?.playerIndex??0,actor=state.rules?.playerIndex??0;\n    const nextRules={...state.rules,...result.nextSnapshot?.rules,...result.nextContext};\n    nextRules.ballOn=result.nextContext?.ballOn??result.nextSnapshot?.rules?.ballOn??verdict.nextBallOn;\n    nextRules.playerIndex=result.nextContext?.playerIndex??result.nextSnapshot?.rules?.playerIndex??(verdict.continueBreak?actor:1-actor);\n    const stays=nextRules.playerIndex===root;\n    const next={...state,balls:result.nextBalls||[],rules:{...nextRules,nominatedColour:null,freeBallNominee:null}};\n    const rootData=preparedRoot||prepareRoot(state,geometry),facts=rootData.results?.get(result)||{};\n    if(rootData.results)rootData.results.set(result,facts);\n    const after=facts.after??=(rootData.layout?rootData.layout(next):layout(next,geometry));\n    const {context,redIds,oldAccess,scale,blockersBefore,shadowBefore}=rootData;\n    const newAccess=facts.newAccess??=accessibleReds(next,redIds,geometry);\n    const freedRedIds=[...newAccess].filter(i=>!oldAccess.has(i));\n    // Fixed original-red denominator: a pot or red/colour phase change cannot inflate development.\n    const development=(redIds.size?freedRedIds.length/redIds.size:0)*(1-after.buried)*(1-after.rail);\n    const effect=facts.effect??=classify(state,candidate,result,geometry,{root:rootData,next,after,newAccess});\n    const difficulty=effect==='attack'?1-routeQuality(candidate,scale):0;\n    const features={scoreDelta:points,objective:context.objective,style:context.style,routeDifficulty:difficulty,\n      nextChance:stays?after.best:0,nextTargetIndex:stays?after.bestTargetIndex:null,\n      alternativeLanes:stays?after.alternative||0:0,alternativeTargets:stays?after.alternativeTargets||0:0,\n      opponentChance:stays?0:after.best,opponentTargetIndex:stays?null:after.bestTargetIndex,\n      visibleTargetEdges:after.edgeVisibility,cueRailRestriction:after.rail,cueBuried:after.buried,\n      clusterAccessibility:redIds.size?newAccess.size/redIds.size:0,freedRedIds,\n      development,laneAvailability:after.lanes};\n    const netPoints=points*(actor===root?1:-1);\n    // All values use points. Route quality is a bounded proxy for short-horizon value.\n    const leaf=(after.pointValue||0)+.6*(after.alternative||0)+.25*Math.min(2,after.alternativeTargets||0);\n    let futureValue=stays?leaf:-leaf;\n    const baseScores=state.scores||state.rules?.scores||[0,0];\n    const derivedScores=baseScores.map((score,index)=>score+(points>0&&index===actor?points:points<0&&index!==actor?-points:0));\n    const scores=result.nextContext?.scores||result.nextSnapshot?.rules?.scores||derivedScores;\n    const early=!verdict.foulCode&&core?.earlyFrameOutcome({balls:next.balls,ballOn:next.rules.ballOn,scores,playerIndex:nextRules.playerIndex,\n      actor,continueBreak:!!verdict.continueBreak,freeBall:!!nextRules.freeBallAvailable,freeBallReview:!!nextRules.freeBallReview});\n    const terminal=verdict.frameOutcome==='end'||nextRules.ballOn===0||!!early;\n    const margin=(scores[root]||0)-(scores[1-root]||0);\n    const remaining=core?.remainingPoints(next.balls,next.rules.ballOn);\n    const removed=Number.isFinite(state.remainingPoints)&&Number.isFinite(remaining)?Math.max(0,state.remainingPoints-remaining):0;\n    const blockersAfter=blockerResources(next);\n    const blockerDelta=blockersAfter-blockersBefore;\n    const live=(next.balls||[]).filter(b=>active(b)&&b.n>0);\n    const liveRedsAfter=live.filter(b=>b.n===1).length;\n    const mathematicallyDead=margin< -7&&live.length===1&&live[0].n===7;\n    const cue=next.balls.find(b=>active(b)&&b.n===0),bounds=next.bounds;\n    const cueBaulk=bounds&&cue?clamp(1-(cue.x-bounds.minX)/(bounds.maxX-bounds.minX)):0;\n    const displaced=facts.displaced??=(next.balls||[]).filter(b=>active(b)&&b.n>0&&state.balls.some(old=>old.i===b.i&&dist(old,b)>.02));\n    const objectBallLeak=facts.objectBallLeak??=(()=>{\n      const legalIds=new Set(geometry.targets(next,next.rules.ballOn,null).map(b=>b.i));\n      const displacedLegal=displaced.filter(b=>legalIds.has(b.i));\n      const leakRoutes=!stays&&cue?geometry.attackRoutes(next,cue,displacedLegal):[];\n      return stays?0:leakRoutes.reduce((best,route)=>{\n        const target=displacedLegal.find(b=>b.i===route.targetIndex);\n        const proximity=target?Math.max(0,...(next.pockets||[]).map(p=>clamp(1-dist(target,p)/(.18*scale)))):0;\n        return Math.max(best,routeQuality(route,scale)*(1+proximity));\n      },0);\n    })();\n    const stillNeedsSnookers=Number.isFinite(remaining)&&-margin>remaining;\n    const snookerGap=Number.isFinite(remaining)?Math.max(0,-margin-remaining):0;\n    const shallowComeback=stillNeedsSnookers&&liveRedsAfter>=2&&snookerGap<=12&&(points>=5||(points===1&&stays&&after.best>=.25));\n    const clinchAfter=Number.isFinite(remaining)&&margin>remaining;\n    const clinchBonus=!verdict.foulCode&&clinchAfter&&netPoints>0?(context.snookersInHand?1.5:3.5):0;\n    const recoveryCost=context.objective==='need-snookers'&&margin<0&&!shallowComeback?Math.max(0,removed-Math.max(0,netPoints)):0;\n    const shadowAfter=facts.shadowAfter??=(geometry.shadowZones?geometry.shadowZones(next).length:0);\n    const shadowDelta=clamp(shadowAfter/6)-clamp(shadowBefore/6);\n    const lostObjects=(state.balls||[]).filter(b=>active(b)&&b.n>0&&!live.some(n=>n.i===b.i)).length;\n    const resourceValue=stillNeedsSnookers&&!shallowComeback?(2*blockerDelta-4*lostObjects+6*shadowDelta)+(!stays&&after.snookered?6:0):\n      stillNeedsSnookers&&!stays&&after.snookered?6:0;\n    const scoringDiscount=stillNeedsSnookers&&netPoints>0?(shallowComeback?-.15*netPoints:-.85*netPoints):0;\n    if(stillNeedsSnookers&&futureValue>0)futureValue*=shallowComeback?.75:.15;\n    const incomingSign=nextRules.playerIndex===root?1:-1;\n    const effectiveLeak=clinchAfter?objectBallLeak*.2:objectBallLeak;\n    const defensiveValue=verdict.continueBreak?0:-incomingSign*((cueBaulk+after.rail)*(1-Math.min(1,effectiveLeak))-3*effectiveLeak);\n    const openingBonus=candidate?.opening&&!verdict.foulCode&&!stays&&bounds&&cue?\n      (cueBaulk>=.68?2.5*cueBaulk*(1-Math.min(1,after.best*2)):-5*Math.max(0,.6-cueBaulk)):0;\n    const safeMiss=!verdict.foulCode&&points===0&&!stays&&after.best<.22&&objectBallLeak<.25&&(cueBaulk>=.55||after.rail>=.5||after.snookered===true);\n    const costlyMiss=!verdict.foulCode&&points===0&&!stays&&(after.best>=.35||objectBallLeak>=.35);\n    const twoWayPotential=!verdict.foulCode&&points>0&&stays&&(cueBaulk>=.58||after.rail>=.55);\n    const immediateCost=-recoveryCost+resourceValue+defensiveValue+scoringDiscount+clinchBonus+openingBonus;\n    const terminalValue=terminal?(margin>0?100000:margin<0?-100000:0):0;\n    if(terminal)futureValue=0;\n    Object.assign(features,{netPoints,immediateCost,futureValue,terminalValue,nextPlayerIndex:nextRules.playerIndex,routeQualityProxy:1-difficulty,\n      snookered:after.snookered,opponentSnookered:!stays&&after.snookered===true,selfSnookered:stays&&after.snookered===true,\n      hasDirectHit:after.hasDirectHit,remainingPoints:remaining,recoveryCost,effect,blockersBefore,blockersAfter,blockerDelta,resourceValue,stillNeedsSnookers,shallowComeback,clinchAfter,scoringDiscount,shadowBefore,shadowAfter,shadowDelta,lostObjects,earlyFrameReason:early?.reason||null,\n      cueBaulk,objectBallLeak,mobility:stays?after.mobility||0:0,safeMiss,costlyMiss,twoWayPotential,displacedObjectBallIds:displaced.map(b=>b.i),mathematicallyDead});\n    return {score:netPoints+immediateCost+futureValue+terminalValue,netPoints,immediateCost,futureValue,terminalValue,features};\n  }\n  function estimate(state,geometry) {\n    const after=layout(state,geometry);\n    return {value:after.pointValue||0,layout:after};\n  }\n  // Optional concession reuses the finished local search; it never runs another trial.\n  // Poor bounded observations support a practical choice, never a claim of impossibility.\n  function concession(state,decision,geometry) {\n    const rules=state.rules||{},actor=rules.playerIndex,scores=state.scores||rules.scores;\n    const evidence={policy:'position-and-local-evidence-v1',actor,\n      interpretation:'execution observations, not calibrated win probabilities'};\n    const finish=(action,reason)=>({action,reason,evidence});\n    if(!core||!Array.isArray(state.balls)||!Array.isArray(scores)||scores.length!==2||!scores.every(Number.isFinite)||\n      ![0,1].includes(actor)||!rules.ballOn||rules.ballOn===65535)\n      return finish('continue','incomplete-position');\n    if(state.pending||rules.freeBallReview||rules.freeBallAvailable&&!rules.freeBallDeclined&&rules.freeBallNominee==null)\n      return finish('continue','unresolved-turn-options');\n    const status=core.concessionStatus({balls:state.balls,ballOn:rules.ballOn,scores,playerIndex:actor,\n      freeBall:!!rules.freeBallAvailable&&!rules.freeBallDeclined});\n    Object.assign(evidence,{deficit:status.deficit,remaining:status.remaining,excess:status.excess,\n      minimumFoulEvents:Math.ceil(Math.max(0,status.excess)/7)});\n    if(!status.eligible)return finish('continue','not-beyond-table-points');\n    const search=decision?.search||decision||{},selected=decision?.candidate||decision?.selected;\n    const candidates=[...new Map([selected,...(decision?.shortlist||decision?.candidates||[])].filter(Boolean)\n      .map(c=>[c.id||c,c])).values()];\n    const categories=search.categoryBest||{};\n    if(categories.snooker?.snookered===true||candidates.some(c=>c.evidence?.nominal?.legal===true&&\n      (c.features?.opponentSnookered===true||(c.evidence.samples||[]).some(r=>r.legal&&r.nextActor!==actor&&r.opponentSnookered))))\n      return finish('continue','verified-snooker-available');\n    if(categories.contain?.points===0&&Number.isFinite(categories.contain.opponentChance)&&categories.contain.opponentChance<.2||\n      candidates.some(c=>c.evidence?.nominal?.legal===true&&(c.features?.safeMiss===true||c.risk?.safeMissRate>0||\n        c.evidence.nominal.nextActor!==actor&&c.features?.effect==='contain'&&c.features.opponentChance<.2)))\n      return finish('continue','verified-safe-defense-available');\n    if(candidates.some(c=>c.evidence?.nominal?.legal===true&&(c.features?.shallowComeback===true||\n      c.features?.shadowAfter>c.features?.shadowBefore||c.features?.blockerDelta>0)))\n      return finish('continue','recovery-resources-can-improve');\n    if(!['complete','candidate-limit','budget-exhausted'].includes(search.status)||!geometry?.shadowZones)\n      return finish('continue','incomplete-search-evidence');\n    // Two distinct routes and their existing paired execution samples are a minimum\n    // safeguard against conceding from one failed seed or an interrupted risk check.\n    const routes=new Set(candidates.map(c=>geometry.routeKey?geometry.routeKey(c):[c.kind,c.targetIndex,c.pocketIndex].join(':')));\n    const complete=c=>{\n      const f=c.features,r=c.risk,rows=c.evidence?.samples,n=c.evidence?.nominal;\n      return n?.legal===true&&f&&Number.isFinite(f.opponentChance)&&Number.isFinite(f.objectBallLeak)&&\n        r?.coverage==='complete'&&r.samples>=2&&!r.incomplete&&Array.isArray(rows)&&rows.length===r.samples&&\n        Number.isFinite(r.costlyMissRate)&&rows.every(row=>typeof row.legal==='boolean'&&Number.isFinite(row.points)&&\n          [0,1].includes(row.nextActor)&&typeof row.opponentSnookered==='boolean');\n    };\n    if(routes.size<2||!candidates.every(complete))return finish('continue','incomplete-recovery-evidence');\n    const shadows=geometry.shadowZones(state),usefulBlockers=new Set(shadows.map(s=>s.hideBehindBallId)).size;\n    const liveReds=state.balls.filter(b=>active(b)&&b.n===1).length;\n    Object.assign(evidence,{blockers:blockerResources(state),usefulBlockers,shadowZones:shadows.length,liveReds,\n      routes:routes.size,candidates:candidates.map(c=>{\n        const n=c.risk.samples,fouls=c.evidence.samples.filter(r=>!r.legal).length;\n        return {id:c.id,samples:n,fouls,costlyMisses:Math.round(c.risk.costlyMissRate*n),\n          opponentChanceProxy:c.features.opponentChance,mathematicallyDead:!!c.features.mathematicallyDead};\n      })});\n    // A blocker can be reused; these counts express scarce resources, not a limit\n    // on how many fouls a position can ever produce. Several reds keep options open.\n    const scarce=usefulBlockers===0||evidence.minimumFoulEvents>=2&&usefulBlockers===1&&shadows.length<=3;\n    if(!scarce||liveReds>=3)return finish('continue','defensive-resources-remain');\n    const poor=c=>{\n      const f=c.features,n=c.evidence.nominal,observed=evidence.candidates.find(row=>row.id===c.id);\n      const poorNominal=f.mathematicallyDead===true||f.costlyMiss===true||\n        n.nextActor!==actor&&(f.opponentChance>=.35||f.objectBallLeak>=.35)||\n        f.stillNeedsSnookers===true&&f.blockerDelta<0&&f.shadowAfter<=f.shadowBefore;\n      const minimumBad=evidence.minimumFoulEvents>=2?Math.ceil(observed.samples/2):observed.samples;\n      return poorNominal&&(f.mathematicallyDead===true||observed.fouls+observed.costlyMisses>=minimumBad);\n    };\n    return candidates.every(poor)?finish('concede','weak-tested-recovery-and-scarce-blockers'):\n      finish('continue','recovery-evidence-not-poor-enough');\n  }\n  return {analyze,aggregate,evaluate,createEvaluator,createSession,layout,estimate,classify,concession};\n})();\n\n/* Local geometric intentions; native trials establish achievement. */\nconst PCOLTacticalBrain=(()=>{\n const live=b=>b.active!==false&&Number.isFinite(b.x)&&Number.isFinite(b.z),dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z),tasks=['position','build','contain','need-snookers','escape','develop'];\n function analyze(state,g){\n  const balls=(state.balls||[]).filter(live),cue=balls.find(b=>b.n===0),on=g.targets(state),routes=cue?g.attackRoutes(state,cue,on):[],reds=balls.filter(b=>b.n===1);\n  const graph=g.transitionGraph(state,24),sectors=[...new Map(graph.map(e=>[e.sector.id,e.sector])).values()];\n  const clusters=reds.filter(b=>reds.some(c=>c.i!==b.i&&dist(b,c)<2.5*(b.r||.026))).map(b=>b.i);\n  const pockets=state.pockets||[],hangingIds=reds.filter(b=>pockets.some(p=>dist(b,p)<=.22)).map(b=>b.i);\n  const preserveIds=[...new Set(graph.map(e=>e.toId))].filter(i=>!clusters.includes(i)&&!hangingIds.includes(i)).slice(0,4);\n  const actor=state.rules?.playerIndex||0,scores=state.scores||state.rules?.scores||[0,0],deficit=(scores[1-actor]||0)-(scores[actor]||0),remainingPoints=state.remainingPoints??reds.length*8+balls.filter(b=>b.n>=2).reduce((n,b)=>n+b.n,0);\n  const hasGoodPot=routes.some(r=>(r.cut||0)>=.38);\n  const shallowComeback=deficit>remainingPoints&&(deficit-remainingPoints)<=12&&reds.length>=3&&hasGoodPot;\n  const directlyReachable=cue&&on.some(t=>g.clear(state,cue,t,cue.r||.026,[cue.i,t.i])||g.visibleEdges(state,cue,t)>0);\n  const task=deficit>remainingPoints?(shallowComeback?'position':'need-snookers'):!routes.length?(directlyReachable?'contain':'escape'):-deficit>remainingPoints*.55&&!hasGoodPot?'contain':'position';\n  const edge=graph.find(e=>routes.some(r=>r.targetIndex===e.fromId)),targetId=edge?.fromId??routes[0]?.targetIndex??on[0]?.i??null;\n  const primary={task,targetId,nextBallId:edge?.toId??null,sectorId:edge?.sectorId??null,preserveIds:preserveIds.filter(i=>i!==targetId)};\n  const fallback={task:deficit>remainingPoints?'need-snookers':routes.length||directlyReachable?'contain':'escape',targetId,nextBallId:null,sectorId:null,preserveIds:primary.preserveIds};\n  return {task,allowedTasks:tasks.slice(),tasks:tasks.slice(),ballIds:balls.filter(b=>b.n>0).map(b=>b.i),targetIds:on.map(b=>b.i),sectors,transitionGraph:graph,defaultPrimary:primary,defaultFallback:fallback,primaryIntent:primary,fallbackIntent:fallback,preserveIds,problemOrder:clusters,roles:{problemIds:clusters,insuranceIds:preserveIds,keyColourIds:balls.filter(b=>b.n>=5).map(b=>b.i),transitionIds:graph.map(e=>e.toId),hangingIds},shadowZones:g.shadowZones(state,on),scoreboard:{scores,deficit,remainingPoints}};\n }\n function normalizePlan(raw,brief){\n  raw=raw&&typeof raw==='object'?raw:{};\n  const normalize=(input,base)=>{input=input&&typeof input==='object'?input:{};const targetId=brief.targetIds.includes(input.targetId)?input.targetId:base.targetId;\n   const edge=brief.transitionGraph.find(e=>e.fromId===targetId&&e.toId===input.nextBallId&&(input.sectorId==null||e.sectorId===input.sectorId))||brief.transitionGraph.find(e=>e.fromId===targetId);\n   const sector=brief.sectors.find(s=>s.id===input.sectorId&&s.targetId===(input.nextBallId??edge?.toId));\n   return {task:tasks.includes(input.task)?input.task:base.task,targetId,nextBallId:sector?.targetId??edge?.toId??null,sectorId:sector?.id??edge?.sectorId??null,preserveIds:[...new Set((Array.isArray(input.preserveIds)?input.preserveIds:base.preserveIds||[]).filter(i=>brief.ballIds.includes(i)&&i!==targetId&&!(brief.roles?.hangingIds||[]).includes(i)))].slice(0,4),...(brief.ballIds.includes(input.hideBehindBallId)?{hideBehindBallId:input.hideBehindBallId}:{}),reason:typeof input.reason==='string'?input.reason.slice(0,180):undefined};};\n  return {primaryIntent:normalize(raw.primaryIntent||raw,brief.defaultPrimary),fallbackIntent:normalize(raw.fallbackIntent,brief.defaultFallback),reason:typeof raw.reason==='string'?raw.reason.slice(0,180):'局部几何路线与下一杆走位'};\n }\n function directed(state,seeds,intent,g,brief=analyze(state,g)){\n  const sector=brief.sectors.find(s=>s.id===intent.sectorId),shadow=brief.shadowZones.find(z=>intent.hideBehindBallId==null||z.hideBehindBallId===intent.hideBehindBallId),zone=['contain','need-snookers'].includes(intent.task)?shadow?.centre:sector?.centre;\n  const attacking=['position','build','develop'].includes(intent.task),defensive=['contain','need-snookers'].includes(intent.task);\n  const eligible=seeds.filter(c=>c.shot&&(intent.targetId==null||c.targetIndex===intent.targetId)&&(!attacking||c.kind==='attack')&&(!defensive||c.kind==='safety'));\n  // Choose independent pot lanes before spending trials on spin; generator order interleaves safety and escape.\n  const lanes=new Map();for(const c of eligible){const key=[c.targetIndex,c.pocketIndex,Math.atan2(c.shot.direction.z,c.shot.direction.x).toFixed(5)].join(':');if(!lanes.has(key))lanes.set(key,c);}\n  const picked=[...lanes.values()].slice(0,defensive?7:4),out=[],groups=[];\n  for(const c of picked){const target=state.balls.find(b=>b.i===c.targetIndex);if(!target)continue;\n   const pocket=state.pockets[c.pocketIndex],length=pocket?dist(target,pocket):0,normal=length?{x:(pocket.x-target.x)/length,z:(pocket.z-target.z)/length}:c.shot.direction;\n   const incoming=c.shot.direction,dot=incoming.x*normal.x+incoming.z*normal.z,tangent={x:incoming.x-dot*normal.x,z:incoming.z-dot*normal.z},want=zone?{x:zone.x-target.x,z:zone.z-target.z}:{x:0,z:0},wantLength=Math.hypot(want.x,want.z),along=want.x*normal.x+want.z*normal.z;\n   const spin=Math.max(-.55,Math.min(.55,along/Math.max(.08,wantLength)*.55)),delta=zone?Math.min(.12,wantLength*.10):0,group=[];\n   for(const [powerDelta,vertical] of [[0,0],[delta,spin],[delta+.06,spin*.65],[-.04,spin],[delta*.5,-spin*.5],[delta+.03,0]]){\n    const outgoing={x:tangent.x+vertical*normal.x,z:tangent.z+vertical*normal.z},alignment=(outgoing.x*want.x+outgoing.z*want.z)/(Math.hypot(outgoing.x,outgoing.z)*wantLength||1);\n    group.push({...c,directed:true,requiresTrace:true,intentTask:intent.task,destinationAlignment:alignment,label:'任务几何走位',shot:{...c.shot,power:Math.max(.08,Math.min(.85,c.shot.power+powerDelta)),vertical,side:0,elevation:vertical<0?.025*Math.PI:0}});}\n   // Preserve a plain pot reference, then try the best predicted outgoing direction on each pocket.\n   group.splice(1,group.length-1,...group.slice(1).sort((a,b)=>b.destinationAlignment-a.destinationAlignment));\n   if(defensive){const originalVariant=eligible.find(s=>s.shot.power!==c.shot.power&&Math.abs(s.shot.direction.x-c.shot.direction.x)<1e-8&&Math.abs(s.shot.direction.z-c.shot.direction.z)<1e-8);\n    if(originalVariant)group.unshift(originalVariant);}\n   groups.push(group);\n   if((c.kind==='escape'&&/库|cushion|bank/i.test(c.label||''))||c.contacts?.some(e=>e.kind==='cushion'))group.push(...[-.18,.18].map(side=>({...c,directed:true,requiresTrace:true,label:'库边适度侧旋走位',shot:{...c.shot,side,vertical:0,elevation:0}})));\n  }\n  for(let variant=0;variant<8;variant++)for(const group of groups)if(group[variant])out.push(group[variant]);\n  if(zone&&['contain','need-snookers'].includes(intent.task)){\n   const cue=state.balls.find(b=>live(b)&&b.n===0),target=state.balls.find(b=>b.i===intent.targetId);if(cue&&target){const d=dist(cue,target),axis={x:(target.x-cue.x)/d,z:(target.z-cue.z)/d};\n    const variants=[];for(const thin of [-.94,-.8,-.55,.55,.8,.94]){const sum=(cue.r||.026)+(target.r||.026),aim={x:target.x-axis.z*thin*sum,z:target.z+axis.x*thin*sum},length=dist(cue,aim),direction={x:(aim.x-cue.x)/length,z:(aim.z-cue.z)/length};\n     if(!g.clear(state,cue,aim,cue.r||.026,[cue.i,target.i]))continue;const n={x:(aim.x-target.x)/sum,z:(aim.z-target.z)/sum},dot=direction.x*n.x+direction.z*n.z,outgoing={x:direction.x-dot*n.x,z:direction.z-dot*n.z},want={x:zone.x-aim.x,z:zone.z-aim.z},alignment=(outgoing.x*want.x+outgoing.z*want.z)/(Math.hypot(outgoing.x,outgoing.z)*Math.hypot(want.x,want.z)||1);\n     for(const power of [.18,.3,.45])variants.push({kind:'safety',targetIndex:target.i,hideBehindBallId:shadow?.hideBehindBallId,directed:true,requiresTrace:true,priority:alignment,label:'遮挡阴影薄球种子',shot:{direction,power,vertical:0,side:0,elevation:0}});}\n    const shadows=variants.sort((a,b)=>b.priority-a.priority).slice(0,12),plain=out.splice(0);\n    for(let i=0;i<Math.max(plain.length,shadows.length);i++){if(plain[i])out.push(plain[i]);if(shadows[i])out.push(shadows[i]);}}}\n  return out.slice(0,28);\n }\n function destination(state,intent,brief){return ['contain','need-snookers'].includes(intent.task)?brief.shadowZones.find(z=>intent.hideBehindBallId==null||z.hideBehindBallId===intent.hideBehindBallId)?.centre:brief.sectors.find(s=>s.id===intent.sectorId)?.centre;}\n function refineIntent(state,candidate,result,intent,g,brief=analyze(state,g)){\n  const zone=destination(state,intent,brief),cue=(result.nextBalls||result.balls||[]).find(b=>live(b)&&b.n===0),start=state.balls.find(b=>live(b)&&b.n===0);if(!zone||!cue||!start||!candidate.shot)return [];\n  const distance=dist(cue,zone),travel=dist(start,cue),dx=cue.x-start.x,dz=cue.z-start.z,projection=travel>1e-6?((zone.x-cue.x)*dx+(zone.z-cue.z)*dz)/travel:distance;\n  const correction=Math.max(-.12,Math.min(.12,projection/(Math.max(.1,travel)*2)*candidate.shot.power)),cushion=result.contacts?.some(c=>c.kind==='cushion'),base=candidate.shot;\n  const target=state.balls.find(b=>b.i===candidate.targetIndex),direction=base.direction,forward=target?(zone.x-cue.x)*direction.x+(zone.z-cue.z)*direction.z:projection,spinCorrection=Math.sign(forward)*Math.min(.2,distance*.4);\n  const specs=[[correction,0,0],[correction*.5,spinCorrection,0],[correction*1.4,-spinCorrection*.5,0],[-correction*.35,spinCorrection,0]];\n  if(cushion)specs.push([correction*.5,0,-.16],[correction*.5,0,.16]);else specs.push([0,spinCorrection*1.25,0],[correction*.8,0,0]);\n  return specs.map(([powerDelta,verticalDelta,side])=>({...candidate,parentCandidateId:candidate.id,directed:true,requiresTrace:true,destinationDistance:distance,refinement:'actual-destination-miss',shot:{...base,power:Math.max(.08,Math.min(.85,base.power+powerDelta)),vertical:Math.max(-.6,Math.min(.6,(base.vertical||0)+verticalDelta)),side:cushion?side:0,elevation:(base.vertical||0)+verticalDelta<0?.025*Math.PI:0}}));\n }\n function nextState(state,result){return {...state,balls:result.nextBalls||result.balls||[],rules:{...state.rules,...result.nextSnapshot?.rules,ballOn:result.adjudication?.nextBallOn??state.rules?.ballOn,freeBallNominee:null,nominatedColour:null}};}\n function compliance(state,expected,g){\n  if(!expected)return {met:false,reason:'missing expectation'};const cue=state.balls?.find(b=>live(b)&&b.n===0),target=state.balls?.find(b=>live(b)&&b.i===expected.targetId);\n  if(!cue||!target||!g.targets(state).some(b=>b.i===target.i))return {met:false,reason:'next target unavailable'};\n  const position=g.sectorCheck(cue,expected.sector),route=g.attackRoutes(state,cue,[target]).some(r=>expected.sector?.pocketIndex==null||r.pocketIndex===expected.sector.pocketIndex);\n  return {...position,routeAvailable:route,met:route,reason:route?'next route available':'next route blocked'};\n }\n function assess(state,candidate,result,intent,g,brief=analyze(state,g),options){\n  const next=nextState(state,result),cue=next.balls.find(b=>live(b)&&b.n===0),sector=brief.sectors.find(s=>s.id===intent.sectorId),position=g.sectorCheck(cue,sector,result.trace),foul=!!(result.adjudication?.foul||result.adjudication?.foulCode),potted=result.potted||[];\n  const expectedPotId=candidate?.potTargetIndex??intent.targetId;\n  const scored=(result.adjudication?.score||0)>0&&(potted.includes(intent.targetId)||potted.includes(expectedPotId)),continues=result.adjudication?.continueBreak===true;\n  const nextTargets=g.targets(next),nextRoutes=cue?g.attackRoutes(next,cue,nextTargets):[];\n  const pockets=state.pockets||[],hasReds=(state.balls||[]).some(b=>live(b)&&b.n===1);\n  let hasAlternative;\n  const preserveConsumed=(intent.preserveIds||[]).filter(i=>{\n   if(!potted.includes(i))return false;\n   const obj=(state.balls||[]).find(b=>b.i===i);\n   if(obj&&obj.n>=2&&(hasReds||(result.adjudication?.respots||[]).includes(i)))return false;\n   if(obj&&pockets.some(p=>dist(obj,p)<=.22))return false;\n   if(i===expectedPotId&&!foul&&continues){\n    if(nextRoutes.length>0)return false;\n    if(hasAlternative===undefined){const startCue=(state.balls||[]).find(b=>live(b)&&b.n===0);hasAlternative=!!startCue&&g.attackRoutes(state,startCue,g.targets(state)).some(r=>r.targetIndex!==expectedPotId&&(r.cut||0)>=.45);}\n    if(!hasAlternative)return false;\n   }\n   return true;\n  }).length;\n  const nextTarget=next.balls.find(b=>live(b)&&b.i===intent.nextBallId),targetPositionChanged=!!(sector&&nextTarget&&dist(nextTarget,sector.origin)>(nextTarget.r||.026));\n  const route=sector&&cue&&!targetPositionChanged?g.attackRoutes(next,cue,nextTargets.filter(b=>b.i===intent.nextBallId)).some(r=>r.pocketIndex===sector.pocketIndex):false;\n  const hidden=cue&&nextTargets.length>0&&nextTargets.every(t=>g.visibleEdges(next,cue,t)===0);\n  let developed=false;\n  if(!foul&&scored&&continues&&cue){\n   const clusterIds=candidate?.development?.clusterIds||brief.problemOrder||[],contact=result.contacts?.some(c=>clusterIds.includes(c.ballIndex));\n   if(contact&&clusterIds.some(i=>{const a=state.balls.find(b=>b.i===i),b=next.balls.find(b=>live(b)&&b.i===i);return a&&b&&dist(a,b)>(a.r||.026)*2;})){\n    const baseline={...state,balls:state.balls.filter(b=>!potted.includes(b.i))},beforeOpen=new Set(g.attackRoutes(baseline,cue,baseline.balls.filter(b=>live(b)&&b.n===1)).map(r=>r.targetIndex)),afterOpen=new Set(g.attackRoutes(next,cue,next.balls.filter(b=>live(b)&&b.n===1)).map(r=>r.targetIndex));\n    const freed=clusterIds.some(i=>afterOpen.has(i)&&!beforeOpen.has(i)),insuranceIds=candidate?.development?.insuranceIds||intent.preserveIds||[];\n    developed=freed&&(insuranceIds.some(i=>afterOpen.has(i)&&!clusterIds.includes(i))||(!!candidate?.development?.powerSplit&&!insuranceIds.length));\n   }\n  }\n  const defensive=['contain','need-snookers'].includes(intent.task);\n  const actor=state.rules?.playerIndex??0,nextActor=result.nextContext?.playerIndex??result.nextSnapshot?.rules?.playerIndex??(continues?actor:1-actor),handedOver=nextActor!==actor&&!continues&&(result.adjudication?.score||0)<=0&&potted.length===0;\n  const zone=destination(state,intent,brief),destinationDistance=cue&&zone?dist(cue,zone):null;\n  const b=state.bounds,fullTable=b&&(b.maxX-b.minX)>2.5,scale=b?Math.hypot(b.maxX-b.minX,b.maxZ-b.minZ):2;\n  const cueBaulk=b&&cue?Math.max(0,Math.min(1,1-(cue.x-b.minX)/(b.maxX-b.minX))):0;\n  const rail=b&&cue?Math.max(0,Math.min(1,1-Math.min(cue.x-b.minX,b.maxX-cue.x,cue.z-b.minZ,b.maxZ-cue.z)/(.12*scale))):0;\n  const containSafe=!fullTable||cueBaulk>=.52||rail>=.45||hidden||(destinationDistance!==null&&destinationDistance<=.28);\n  const met=!foul&&(defensive?(handedOver&&(intent.task==='need-snookers'?hidden:nextRoutes.length===0&&containSafe)):intent.task==='escape'?(result.firstHits||[]).some(i=>g.targets(state).some(b=>b.i===i)):intent.task==='develop'?!!developed:scored&&continues&&nextRoutes.length>0);\n  const qFn=r=>Math.max(0,Math.min(1,((r.cut||.15)**1.4)/(1+(r.travel||0)/1.8)));\n  const distinctNext=[],seenNext=new Set();for(const r of nextRoutes.slice().sort((a,b)=>qFn(b)-qFn(a)))if(!seenNext.has(r.targetIndex)){distinctNext.push(r);seenNext.add(r.targetIndex);if(distinctNext.length===3)break;}\n  const mobilityBonus=scored&&continues&&!foul?Math.min(4.5,2.8*(distinctNext[0]?qFn(distinctNext[0]):0)+1.1*(distinctNext[1]?qFn(distinctNext[1]):0)+.5*(distinctNext[2]?qFn(distinctNext[2]):0)):0;\n  const sectorProx=scored&&continues&&!foul&&sector&&cue?Math.max(0,1-dist(cue,sector.centre)/.55)*(route?1.8:.6):0;\n  let expectedNext=null;\n  if(options?.expectedNext!==false&&scored&&continues&&sector&&route&&(position.met||!distinctNext.length)){\n   const edge=g.transitionGraph(next,24).find(e=>e.fromId===intent.nextBallId);\n   expectedNext={targetId:intent.nextBallId,sector:{...sector,axis:{...sector.axis},origin:{...sector.origin},centre:{...sector.centre}},preserveIds:(intent.preserveIds||[]).filter(i=>next.balls.some(b=>live(b)&&b.i===i)),intent:edge?{task:'position',targetId:edge.fromId,nextBallId:edge.toId,sectorId:edge.sectorId,preserveIds:(intent.preserveIds||[]).filter(i=>i!==edge.fromId)}:undefined};\n  }else if(options?.expectedNext!==false&&scored&&continues&&!foul&&cue&&distinctNext.length){\n   const graph=g.transitionGraph(next,24),bestR=distinctNext[0],nb=next.balls.find(x=>live(x)&&x.i===bestR.targetIndex);\n   const edge=graph.find(e=>e.fromId===bestR.targetIndex)||graph[0];\n   if(nb&&edge){\n    const d=Math.max(.08,dist(nb,cue)),ax={x:(cue.x-nb.x)/d,z:(cue.z-nb.z)/d};\n    expectedNext={targetId:nb.i,sector:{id:`opportunistic-${nb.i}-${bestR.pocketIndex}`,targetId:nb.i,pocketIndex:bestR.pocketIndex,origin:{x:nb.x,z:nb.z},axis:ax,centre:{x:cue.x,z:cue.z},distance:d,minDistance:Math.max(.05,d-.18),maxDistance:d+.18,angleTolerance:.32,arrivalTolerance:.85},preserveIds:(intent.preserveIds||[]).filter(i=>next.balls.some(x=>live(x)&&x.i===i)),intent:{task:'position',targetId:edge.fromId,nextBallId:edge.toId,sectorId:edge.sectorId,preserveIds:(intent.preserveIds||[]).filter(i=>i!==edge.fromId)}};\n   }\n  }\n  // Intent is planning metadata. Value is assigned once, in the shared points-based policy.\n  const scoreDelta=0;\n  return {met,destinationDistance,scoreDelta,features:{visitTask:intent.task,intentMet:met,destinationDistance,cueSectorReached:position.met,arrivalAligned:position.arrivalAligned,arrivalAngle:position.arrivalAngle,cueSectorAngle:position.angle,cueSectorDistance:position.distance,nextRouteAvailable:!!route,targetPositionChanged,snookerAchieved:!!hidden,handedOver,problemHandled:!!developed,preserveConsumed,mobilityBonus},expectedNext};\n }\n function rank(state,candidate,result,intent,g,brief){return assess(state,candidate,result,intent,g,brief);}\n return {analyze,normalizePlan,directed,refineIntent,assess,compliance,rank};\n})();\nif(typeof module!=='undefined'&&module.exports)module.exports=PCOLTacticalBrain;\n\n\n/* Execution uncertainty calibrated against a fixed native-physics practice shot,\n * not a measured professional-player skill distribution.\n * describe is deterministic. perturb draws three uniform samples once and\n * returns a coherent native-compatible shot; search and delivery share it.\n */\nconst PCOLShotSkill = (() => {\n  const profiles={club:{angle:.01026,power:.01728,vertical:.0324},strong:{angle:.0010098,power:.00972,vertical:.0216},expert:{angle:.00053568,power:.0054,vertical:.01296}};\n  const clamp=(v,lo,hi)=>Math.max(lo,Math.min(hi,v));\n  const distance=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);\n  function describe(state,candidate,level='strong') {\n    const profile=profiles[level]||profiles.strong;\n    const cue=state.balls?.find(b=>b.n===0&&b.active!==false);\n    const target=state.balls?.find(b=>b.i===candidate.targetIndex);\n    const pocket=state.pockets?.[candidate.pocketIndex];\n    const bounds=state.bounds;\n    const scale=bounds?Math.max(.1,Math.hypot(bounds.maxX-bounds.minX,bounds.maxZ-bounds.minZ)):3.6;\n    const travel=cue&&target?distance(cue,target)/scale:.3;\n    let cut=0;\n    if(target&&pocket) {\n      const d=distance(target,pocket),direction=candidate.shot.direction;\n      if(d>1e-9)cut=1-clamp((direction.x*(pocket.x-target.x)+direction.z*(pocket.z-target.z))/d,0,1);\n    }\n    const railGap=cue&&bounds?Math.min(cue.x-bounds.minX,bounds.maxX-cue.x,cue.z-bounds.minZ,bounds.maxZ-cue.z):Infinity;\n    const rail=Number.isFinite(railGap)?clamp(1-railGap/Math.max(.06,(cue.r||.026)*4),0,1):0;\n    const power=clamp(candidate.shot.power,0,1),difficulty=clamp(travel*.65+cut*.7+power*.2+rail*.3,0,1);\n    return {level:profiles[level]?level:'strong',difficulty,distance:travel,cut,rail,\n      angleSigma:profile.angle*(1+travel*2+cut*2+rail),\n      powerSigma:profile.power*(1+travel+power+rail*.5),\n      verticalSigma:profile.vertical*(1+power+rail)};\n  }\n  function perturb(shot,descriptor,random=Math.random) {\n    // Uniform zero-mean error with the requested standard deviation.\n    // Angular accuracy is independent of the power and spin error profiles.\n    const sample=sigma=>(clamp(random(),0,1)*2-1)*Math.sqrt(3)*sigma;\n    const angle=Math.atan2(shot.direction.z,shot.direction.x)+sample(descriptor.angleSigma);\n    const power=clamp(shot.power+sample(descriptor.powerSigma),0,1);\n    const vertical=clamp((shot.vertical||0)+sample(descriptor.verticalSigma),-1,1);\n    return {...shot,direction:{x:Math.cos(angle),z:Math.sin(angle)},power,vertical,side:shot.side||0,\n      elevation:vertical<0?.025*Math.PI:0};\n  }\n  // Common, stratified coordinates for comparisons. Each new pair changes all\n  // three axes; actual delivery still draws independent uniform errors.\n  function coordinates(index) {\n    const pairs=[[.25,.25,.75],[1/12,7/12,5/12],[5/12,1/12,1/12]];\n    const row=pairs[Math.floor(index/2)%pairs.length];\n    return index%2?row.map(v=>1-v):row;\n  }\n  return {describe,perturb,coordinates};\n})();\n\n/* Geometric development intentions only; the native trial must prove the cannon and continuation. */\nconst PCOLDevelopment = (() => {\n  const active=b=>b.active!==false&&Number.isFinite(b.x)&&Number.isFinite(b.z);\n  const r=b=>Number.isFinite(b.r)&&b.r>0?b.r:.026;\n  const dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);\n  const unit=v=>{const d=Math.hypot(v.x,v.z);return d>1e-8?{x:v.x/d,z:v.z/d}:null;};\n  function generate(state,geometry) {\n    const balls=(state.balls||[]).filter(active),cue=balls.find(b=>b.n===0);\n    if(!cue||!geometry?.attackRoutes||!geometry?.targets||!geometry?.clear)return [];\n    const reds=balls.filter(b=>b.n===1),remaining=new Set(reds),clusters=[];\n    while(remaining.size){\n      const first=remaining.values().next().value,group=[first];remaining.delete(first);\n      for(let i=0;i<group.length;i++)for(const b of remaining)if(dist(group[i],b)<=1.55*(r(group[i])+r(b))){group.push(b);remaining.delete(b);}\n      if(group.length>=2)clusters.push(group);\n    }\n    if(!clusters.length)return [];\n    const routes=geometry.attackRoutes(state,cue,geometry.targets(state));\n    const insuranceRoutes=geometry.attackRoutes(state,cue,reds),result=[];\n    for(const route of routes){\n      const target=balls.find(b=>b.i===route.targetIndex),pocket=state.pockets?.[route.pocketIndex];\n      if(!target||!pocket)continue;\n      const normal=unit({x:pocket.x-target.x,z:pocket.z-target.z}),incoming=unit(route.direction);\n      if(!normal||!incoming)continue;\n      const projection=incoming.x*normal.x+incoming.z*normal.z;\n      const tangent={x:incoming.x-projection*normal.x,z:incoming.z-projection*normal.z};\n      const contact={x:target.x-normal.x*(r(cue)+r(target)),z:target.z-normal.z*(r(cue)+r(target))};\n      const {direction,...meta}=route;\n      const explicit=state.rules?.nominatedColour;\n      const nomination=state.rules?.ballOn===252?{nominatedColour:explicit>=2&&explicit<=7?explicit:target.n>=2&&target.n<=7?target.n:2}:{};\n      const label=target.n>=2?'借彩球轻拆':'进攻轻拆';\n      for(const cluster of clusters){\n        if(cluster.some(b=>b.i===target.i))continue;\n        const ids=cluster.map(b=>b.i),centre={x:cluster.reduce((s,b)=>s+b.x,0)/cluster.length,z:cluster.reduce((s,b)=>s+b.z,0)/cluster.length};\n        const insuranceIds=[...new Set(insuranceRoutes.filter(a=>!ids.includes(a.targetIndex)&&a.targetIndex!==target.i).map(a=>a.targetIndex))];\n        let delicateAdded=0;\n        for(const vertical of [0,.3,-.3]){\n          // Modest axial component is an alignment heuristic, not a spin/trajectory solver.\n          const outgoing=unit({x:tangent.x+normal.x*vertical*.35,z:tangent.z+normal.z*vertical*.35});\n          if(!outgoing)continue;\n          const entries=cluster.map(b=>{const dx=b.x-contact.x,dz=b.z-contact.z,t=dx*outgoing.x+dz*outgoing.z;\n            return {b,t,offset:Math.abs(dx*outgoing.z-dz*outgoing.x)};\n          }).filter(e=>e.t>r(cue)+r(e.b)&&e.t<1.5&&e.offset<r(cue)+r(e.b)*.8&&e.offset>r(e.b)*.3).sort((a,b)=>a.t-b.t);\n          const entry=entries[0];if(!entry)continue;\n          // Approach an exposed edge: reject a line aimed deeply through the cluster centre.\n          const centreOffset=Math.abs((centre.x-contact.x)*outgoing.z-(centre.z-contact.z)*outgoing.x);\n          if(centreOffset<r(entry.b)*.65)continue;\n          const endpoint={x:contact.x+outgoing.x*Math.max(0,entry.t-(r(cue)+r(entry.b))),z:contact.z+outgoing.z*Math.max(0,entry.t-(r(cue)+r(entry.b)))};\n          if(!geometry.clear(state,contact,endpoint,r(cue),[cue.i,target.i,entry.b.i]))continue;\n          const base=Math.max(.24,Math.min(.62,.23+.045*route.travel+.10*(1-route.cut)+.08*entry.t));\n          for(const delta of [0,.07]){\n            result.push({...meta,...nomination,label,development:{clusterIds:ids.slice(),entryIndex:entry.b.i,insuranceIds:insuranceIds.slice()},\n              shot:{direction:{...route.direction},power:Math.min(.85,base+delta),side:0,vertical,elevation:vertical<0?.025*Math.PI:0}});\n            delicateAdded++;\n          }\n        }\n        if((cluster.length>=3||!delicateAdded)&&(route.cut||0)>=.38){\n          for(const vertical of [0,-.45,.45,-.3,.3]){\n            const outgoing=unit({x:tangent.x+normal.x*vertical*.45,z:tangent.z+normal.z*vertical*.45});\n            if(!outgoing)continue;\n            const entries=cluster.map(b=>{const dx=b.x-contact.x,dz=b.z-contact.z,t=dx*outgoing.x+dz*outgoing.z;\n              return {b,t,offset:Math.abs(dx*outgoing.z-dz*outgoing.x)};\n            }).filter(e=>e.t>r(cue)+r(e.b)&&e.t<1.65&&e.offset<r(cue)+r(e.b)*.95).sort((a,b)=>a.t-b.t);\n            const entry=entries[0];if(!entry)continue;\n            const endpoint={x:contact.x+outgoing.x*Math.max(0,entry.t-(r(cue)+r(entry.b))),z:contact.z+outgoing.z*Math.max(0,entry.t-(r(cue)+r(entry.b)))};\n            if(!geometry.clear(state,contact,endpoint,r(cue),[cue.i,target.i,entry.b.i]))continue;\n            const powerBase=Math.max(.66,Math.min(.82,.58+.06*route.travel+.08*entry.t));\n            for(const delta of [0,.07]){\n              result.push({...meta,...nomination,powerSplit:true,label,development:{clusterIds:ids.slice(),entryIndex:entry.b.i,insuranceIds:insuranceIds.slice(),powerSplit:true},\n                shot:{direction:{...route.direction},power:Math.min(.85,powerBase+delta),side:0,vertical,elevation:vertical<0?.025*Math.PI:0}});\n            }\n          }\n        }\n      }\n    }\n    return (geometry.diverse?geometry.diverse(result):result).slice(0,16);\n  }\n  return {generate};\n})();\n\n/* Bounded minimax replaces a leaf estimate with adjudicated points and a new leaf. */\nconst PCOLContinuation=(()=>{\n  function create({geometry,policy,core,development,skill}) {\n    function settled(base,result) {\n      if(!result.nextSnapshot||!result.nextBalls||result.adjudication?.foulCode)return null;\n      const rules={...base.rules,...result.nextSnapshot.rules,...result.nextContext};\n      const next={...base,balls:result.nextBalls,rules,scores:rules.scores,touching:null};\n      if(core?.remainingPoints)next.remainingPoints=core.remainingPoints(next.balls,rules.ballOn);\n      if(!rules.ballOn||rules.requiresDraw||rules.inHand||rules.freeBallAvailable||rules.freeBallReview)return null;\n      if(core?.touchingStatus){next.touching=core.touchingStatus({balls:next.balls,...rules});if(next.touching?.requiresColourDeclaration)return null;}\n      return next;\n    }\n    function orderedSeeds(state,layout) {\n      const blocked=layout(state).hasDirectHit===false;\n      const developed=development?.generate(state,geometry)||[];\n      const pool=geometry.generate(state),attacks=pool.filter(c=>c.kind==='attack'&&!c.development);\n      const merit=c=>((c.cut??1)**1.5)/(1+(c.travel||0))*(state.balls?.find(b=>b.i===(c.potTargetIndex??c.targetIndex))?.n||1);\n      attacks.sort((a,b)=>merit(b)-merit(a));\n      const diverse=geometry.diverse||((items)=>items),objective=policy.analyze?.(state).objective;\n      const safety=diverse(pool.filter(c=>c.kind==='safety')),escape=diverse(pool.filter(c=>c.kind==='escape'));\n      const ordered=blocked?escape.concat(safety,attacks,developed):objective==='need-snookers'?safety.concat(attacks,developed,escape):\n        attacks.length?[attacks[0],...(developed.length?diverse(developed):diverse(attacks.slice(1))),...diverse(attacks.slice(1)),...safety,...escape]:safety.concat(escape,developed);\n      const seen=new Set(),first=[],rest=[];\n      for(const seed of ordered){const key=geometry.routeKey?geometry.routeKey(seed):[seed.kind,seed.targetIndex,seed.pocketIndex,!!seed.development].join(':');\n        if(seen.has(key))rest.push(seed);else{seen.add(key);first.push(seed);}}\n      return first.concat(rest);\n    }\n    // Revisited first layers share immutable nodes and seed order within this search only.\n    function createSession({policySession}={}) {\n      const sharedPolicy=policySession||policy.createSession?.(geometry);\n      const nodes=new WeakMap(),seedLists=new WeakMap(),evaluators=new WeakMap(),rootStates=new WeakMap();\n      const layout=state=>sharedPolicy?sharedPolicy.layout(state):policy.layout(state,geometry);\n      function nextState(base,result) {\n        let children=nodes.get(base);\n        if(!children){children=new WeakMap();nodes.set(base,children);}\n        if(!children.has(result))children.set(result,settled(base,result));\n        return children.get(result);\n      }\n      function seeds(state,count) {\n        let list=seedLists.get(state);\n        if(!list){list=orderedSeeds(state,layout);seedLists.set(state,list);}\n        return list.slice(0,count);\n      }\n      function evaluatePolicy(state,candidate,result) {\n        if(sharedPolicy)return sharedPolicy.evaluate(state,candidate,result);\n        let evaluator=evaluators.get(state);\n        if(!evaluator){evaluator=policy.createEvaluator?.(state,geometry)||((c,r)=>policy.evaluate(state,c,r,geometry));evaluators.set(state,evaluator);}\n        return evaluator(candidate,result);\n      }\n    async function evaluate({state,candidate,result,preparedEvaluation,simulateFrom,canContinue=()=>true,maxTrials=6,depth:requestedDepth,breadth:requestedBreadth}) {\n      const root=state.rootPlayerIndex??state.rules.playerIndex;\n      if(state.rootPlayerIndex==null){\n        let rooted=rootStates.get(state);\n        if(!rooted){rooted={...state,rootPlayerIndex:root};rootStates.set(state,rooted);}\n        state=rooted;\n      }\n      const original=preparedEvaluation||evaluatePolicy(state,candidate,result);\n      const summary={mode:'unassessed',status:'unassessed',trials:0,completed:0,verifiedPath:[],coverage:'unknown',chainVerified:false,insuranceVerified:false,provenTerminalLoss:false,rootTerminalLoss:original.terminalValue<0,\n        assessment:'bounded sampled branch; not evidence for every execution outcome'};\n      let interrupted=false;\n      const cap=Math.max(0,Math.min(12,Math.floor(maxTrials)));\n      const levelFor=s=>s.rules.playerIndex===root?s.skill:s.opponentSkill;\n      const checkExecution=!!skill&&!!levelFor(nextState(state,result)||state);\n      const width=checkExecution?3:1;\n      const horizon=requestedDepth??(cap>=(checkExecution?12:6)?2:cap>0?1:0);\n      const requestedWidth=requestedBreadth??(checkExecution&&horizon>1?1:2);\n      summary.depth=horizon;\n      summary.execution=checkExecution?'nominal-and-common-error-pair':'geometric-proxy; opponent skill may be unknown';\n      async function visit(base,parent,depth) {\n        const next=nextState(base,parent);if(!next||depth<=0)return null;\n        const maximise=next.rules.playerIndex===root,branches=[];\n        const available=cap-summary.trials;\n        // Compare siblings before spending the same bounded cap below a single route.\n        const level=levelFor(next),sampleCount=skill&&level?2:0,unit=1+sampleCount;\n        const breadth=Math.min(requestedWidth,Math.floor(cap/unit));\n        if(!breadth||available<breadth*unit){interrupted=true;return null;}\n        for(const seed of seeds(next,breadth)) {\n          const executions=[seed],uncertainty=sampleCount?skill.describe(next,seed,level):null;\n          for(let i=0;i<sampleCount;i++){let k=0;const values=skill.coordinates(i);\n            executions.push({...seed,shot:skill.perturb(seed.shot,uncertainty,()=>values[k++])});}\n          const observations=[];\n          for(let sample=0;sample<executions.length;sample++){\n          if(summary.trials>=cap||!canContinue()){interrupted=true;break;}\n          summary.trials++;\n          const r=await simulateFrom(parent,executions[sample]);\n          if(r?.status!=='complete'||!r.adjudication||!r.nextBalls){interrupted=true;continue;}\n          summary.completed++;\n          const e=evaluatePolicy(next,seed,r);\n          if(!e.terminalValue&&!nextState(next,r)){interrupted=true;summary.adjudicationPending=true;}\n          const potted=!r.adjudication.foulCode&&r.adjudication.score>0&&(r.potted||[]).some(i=>i===seed.targetIndex||i===seed.potTargetIndex);\n          const cluster=seed.development?.clusterIds||[];\n          const opened=cluster.some(i=>(e.features?.freedRedIds||[]).includes(i)&&(r.contacts||[]).some(c=>c.ballIndex===i));\n          const entry={actor:next.rules.playerIndex,ballPhase:next.rules.ballOn,targetIndex:seed.targetIndex,execution:sample===0?'nominal':'sample-'+(sample-1),\n            nominatedColour:seed.nominatedColour??null,points:r.adjudication.score||0,potted,\n            nextActor:e.features?.nextPlayerIndex??r.nextContext?.playerIndex??r.nextSnapshot?.rules?.playerIndex,\n            foulCode:r.adjudication.foulCode||0,development:!!seed.development,developmentOpened:opened,clusterIds:cluster,components:{netPoints:e.netPoints,immediateCost:e.immediateCost||0,futureValue:e.futureValue,terminalValue:e.terminalValue}};\n          observations.push({value:e.score,path:[entry],r,e,terminalLoss:e.terminalValue<0});\n          }\n          const nominal=observations.find(row=>row.path[0].execution==='nominal');\n          if(!nominal)continue;\n          const errors=observations.filter(row=>row!==nominal);\n          const value=errors.length===sampleCount&&sampleCount?policy.aggregate({...next,rootPlayerIndex:next.rules.playerIndex},errors.map(row=>maximise?row.value:-row.value)).score*(maximise?1:-1):nominal.value;\n          if(observations.length!==executions.length)interrupted=true;\n          branches.push({...nominal,value,observations,sampleCount});\n        }\n        branches.sort((a,b)=>maximise?b.value-a.value:a.value-b.value);\n        const expandable=branches.flatMap(branch=>branch.observations.filter(row=>!row.e.terminalValue&&nextState(next,row.r)));\n        if(depth>1&&cap-summary.trials<expandable.length*requestedWidth*width){interrupted=true;return branches[0]||null;}\n        if(depth>1)for(const branch of expandable) {\n          if(summary.trials>=cap||!canContinue()){interrupted=true;break;}\n          if(branch.e.terminalValue)continue;\n          const child=await visit(next,branch.r,depth-1);\n          if(child){branch.value=branch.e.netPoints+(branch.e.immediateCost||0)+branch.e.terminalValue+child.value;branch.path=branch.path.concat(child.path);branch.terminalLoss=child.terminalLoss;}\n        }\n        if(depth>1)for(const branch of branches){\n          const errors=branch.observations.slice(1),nominal=branch.observations[0];\n          branch.value=errors.length===branch.sampleCount&&errors.length?policy.aggregate({...next,rootPlayerIndex:next.rules.playerIndex},errors.map(row=>maximise?row.value:-row.value)).score*(maximise?1:-1):nominal.value;\n          branch.path=nominal.path;branch.terminalLoss=nominal.terminalLoss;\n        }\n        branches.sort((a,b)=>maximise?b.value-a.value:a.value-b.value);\n        return branches[0]||null;\n      }\n      const next=nextState(state,result);\n      if(next&&result.adjudication&&!original.terminalValue) {\n        summary.mode=next.rules.playerIndex===root?'continuation':'opponent-reply';\n        const best=await visit(state,result,horizon);\n        if(best){\n          summary.sampledPath=best.path;\n          summary.executionOutcomes=best.observations.map(row=>({value:row.value,path:row.path}));\n          if(summary.mode==='continuation'&&!result.adjudication.foulCode&&result.adjudication.score>0)\n            for(const entry of best.path){if(entry.actor!==root||!entry.potted)break;summary.verifiedPath.push(entry);}\n          summary.provenContinuation=summary.verifiedPath.length>0;\n          summary.chainVerified=summary.verifiedPath.length>=2;\n          const cluster=candidate.development?.clusterIds||summary.verifiedPath.find(e=>e.development)?.clusterIds||[];\n          const developedAt=summary.verifiedPath.findIndex(e=>e.development);\n          summary.insuranceVerified=summary.chainVerified&&cluster.length>0&&summary.verifiedPath.some((e,i)=>\n            i>developedAt&&e.ballPhase===2&&!cluster.includes(e.targetIndex));\n          if(summary.verifiedPath.some(e=>e.development)&&(!summary.verifiedPath.some(e=>e.developmentOpened)||!summary.insuranceVerified))summary.chainVerified=false;\n          if(summary.mode==='opponent-reply')summary.opponentBestReply=best.path[0];\n          summary.status=interrupted?'partial':'complete';summary.coverage=interrupted?'partial':'covered';\n          summary.sampledTerminalLoss=!!best.terminalLoss;\n          // A terminal leaf proves that sampled execution lost, not a forced minimax loss.\n          summary.provenTerminalLoss=false;\n          return {futureValue:best.value,scoreDelta:best.value-original.futureValue,shallowScore:original.score,comparableScore:original.score,horizonScore:original.score+best.value-original.futureValue,summary};\n        }\n      }\n      if(summary.trials){summary.status='partial';summary.coverage='partial';}\n      if(result.adjudication?.foulCode)summary.adjudicationPending=true;\n      if(original.terminalValue){summary.status='complete';summary.coverage='covered';summary.provenTerminalLoss=original.terminalValue<0;}\n      return {futureValue:original.futureValue,scoreDelta:0,shallowScore:original.score,comparableScore:original.score,horizonScore:original.terminalValue?original.score:null,summary};\n    }\n      return {evaluate};\n    }\n    return {evaluate:options=>createSession({policySession:options.policySession}).evaluate(options),createSession};\n  }\n  return {create};\n})();\n\n/* Shared cooperative clock: explicit pauses never spend effective search time. */\nconst PCOLComputeScheduler=(()=>{\n  const bounded=(value,fallback)=>Number.isFinite(value)?Math.max(0,Math.min(16,value)):fallback;\n  function create({now=()=>performance.now(),setTimer=setTimeout,clearTimer=clearTimeout}={}) {\n    let pacing={sliceMs:6,delayMs:4};\n    function setPacing(settings={}) {pacing={sliceMs:bounded(settings.sliceMs,pacing.sliceMs),delayMs:bounded(settings.delayMs,pacing.delayMs)};}\n    function start({cooperativeYield}={}) {\n      const enabled=cooperativeYield!==false,settings=cooperativeYield||{},started=now();\n      let waitMs=0,yields=0,sliceStarted=started,pause=null,cancelled=false,closed=false;\n      const deadlines=new Set();\n      const pausedMs=()=>waitMs+(pause?now()-pause.started:0);\n      const clock=()=>now()-pausedMs();\n      function arm(entry) {\n        clearTimer(entry.timer);\n        if(!pause&&!closed&&!cancelled)entry.timer=setTimer(()=>{\n          if(!deadlines.delete(entry))return;\n          entry.callback();\n        },Math.max(0,entry.deadline-clock()));\n      }\n      function setDeadline(deadline,callback) {\n        const entry={deadline,callback};deadlines.add(entry);arm(entry);\n        return ()=>{clearTimer(entry.timer);deadlines.delete(entry);};\n      }\n      function resume() {\n        if(!pause)return;\n        const current=pause;pause=null;clearTimer(current.timer);\n        waitMs+=now()-current.started;sliceStarted=now();\n        for(const entry of deadlines)arm(entry);\n        current.resolve(!cancelled&&!closed);\n      }\n      async function checkpoint() {\n        if(cancelled||closed)return false;\n        const sliceMs=bounded(settings.sliceMs,pacing.sliceMs),delayMs=bounded(settings.delayMs,pacing.delayMs);\n        if(!enabled||now()-sliceStarted<sliceMs)return true;\n        if(pause)return pause.promise;\n        for(const entry of deadlines)clearTimer(entry.timer);\n        yields++;\n        const current={started:now()};pause=current;\n        current.promise=new Promise(resolve=>{current.resolve=resolve;current.timer=setTimer(resume,delayMs);});\n        return current.promise;\n      }\n      // Call after creating the promise: synchronous Worker simulation still fills\n      // the slice; only the subsequent natural await is ignored for pacing.\n      async function wait(promise) {\n        const waiting=now();try{return await promise;}finally{sliceStarted+=now()-waiting;}\n      }\n      function cancel() {cancelled=true;resume();for(const entry of deadlines)clearTimer(entry.timer);}\n      function close() {closed=true;resume();for(const entry of deadlines)clearTimer(entry.timer);deadlines.clear();}\n      return {now:clock,checkpoint,wait,setDeadline,cancel,close,\n        stats:()=>({enabled,yields,waitMs:pausedMs(),budgetElapsedMs:clock()-started})};\n    }\n    return {start,setPacing};\n  }\n  return {create};\n})();\n\n/* Compact legal turn options. Geometry scores are proxies; native trials rank shots. */\nconst PCOLTurnOptions = (() => {\n  const active=b=>b.active!==false&&Number.isFinite(b.x)&&Number.isFinite(b.z);\n  const radius=b=>b.r>0?b.r:.026;\n  const dist=(a,b)=>Math.hypot(a.x-b.x,a.z-b.z);\n  const copy=s=>({...s,balls:(s.balls||[]).map(b=>({...b})),rules:{...s.rules},scores:[...(s.scores||s.rules?.scores||[0,0])]});\n  function create({geometry,core}) {\n    function placements(state,dArea=state.dArea) {\n      if(!dArea)return [];\n      const {center,arcDir,diameterDir,radius:R}=dArea;\n      const cue=(state.balls||[]).find(b=>b.n===0),r=radius(cue||{}),bounds=state.bounds;\n      const positions=[[.72,.12],[-.72,.12],[0,.30],[0,0],[.42,.42],[-.42,.42],[0,.75],[.82,0],[-.82,0]];\n      return positions.map(([side,back],i)=>({id:`d-${i}`,x:center.x+R*(side*diameterDir.x+back*arcDir.x),y:center.y??cue?.y??0,z:center.z+R*(side*diameterDir.z+back*arcDir.z)})).filter(p=>{\n        const dx=p.x-center.x,dz=p.z-center.z;\n        return dx*dx+dz*dz<=R*R+1e-9&&dx*arcDir.x+dz*arcDir.z>=-1e-9&&\n          (!bounds||(p.x>=bounds.minX+r&&p.x<=bounds.maxX-r&&p.z>=bounds.minZ+r&&p.z<=bounds.maxZ-r))&&\n          !(state.balls||[]).some(b=>b.n>0&&active(b)&&dist(p,b)<r+radius(b)+1e-5);\n      });\n    }\n    function isOpening(state) {\n      const rules=state.rules||{},reds=(state.balls||[]).filter(b=>b.n===1&&active(b));\n      if(!(rules.inHand>0)||rules.ballOn!==2||!(Number.isFinite(rules.nRounds)&&rules.nRounds<=1)||reds.length!==15)return false;\n      const seen=new Set([reds[0].i]);let changed=true;\n      while(changed){changed=false;for(const b of reds)if(!seen.has(b.i)&&reds.some(a=>seen.has(a.i)&&dist(a,b)<=1.14*(radius(a)+radius(b)))){seen.add(b.i);changed=true;}}\n      return seen.size===15;\n    }\n    function openingShots(state) {\n      if(!isOpening(state))return [];\n      const cue=(state.balls||[]).find(b=>b.n===0&&active(b));if(!cue)return [];\n      const reds=geometry.targets(state),mean=reds.reduce((p,b)=>({x:p.x+b.x/reds.length,z:p.z+b.z/reds.length}),{x:0,z:0});\n      const axis={x:mean.x-cue.x,z:mean.z-cue.z},length=Math.hypot(axis.x,axis.z);if(!length)return [];\n      const transverse=b=>(b.x-mean.x)*(-axis.z/length)+(b.z-mean.z)*(axis.x/length);\n      const sorted=[...reds].sort((a,b)=>transverse(a)-transverse(b)),result=[];\n      for(const power of [.48,.53,.58,.63,.68])for(const thin of [.72,.80,.88])for(const [target,sign] of [[sorted[0],-1],[sorted.at(-1),1]]){\n        const d=dist(cue,target),ux=(target.x-cue.x)/d,uz=(target.z-cue.z)/d,offset=(radius(cue)+radius(target))*thin*sign;\n        const aim={x:target.x-uz*offset,z:target.z+ux*offset},travel=dist(cue,aim);\n        if(!geometry.clear(state,cue,aim,radius(cue),[cue.i,target.i]))continue;\n        result.push({kind:'safety',opening:true,targetIndex:target.i,label:'标准薄红球开球',priority:1,shot:{direction:{x:(aim.x-cue.x)/travel,z:(aim.z-cue.z)/travel},power,side:0,vertical:.25,elevation:0}});\n      }\n      return result;\n    }\n    function summarize(state) {\n      const cue=(state.balls||[]).find(b=>b.n===0&&active(b)),on=geometry.targets(state);\n      const bounds=state.bounds,scale=bounds?Math.hypot(bounds.maxX-bounds.minX,bounds.maxZ-bounds.minZ):2;\n      const routes=cue?geometry.attackRoutes(state,cue,on):[];\n      const qualities=routes.map(r=>Math.max(0,r.cut||0)**1.5/(1+2*(r.travel||0)/scale));\n      const nominee=(state.balls||[]).find(b=>b.i===state.rules?.freeBallNominee&&active(b));\n      const directMask=nominee?1<<nominee.n:state.rules?.ballOn===252&&state.rules?.nominatedColour?1<<state.rules.nominatedColour:state.rules?.ballOn;\n      const direct=cue?core.hasDirectHit(state.balls,directMask,cue):{hasDirectHit:null};\n      return {bestPotQuality:Math.max(0,...qualities),possibleTargets:on.length,potRoutes:routes.length,blocked:direct.hasDirectHit===false,directHit:direct.hasDirectHit,\n        targetDistance:cue&&on.length?Math.min(...on.map(b=>dist(cue,b)))/scale:0,inHand:state.rules?.inHand>0};\n    }\n    function nominations(state) {\n      const rules=state.rules||{},decline={id:'free-decline',nominee:null,rulesOverride:{freeBallNominee:null}};\n      if(!rules.freeBallAvailable)return [decline];\n      const on=new Set(geometry.targets({...state,rules:{...rules,freeBallNominee:null}}).map(b=>b.i));\n      const candidates=(state.balls||[]).filter(b=>b.n>0&&active(b)&&!on.has(b.i)).map(b=>{\n        const rulesOverride={freeBallNominee:b.i};\n        const features=summarize({...state,rules:{...rules,...rulesOverride}});\n        return {id:`free-${b.i}`,nominee:b.i,rulesOverride,features,preorder:features.bestPotQuality};\n      }).sort((a,b)=>b.preorder-a.preorder);\n      return [decline,...candidates.slice(0,6)];\n    }\n    function foulChoices(state,pending) {\n      if(!pending)return [];\n      const incoming=1-pending.offender,before=pending.before.context||pending.before.rules||{};\n      return ['continue','again',...(pending.miss?['restore']:[])].map(action=>{\n        const next=copy(state),rules=next.rules;\n        if(action==='restore'){next.balls=(pending.before.balls||[]).map(b=>({...b}));Object.assign(rules,before);}\n        rules.playerIndex=action==='continue'?incoming:pending.offender;\n        rules.ballOn=action==='continue'?pending.result.nextBallOn:before.ballOn;\n        if(action==='again'&&rules.ballOn===2&&!next.balls.some(b=>active(b)&&b.n===1))rules.ballOn=4;\n        rules.inHand=action==='restore'?(before.inHand||0):(pending.result.requiresInHand?2:state.rules?.inHand||0);\n        rules.freeBallAvailable=action==='continue'&&Boolean(state.rules?.freeBallAvailable);\n        rules.freeBallNominee=null;rules.nominatedColour=null;rules.nominationSource=null;\n        rules.freeBallReview=false;rules.freeBallDeclined=false;rules.scores=[...next.scores];\n        const features=summarize(next);\n        return {id:action,action,state:next,features,score:null};\n      });\n    }\n    return {placements,isOpening,openingShots,nominations,foulChoices,summarize};\n  }\n  return {create};\n})();\n\n/* One pre-shot decision: adjudicated foul options, nomination and legal D placement. */\nconst PCOLTurnManager = (() => {\n  function create({getState,getPending,getTrial,options,geometry,policy,skill,choose,commit,onError,onChange=()=>{},onEvent=()=>{},scheduler,cooperativeYield}) {\n    const scheduling=scheduler||(typeof PCOLComputeScheduler!=='undefined'?PCOLComputeScheduler:require('./compute-scheduler')).create();\n    let active=null,epoch=0,failed=false,lastResult=null;\n    const status=()=>({busy:!!active,failed,phase:active?.phase||'idle',lastResult});\n    const changed=()=>onChange(status());\n    function cancel(){epoch++;if(active){active.schedule.cancel();getTrial().cancel();}active=null;failed=false;changed();}\n    const available=(job,deadline=job.deadline)=>epoch===job.epoch&&!job.control.expired&&job.schedule.now()<deadline;\n    async function simulate(job,trial,scenario,shot,nomination,deadline,maxWallMs) {\n      if(!available(job,deadline)||!await job.schedule.checkpoint()||!available(job,deadline))return null;\n      job.control.inFlight=true;\n      try{return await job.schedule.wait(trial.simulateScenario(scenario,shot,{nominatedColour:nomination,\n        maxWallMs:Math.min(maxWallMs,Math.max(1,deadline-job.schedule.now())),trace:false}));}\n      catch(error){if(epoch!==job.epoch||job.control.expired)return null;throw error;}\n      finally{job.control.inFlight=false;}\n    }\n    function variants(state) {\n      const positions=state.rules.inHand>0?options.placements(state):[null];\n      const result=[];\n      for(const position of positions)for(const nomination of options.nominations(state)) {\n        const balls=state.balls.map(b=>b.n===0&&position?{...b,...position,active:true}:{...b});\n        const rules={...state.rules,...nomination.rulesOverride,freeBallReview:false,\n          freeBallDeclined:nomination.nominee==null,nominationSource:state.rules.nominationSource};\n        const next={...state,balls,rules},features=options.summarize(next);\n        result.push({id:(position?.id||'current')+'-'+nomination.id,position,nominee:nomination.nominee,state:next,\n          features,score:null,preorder:features.bestPotQuality});\n      }\n      return result.sort((a,b)=>b.preorder-a.preorder).slice(0,options.isOpening(state)?9:8);\n    }\n    function seeds(state) {\n      const pool=options.isOpening(state)?options.openingShots(state):geometry.generate(state),picked=[],used=new Set();\n      // Cycle kinds and spread targets/powers before revisiting a route family.\n      for(let i=0;i<3;i++)for(const kind of ['attack','safety','escape']){\n        const candidates=pool.filter(s=>s.kind===kind&&!picked.includes(s));\n        const seed=candidates.find(s=>!used.has(s.targetIndex+'_'+s.shot.power))||candidates[0];\n        if(seed){picked.push(seed);used.add(seed.targetIndex+'_'+seed.shot.power);}\n      }\n      if(options.isOpening(state))return pool.filter((_,i)=>[0,3,8,11,14,17,20,25,28].includes(i));\n      return picked;\n    }\n    async function evaluateOption(option,trial,job,serial) {\n      const state=option.state;\n      const evaluate=policy.createEvaluator?policy.createEvaluator(state,geometry):(c,r)=>policy.evaluate(state,c,r,geometry);\n      const nominalDeadline=job.schedule.now()+Math.max(0,job.deadline-job.schedule.now())*.65;\n      const scenario={balls:state.balls,rules:state.rules,cuePosition:option.position};\n      if(serial)scenario.serial=serial;\n      let best=null,tested=0,legal=0,fouls=0;const finalists=[];\n      const routes=seeds(state);\n      for(const seed of routes) {\n        if(!available(job,nominalDeadline))break;\n        const r=await simulate(job,trial,scenario,seed.shot,seed.nominatedColour,nominalDeadline,2200);\n        if(!r)break;tested++;\n        if(r.stale)throw new Error('Position changed; AI decision is stale');\n        if(r.status!=='complete'||!r.adjudication)continue;\n        const evaluated=evaluate(seed,r);\n        if(r.adjudication.foulCode){fouls++;continue;}\n        legal++;\n        const score=evaluated.score;\n        finalists.push({score,seed,result:r,features:evaluated.features});\n      }\n      const testedFinalists=finalists.sort((a,b)=>b.score-a.score).slice(0,2);\n      for(const candidate of testedFinalists) {\n        const uncertainty=skill.describe(state,candidate.seed,state.skill);\n        candidate.samples=[];\n        for(let index=0;index<2;index++) {\n          const values=skill.coordinates(index);\n          if(!available(job))break;\n          let i=0;const shot=skill.perturb(candidate.seed.shot,uncertainty,()=>values[i++]);\n          const r=await simulate(job,trial,scenario,shot,candidate.seed.nominatedColour,job.deadline,2000);\n          if(!r)break;\n          if(r.stale)throw new Error('Position changed; AI decision is stale');\n          if(r.status==='complete'&&r.adjudication){\n            candidate.samples.push({index,value:evaluate(candidate.seed,r).score,foul:!!r.adjudication.foulCode});\n          }\n        }\n      }\n      const indices=[0,1].filter(i=>testedFinalists.every(c=>c.samples.some(row=>row.index===i)));\n      for(const candidate of testedFinalists){\n        const rows=candidate.samples.filter(row=>indices.includes(row.index));\n        candidate.nominalScore=candidate.score;\n        candidate.features={...candidate.features,executionSamples:rows.length,sampledFoulRate:rows.length?rows.filter(r=>r.foul).length/rows.length:null};\n        if(rows.length){const value=policy.aggregate(state,rows.map(r=>r.value));candidate.score=value.score;\n          candidate.features={...candidate.features,executionMean:value.mean,executionDownside:value.downside};}\n        if(!best||candidate.score>best.score)best=candidate;\n      }\n      option.features={...option.features,tested,legal,fouls,verified:!!best,freeBallNominee:option.nominee,\n        cuePosition:option.position&&{x:option.position.x,z:option.position.z}};\n      if(best) {\n        const r=best.result,v=r.adjudication,cue=r.nextBalls.find(b=>b.n===0);\n        option.score=best.score;option.features={...option.features,...best.features};\n        option.nominalScore=best.nominalScore;option.executionScores=best.samples;\n        option.outcome={score:v.score,foulCode:0,nextBallOn:v.nextBallOn,cue:{x:cue.x,z:cue.z}};\n        option.candidate={...best.seed,score:best.score,features:best.features,stroke:r.stroke,actual:r.compiled.actual,\n          skill:skill.describe(state,best.seed,state.skill),outcome:{...option.outcome,nominatedColour:v.ballOnUsed}};\n      } else {option.score=null;option.features.assessment='unknown';}\n      return option;\n    }\n    async function run() {\n      if(active||failed)return;\n      const started=performance.now(),schedule=scheduling.start({cooperativeYield}),workStarted=schedule.now();\n      const wallLimitMs=37000,job=active={epoch,schedule,phase:'turn-search',deadline:workStarted+18000,control:{expired:false,inFlight:false}};changed();\n      const expire=()=>{job.control.expired=true;schedule.cancel();if(job.control.inFlight)getTrial().cancel();};\n      const clearDeadline=schedule.setDeadline(job.deadline,expire),wallTimer=setTimeout(expire,wallLimitMs);\n      try {\n        const trial=getTrial(),before=JSON.stringify(trial.snapshot()),state=getState(),pending=getPending();\n        let choices=[],kind;\n        if(pending) {\n          kind='foul';\n          const actions=options.foulChoices(state,pending);\n          for(let actionIndex=0;actionIndex<actions.length;actionIndex++) {\n            const action=actions[actionIndex];let best=null;\n            const actionDeadline=schedule.now()+Math.max(0,job.deadline-schedule.now())/(actions.length-actionIndex);\n            const places=variants(action.state).slice(0,3);\n            for(let i=0;i<places.length;i++) {\n              const deadline=schedule.now()+Math.max(0,actionDeadline-schedule.now())/(places.length-i);\n              const tested=await evaluateOption(places[i],trial,{...job,deadline},action.action==='restore'?pending.before.serial:null);\n              if(tested.candidate&&(!best||tested.score>best.score))best=tested;\n            }\n            action.features={...action.features,verified:!!best,assessment:best?'trial':'unknown',actingPlayer:action.state.rules.playerIndex};\n            action.score=null;\n            if(best){action.features={...action.features,...best.features};\n              const sign=action.action==='continue'?1:-1;\n              action.score=sign*best.score;action.nominalScore=sign*best.nominalScore;\n              action.executionScores=best.executionScores.map(row=>({...row,value:sign*row.value}));action.outcome=best.outcome;}\n            choices.push({...action,label:{continue:'接手当前球形',again:'让对手从现位再打',restore:'复位后让对手重打'}[action.action]});\n          }\n          const verified=choices.filter(c=>c.features.verified);\n          choices=verified.length?verified:choices.filter(c=>c.action==='continue');\n        } else {\n          kind=options.isOpening(state)?'opening':state.rules.freeBallAvailable?'free-ball':state.rules.inHand>0?'placement':'colour';\n          let places=variants(state);\n          // Touching colours need an explicit declaration, even for a play-away.\n          if(state.touching?.requiresColourDeclaration)places=state.balls.filter(b=>b.active&&b.n>1).map(b=>({\n            id:'colour-'+b.n,nominee:null,state:{...state,rules:{...state.rules,nominatedColour:b.n,nominationSource:'manual'}},\n            score:null,features:{nominatedColour:b.n}}));\n          for(let i=0;i<places.length;i++) {\n            const place=places[i];\n            if(!available(job))break;\n            const deadline=schedule.now()+Math.max(0,job.deadline-schedule.now())/(places.length-i);\n            await evaluateOption(place,trial,{...job,deadline});\n            place.label=kind==='opening'?'D区薄红球开球':kind==='free-ball'?(place.nominee==null?'不选自由球':'指定自由球'):'安排本杆球位与目标';\n            choices.push(place);\n          }\n          const verified=choices.filter(c=>c.candidate);\n          choices=verified.length?verified:choices.slice(0,1);\n        }\n        if(epoch!==job.epoch)return;\n        if(!choices.length)throw new Error('No legal turn choices available for AI');\n        const shared=[0,1].filter(i=>choices.every(c=>c.executionScores?.some(row=>row.index===i)));\n        for(const choice of choices){\n          if(choice.nominalScore==null)continue;\n          choice.score=shared.length?policy.aggregate(state,choice.executionScores.filter(row=>shared.includes(row.index)).map(row=>row.value)).score:choice.nominalScore;\n          choice.features.comparisonBasis=shared.length?'common-execution':'common-nominal';choice.features.comparedSampleIndices=shared;\n        }\n        choices.sort((a,b)=>b.score-a.score);choices=choices.slice(0,6);\n        clearDeadline();clearTimeout(wallTimer);\n        try {onEvent('turn.search',{kind,elapsedMs:performance.now()-started,budgetMs:18000,scheduling:{...schedule.stats(),wallLimitMs},choices:choices.map(c=>({id:c.id,action:c.action,score:c.score,features:c.features,outcome:c.outcome,position:c.position,nominee:c.nominee}))});}catch(_){}\n        job.phase='turn-selection';changed();\n        const selected=await choose({kind,state:{ballOn:state.rules.ballOn,playerIndex:state.rules.playerIndex,\n          scores:state.scores,remainingPoints:state.remainingPoints,skill:state.skill},choices,\n          timeoutMs:Math.max(1000,90000-(schedule.now()-workStarted)),wallTimeoutMs:Math.max(1,180000-(performance.now()-started)),schedulerSession:schedule});\n        if(epoch!==job.epoch)return;\n        if(JSON.stringify(trial.snapshot())!==before)throw new Error('Position changed; AI decision is stale');\n        lastResult={kind,choiceId:selected.choice.id,reason:selected.reason,options:choices.map(c=>({id:c.id,score:c.score,features:c.features}))};\n        commit(selected.choice,kind,selected.reason,selected.source);\n      } catch(error) {if(epoch===job.epoch){failed=true;onError(error);}}\n      finally {clearDeadline();clearTimeout(wallTimer);schedule.close();if(active===job)active=null;changed();}\n    }\n    return {run,cancel,getStatus:status};\n  }\n  return {create};\n})();\n\n/* Local search shares one work budget; deliberate UI yields have a separate wall limit. */\nconst PCOLSearch=(()=>{\n  const limit=(v,d,a,b)=>Number.isFinite(v)?Math.max(a,Math.min(b,v)):d;\n  const key=s=>[s.nominatedColour||0,Math.atan2(s.shot.direction.z,s.shot.direction.x),s.shot.power,s.shot.vertical||0,s.shot.side||0,s.shot.elevation||0].map(x=>Math.round(x*100000)).join(':');\n  function create({getTrial,getState,geometry,policy,skill,continuation,development,brain,scheduler}) {\n    const scheduling=scheduler||(typeof PCOLComputeScheduler!=='undefined'?PCOLComputeScheduler:require('./compute-scheduler')).create();\n    let active=null,lastResult=null;\n    const stop=reason=>{if(active){active.reason=reason;active.schedule.cancel();if(active.inFlight)active.trial.cancel();}};\n    function preparePlan(previous,context={}) {\n      const snapshot=getTrial().snapshot(),state=getState(snapshot),brief=brain.analyze(state,geometry),actor=state.rules.playerIndex;\n      const planCompliance=brain.compliance(state,previous?.expectedNext,geometry),last=context.lastOutcome;\n      let reason=!previous?'new-visit':previous.actor!==actor?'actor-changed':\n        !last||last.actor!==actor||!(last.score>0)||last.foulCode?'turn-changed':\n        previous.objective!=='need-snookers'&&brief.task==='need-snookers'?'need-snookers':\n        previous.lastWasDevelopment?'after-development':\n        previous.coverageInsufficient&&(!planCompliance.met||!previous.expectedNext?.intent)?'coverage-insufficient':\n        !planCompliance.met?'position-lost':!previous.expectedNext?.intent?'transition-not-covered':null;\n      const continuedPlan=reason?null:{...previous,...brain.normalizePlan({primaryIntent:previous.expectedNext.intent,\n        fallbackIntent:previous.fallbackIntent,reason:previous.reason},brief)};\n      if(continuedPlan?.primaryIntent.task==='develop')reason='prepare-development';\n      return {brief,preparedRoot:{fingerprint:JSON.stringify(snapshot),brief,style:state.style},needsReplan:!!reason,reason,planCompliance,continuedPlan};\n    }\n    async function run(options={}) {\n      if(active)throw new Error('A candidate search is already running');\n      const started=performance.now(),trial=options.trial||getTrial();\n      if(trial.getStatus?.().busy)throw new Error('Wait for the current trial before searching');\n      const before=options.snapshot||trial.snapshot(),fingerprint=JSON.stringify(before);\n      const liveFingerprint=trial.fingerprint?.(),checkedRoots=new WeakSet();\n      const state={...(options.state||getState(before))};state.rules={...state.rules};\n      state.rootPlayerIndex=state.rules.playerIndex??0;state.style='unified';\n      if(options.skill)state.skill=options.skill;\n      const rules=state.rules,reviewReasons=[];\n      if(!rules.ballOn||rules.ballOn===65535)reviewReasons.push('Search requires standard snooker rules');\n      if(rules.freeBallReview||(rules.freeBallAvailable&&rules.freeBallNominee==null&&!rules.freeBallDeclined))reviewReasons.push('Resolve the free-ball choice first');\n      if(state.touching?.requiresColourDeclaration&&rules.nominationSource!=='manual')reviewReasons.push('Declare the touching colour first');\n      if(reviewReasons.length)return {status:'needs-ruling',reviewReasons,candidates:[],elapsedMs:performance.now()-started};\n      const budgetMs=limit(options.budgetMs,45000,100,90000);\n      const maxCandidates=Math.floor(limit(options.maxCandidates,96,1,288)),maxResults=Math.floor(limit(options.maxResults,4,1,4));\n      const samples=Math.floor(limit(options.riskSamples,2,0,6)),branchCap=Math.floor(limit(options.continuationTrials,6,0,12));\n      const riskCap=samples*8;\n      const schedule=options.schedulerSession||scheduling.start({cooperativeYield:options.cooperativeYield});\n      const initialScheduling=schedule.stats(),workStarted=schedule.now()-(performance.now()-started),deadline=workStarted+budgetMs;\n      const job=active={trial,schedule,inFlight:false,reason:null,phase:'routes'};\n      // The absolute guard is separate from effective compute time. Its margin\n      // accommodates the normal 6 ms / 4 ms cadence without cutting search work.\n      const wallLimitMs=Math.max(1000,budgetMs*2+1000);\n      const clearDeadline=schedule.setDeadline(deadline,()=>stop('budget-exhausted'));\n      const wallTimer=setTimeout(()=>stop('budget-exhausted'),Math.max(0,started+wallLimitMs-performance.now()));\n      const cooperate=()=>job.reason?false:schedule.checkpoint();\n      const accepted=[],cache=new Map(),outcomes=new Map(),evaluations=new Map(),sampled=new Map(),durations=[],stages=[];\n      const counts={generated:0,tried:0,completed:0,incomplete:0,rejected:0,reused:0,recovery:0,refined:0,development:0,riskTrials:0,boundaryTrials:0,branchTrials:0,reasons:{ruling:0,foul:0,miss:0}};\n      const current=()=>{try{return liveFingerprint!==undefined?trial.fingerprint()===liveFingerprint:JSON.stringify(trial.snapshot())===fingerprint;}catch(_){return false;}};\n      const available=(reserve=0)=>!job.reason&&deadline-schedule.now()>reserve;\n      const prepared=options.preparedRoot;\n      const brief=brain&&(prepared&&!options.state&&prepared.fingerprint===fingerprint?prepared.brief:brain.analyze(state,geometry)),plan=brain?brain.normalizePlan(options.plan||{},brief):null;\n      const searchIntent={primaryIntent:plan?.primaryIntent,fallbackIntent:plan?.fallbackIntent,used:'unified',fallbackTriggered:false,reason:'compare-independent-opportunities'};\n      const intentFor=seed=>{\n        if(!plan)return null;\n        const edge=brief.transitionGraph?.find(e=>e.fromId===seed.targetIndex);\n        return {task:seed.development?'develop':seed.kind==='attack'?'position':seed.kind==='escape'?'escape':brief.task==='need-snookers'?'need-snookers':'contain',\n          targetId:seed.targetIndex,nextBallId:edge?.toId??null,sectorId:edge?.sectorId??null,preserveIds:(brief.preserveIds||[]).filter(i=>i!==seed.targetIndex)};\n      };\n      const intentWorks=c=>c.intentMet&&\n        (!skill||!samples||(sampled.get(c.id)?.length||0)>=samples)&&\n        !(sampled.get(c.id)||[]).some(row=>!row.evidence.legal||row.evidence.planCompliance?.intentMet===false);\n      const policySession=policy?.createSession?.(geometry);\n      const evaluatePolicy=policySession?((candidate,r)=>policySession.evaluate(state,candidate,r)):policy?.createEvaluator?.(state,geometry);\n      const evaluate=(candidate,r,expectedNext=false)=>{\n        const e=evaluatePolicy?evaluatePolicy(candidate,r):policy?policy.evaluate(state,candidate,r,geometry):geometry.evaluate(state,candidate,r);\n        const assessment=brain&&candidate.intent?brain.assess(state,candidate,r,candidate.intent,geometry,brief,{expectedNext}):null;\n        return {...e,score:e.score,features:{...e.features,...assessment?.features},assessment};\n      };\n      function evidence(r,e) {\n        const v=r.adjudication,actor=state.rules.playerIndex??0;\n        return {actor,nextActor:e.features?.nextPlayerIndex??r.nextContext?.playerIndex??r.nextSnapshot?.rules?.playerIndex??(v.continueBreak?actor:1-actor),\n          legal:!v.foulCode,potted:r.potted||[],foulCode:v.foulCode||0,penalty:v.foulCode?Math.max(0,-(v.score||0)):0,\n          points:v.score||0,components:{netPoints:e.netPoints??e.features?.netPoints??null,immediateCost:e.immediateCost??e.features?.immediateCost??null,\n            futureValue:e.futureValue??e.features?.futureValue??null,terminalValue:e.terminalValue??e.features?.terminalValue??null},\n          opponentSnookered:e.features?.opponentSnookered??null,selfSnookered:e.features?.selfSnookered??null,\n          scoreBeforeBranches:e.score,branchDelta:0,scoreAfterBranches:e.score,continuation:{status:'unassessed',trials:0}};\n      }\n      const context=policy?.analyze(state);\n      const aggregate=values=>policy?.aggregate?policy.aggregate(state,values):{score:values.reduce((a,b)=>a+b,0)/values.length,mean:values.reduce((a,b)=>a+b,0)/values.length,downside:0,riskPreference:0};\n      const descriptor=c=>skill?.describe(state,c,options.skill||state.skill||'strong');\n      const powerWindow=c=>Math.sqrt(3)*(c.skill||descriptor(c))?.powerSigma||0;\n      const bufferedPower=(c,reachedPower,observedShortfall=0)=>{\n        let power=reachedPower;\n        for(let i=0;i<4;i++)power=reachedPower+Math.max(observedShortfall,powerWindow({...c,skill:null,shot:{...c.shot,power}}));\n        return Math.min(.85,power+1e-5);\n      };\n      const sameDirection=(a,b)=>a&&b&&Math.abs(Math.atan2(a.x*b.z-a.z*b.x,a.x*b.x+a.z*b.z))<=.006;\n      // The caller supplies only failures from this exact restored layout. Match the\n      // stroke as well, so a failure cannot contaminate another ball, pocket or spin.\n      const failuresFor=c=>(options.failureEvidence||[]).filter(f=>f.targetIndex===c.targetIndex&&\n        (f.nominatedColour||0)===(c.nominatedColour||0)&&\n        (c.kind!=='attack'||f.pocketIndex===c.pocketIndex)&&f.shot&&sameDirection(f.shot.direction,c.shot.direction)&&\n        Math.abs((f.shot.vertical||0)-(c.shot.vertical||0))<=.08&&\n        Math.abs(f.shot.power-c.shot.power)<=Math.max(.025,powerWindow(c))&&\n        ((f.result?.firstHits?.length===0)||(c.kind==='attack'&&!(f.result?.score>0))));\n      async function simulate(shot,nomination,parent=null) {\n        if(!available())return null;\n        if(!await cooperate()||!available())return null;\n        if(!current()){job.reason='stale';return null;}\n        job.inFlight=true;const t=performance.now();\n        try {\n          const opts={nominatedColour:nomination,maxWallMs:Math.min(5000,Math.max(1,deadline-schedule.now())),trace:brain?'cue':false};\n          const pending=parent?trial.simulateFrom(parent,shot,opts):trial.simulate(shot,opts);\n          const r=await schedule.wait(pending);\n          if(r.stale||r.snapshot&&!checkedRoots.has(r.snapshot)&&JSON.stringify(r.snapshot)!==fingerprint){job.reason='stale';return null;}\n          if(r.snapshot)checkedRoots.add(r.snapshot);\n          return r;\n        }catch(error){if(!current())job.reason='stale';if(job.reason)return null;throw error;}\n        finally{durations.push(performance.now()-t);job.inFlight=false;}\n      }\n      async function stage(name,work) {\n        job.phase=name;const t=performance.now(),n=durations.length,r=counts.rejected;\n        await work();await cooperate();stages.push({name,elapsedMs:Math.round(performance.now()-t),trials:durations.length-n,rejected:counts.rejected-r});\n      }\n      async function explore(seeds,cap,reserve=0,stopAfterLegal=false) {\n        counts.generated+=seeds.length;let used=0;\n        for(const input of seeds) {\n          const seedIntent=input.intent||intentFor(input);\n          const seed=seedIntent?{...input,intent:seedIntent,intentSource:job.phase}:input;\n          if(!available(reserve)||used>=cap||counts.tried>=maxCandidates)break;\n          const k=key(seed);let r=cache.get(k);\n          if(r){counts.reused++;if(accepted.some(c=>key(c)===k))continue;}\n          else {used++;counts.tried++;r=await simulate(seed.shot,seed.nominatedColour);if(!r)break;}\n          if(r.status!=='complete'){counts.incomplete++;continue;}\n          counts.completed++;cache.set(k,r);\n          if(!r.adjudication||!r.nextBalls){counts.rejected++;counts.reasons.ruling++;continue;}\n          // Only settled legal nominal strokes may be executed; sampled fouls still count as risk.\n          if(r.adjudication.foulCode){counts.rejected++;counts.reasons.foul++;continue;}\n          if(seed.kind==='attack'&&!r.potted?.some(i=>i===seed.targetIndex||i===seed.potTargetIndex))counts.reasons.miss++;\n          const e=evaluate(seed,r),cue=r.nextBalls.find(b=>b.n===0),v=r.adjudication;\n          let effect=e.features?.effect||policy?.classify?.(state,seed,r,geometry)||(v.score>0?'attack':'contain');\n          if(e.assessment?.features.problemHandled)effect='development';\n          else if(v.score>0&&e.assessment?.features.cueSectorReached&&e.assessment?.features.nextRouteAvailable)\n            effect=e.assessment.features.arrivalAligned?'position':'attack';\n          const c={...seed,id:'shot-'+accepted.length,effect,expectedNext:e.assessment?.expectedNext,\n            intentMet:e.assessment?.met??false,score:e.score,nominalScore:e.score,features:e.features,evidence:{nominal:{...evidence(r,e),planCompliance:e.assessment?.features},samples:[]},\n            skill:descriptor(seed),stroke:r.stroke,actual:r.compiled?.actual,\n            outcome:{score:v.score,foulCode:v.foulCode,potted:r.potted,firstHits:r.firstHits,nextBallOn:v.nextBallOn,\n              continueBreak:v.continueBreak,nominatedColour:rules.ballOn===252?v.ballOnUsed:rules.nominatedColour,\n              cue:cue&&{x:cue.x,y:cue.y,z:cue.z},simulatedSeconds:r.simulatedSeconds}};\n          c.evidence.nominal.delivery={firstContactMade:r.firstHits?.includes(seed.targetIndex)??false,\n            targetPotted:!!r.potted?.some(i=>i===seed.targetIndex||i===seed.potTargetIndex)};\n          if(c.executionRepair)c.executionRepair={...c.executionRepair,lowErrorPower:Math.max(0,c.shot.power-powerWindow(c)),\n            goalVerified:c.kind==='attack'?c.evidence.nominal.delivery.targetPotted:c.evidence.nominal.delivery.firstContactMade};\n          accepted.push(c);outcomes.set(c.id,r);evaluations.set(c.id,e);\n          if(stopAfterLegal)break;\n        }\n      }\n      const routeKey=c=>geometry.routeKey?geometry.routeKey(c):[c.kind,c.targetIndex,c.pocketIndex,c.nominatedColour].join(':');\n      function shortlist(count,fresh=false) {\n        // This is a proposal queue, not a ranking of sampled and nominal values.\n        const sorted=accepted.filter(c=>!fresh||(sampled.get(c.id)?.length||0)<samples).sort((a,b)=>b.nominalScore-a.nominalScore);\n        const preferred=new Map();\n        for(const c of sorted)if(c.executionRepair?.goalVerified&&!preferred.has(routeKey(c)))preferred.set(routeKey(c),c);\n        const proposed=[...new Set(sorted.map(c=>preferred.get(routeKey(c))||c))];\n        const chosen=[],routes=new Set(),targets=new Set();\n        const add=c=>{if(c&&chosen.length<count&&!routes.has(routeKey(c))){chosen.push(c);routes.add(routeKey(c));targets.add(c.targetIndex);}};\n        add(proposed[0]);add(proposed.find(c=>c.outcome.score>0));\n        add(proposed.find(c=>['snooker','contain'].includes(c.effect)));\n        for(const c of proposed)if(!targets.has(c.targetIndex))add(c);\n        for(const c of proposed)add(c);\n        // Once independent routes are covered, a refinement can challenge its parent.\n        for(const c of sorted)if(chosen.length<count&&!chosen.includes(c))chosen.push(c);\n        return chosen;\n      }\n      function updateRisk(c,indices=null) {\n        const rows=(sampled.get(c.id)||[]).filter(row=>!indices||indices.includes(row.evidence.sampleIndex)),values=rows.map(r=>r.value),n=values.length;\n        if(!n)return;\n        const combined=aggregate(values),{mean,downside,riskPreference}=combined;\n        const safeMisses=rows.filter(r=>r.features?.safeMiss===true).length;\n        const costlyMisses=rows.filter(r=>r.features?.costlyMiss===true).length;\n        const hasFoul=rows.some(r=>r.result.adjudication.foulCode);\n        const twoWay=!!(rows.some(row=>row.result.adjudication.score>0)&&!hasFoul&&costlyMisses===0&&safeMisses>0);\n        const effectiveDownside=downside,twoWayBonus=0;\n        c.score=combined.score;\n        c.features={...c.features,twoWay,safeMissRate:safeMisses/n,costlyMissRate:costlyMisses/n,twoWayBonus};\n        c.evidence.samples=(sampled.get(c.id)||[]).map(r=>r.evidence);\n        c.evidence[indices?'comparisonExecution':'execution']={score:c.score,sampleCount:n,sampleIndices:rows.map(row=>row.evidence.sampleIndex),availableSamples:sampled.get(c.id).length,coverage:n>=samples?'complete':'partial',sampleDesign:'common stratified three-axis pairs; additional pairs change error direction'};\n        c.evidence.aggregation={source:'execution-samples',mean,downside,effectiveDownside,twoWayBonus,riskPreference,finalScore:c.score};\n        c.risk={...c.risk,samples:n,incomplete:sampled.get(c.id).incomplete||0,legalRate:rows.filter(r=>!r.result.adjudication.foulCode).length/n,\n          potRate:rows.filter(r=>r.result.adjudication.score>0).length/n,foulRate:rows.filter(r=>r.result.adjudication.foulCode).length/n,\n          safeMissRate:safeMisses/n,costlyMissRate:costlyMisses/n,twoWay,\n          meanScore:mean,downside,confidence:'limited',interpretation:'execution samples, not calibrated probabilities'};\n      }\n      async function risk(finalists,reserve,targetSamples=samples) {\n        if(!skill||!samples)return;\n        for(let n=0;n<targetSamples&&available(reserve);n++) {\n          const values=skill.coordinates?skill.coordinates(n):(n%2?[.75,.75,.25]:[.25,.25,.75]);\n          for(const c of finalists){if(!available(reserve)||counts.riskTrials>=riskCap)break;if(sampled.get(c.id)?.some(row=>row.evidence.sampleIndex===n))continue;let i=0;counts.riskTrials++;\n            const r=await simulate(skill.perturb(c.shot,c.skill,()=>values[i++%3]),c.nominatedColour);\n            const rows=sampled.get(c.id)||[];sampled.set(c.id,rows);\n            if(r?.status!=='complete'||!r.adjudication||!r.nextBalls){rows.incomplete=(rows.incomplete||0)+1;continue;}\n            const e=evaluate(c,r,false);rows.push({result:r,evaluated:e,value:e.score,features:e.features,evidence:{sampleIndex:n,powerUniformCoordinate:values[1],...evidence(r,e),\n              delivery:{firstContactMade:r.firstHits?.includes(c.targetIndex)??false,targetPotted:!!r.potted?.some(i=>i===c.targetIndex||i===c.potTargetIndex)},planCompliance:e.assessment?.features}});\n            if(values[1]<.5&&(!r.firstHits?.includes(c.targetIndex)||c.kind==='attack'&&!r.potted?.some(i=>i===c.targetIndex||i===c.potTargetIndex)))c.executionConcern={source:'sampled-low-power-failure'};\n            updateRisk(c);\n          }\n        }\n      }\n      async function continuations(finalists,commonIndices) {\n        if(!continuation||typeof trial.simulateFrom!=='function'||!branchCap)return;\n        // Preserve the old total ceiling (four finalists times branchCap), shared by the entire verified pool.\n        const commonSamples=commonIndices.length,continuationSession=continuation.createSession?.({policySession})||continuation;\n        let remaining=4*branchCap;\n        const branchCache=new Map();\n        const trialBranch=async(parent,seed)=>{let hits=branchCache.get(parent);if(!hits){hits=new Map();branchCache.set(parent,hits);}const k=key(seed);if(hits.has(k))return hits.get(k);if(remaining<=0)return null;counts.branchTrials++;remaining--;const r=await simulate(seed.shot,seed.nominatedColour,parent);hits.set(k,r);return r;};\n        const assessed=finalists.slice().sort((a,b)=>b.score-a.score).slice(0,4);\n        for(const c of finalists)if(!assessed.includes(c)){\n          c.horizon='unknown';c.evidence.continuation={score:null,coverage:'unknown',depth:0,samples:0};\n        }\n        const roots=assessed.reduce((n,c)=>n+(commonSamples||1),0);\n        const capPerRoot=Math.min(branchCap,Math.floor(remaining/Math.max(1,roots)));\n        for(const c of assessed) {\n          c.shallowScore=c.score;\n          const rows=sampled.get(c.id),branches=commonSamples?rows.filter(row=>commonIndices.includes(row.evidence.sampleIndex)):[{result:outcomes.get(c.id),evaluated:evaluations.get(c.id),value:c.score,evidence:c.evidence.nominal}];\n          for(let i=0;i<branches.length&&remaining>0&&available();i++) {\n            const row=branches[i];\n            const planned=await continuationSession.evaluate({state,candidate:c,result:row.result,policySession,preparedEvaluation:row.evaluated,maxTrials:Math.min(capPerRoot,remaining),canContinue:()=>available(),\n              simulateFrom:trialBranch});\n            Object.assign(row.evidence,{branchDelta:planned.scoreDelta,scoreAfterBranches:row.value+planned.scoreDelta,continuation:planned.summary});\n            if(i===0)c.plan={...planned.summary,source:commonSamples?'execution-sample':'nominal',sampleIndex:commonSamples?row.evidence.sampleIndex:null};\n          }\n          const depth=branches[0]?.evidence.continuation.depth;\n          const covered=branches.every(row=>row.evidence.continuation.coverage==='covered'&&row.evidence.continuation.depth===depth);\n          c.horizon=covered?'covered':'unknown';\n          if(covered){\n            c.continuationScore=aggregate(branches.map(row=>row.evidence.scoreAfterBranches)).score;\n          }\n          c.evidence.continuation={score:c.continuationScore??null,coverage:covered?'complete':branches.some(row=>row.evidence.continuation.trials>0)?'partial':'unknown',depth,samples:branches.length};\n          c.evidence.comparison={...c.evidence.comparison,horizon:c.horizon};\n        }\n        // With one child per error endpoint, selectively extend two leading independent routes.\n        // Reuse their first layer and deepen every sample, including misses; no best-sample cherry-picking.\n        if(capPerRoot===1&&remaining>0){\n          const ordered=finalists.filter(c=>c.horizon==='covered').sort((a,b)=>b.continuationScore-a.continuationScore),seen=new Set();let probed=0;\n          for(const c of ordered){\n            if(probed>=2||remaining<(commonSamples||1)||!available())break;\n            if(c.horizon!=='covered'||seen.has(routeKey(c)))continue;seen.add(routeKey(c));probed++;\n            const rows=sampled.get(c.id),branches=commonSamples?rows.filter(row=>commonIndices.includes(row.evidence.sampleIndex)):[{result:outcomes.get(c.id),evaluated:evaluations.get(c.id),value:c.score,evidence:c.evidence.nominal}];\n            const probes=[];\n            for(const row of branches){const p=await continuationSession.evaluate({state,candidate:c,result:row.result,policySession,preparedEvaluation:row.evaluated,maxTrials:2,depth:2,breadth:1,canContinue:()=>available(),simulateFrom:trialBranch});\n              probes.push({...p,score:row.value+p.scoreDelta});}\n            c.evidence.secondLayer=probes.map(p=>({score:p.score,summary:p.summary}));\n            c.evidence.secondLayerComparison={basis:'diagnostic-only',reason:'second layer is not shared by the comparison pool'};\n          }\n        }\n      }\n      async function softControls(reserveMs) {\n        for(const seed of geometry.softContacts?.(state)||[]) {\n          let low=0,high=.28,reached=false;\n          // Native contact, not a distance-to-power guess, brackets the least force that reaches this ball.\n          for(let i=0;i<3&&available(reserveMs)&&counts.tried<maxCandidates;i++) {\n            const candidate={...seed,shot:{...seed.shot,power:(low+high)/2}};\n            await explore([candidate],1,reserveMs);\n            const r=cache.get(key(candidate));\n            if(r?.firstHits?.includes(seed.targetIndex)){high=candidate.shot.power;reached=true;}\n            else low=candidate.shot.power;\n          }\n          if(reached&&skill&&available(reserveMs)&&counts.tried<maxCandidates){\n            const power=bufferedPower(seed,high),candidate={...seed,shot:{...seed.shot,power},\n              executionRepair:{source:'native-contact-bracket',failedPower:low,reachedPower:high,\n                lowErrorPower:power-powerWindow({...seed,shot:{...seed.shot,power}})}};\n            await explore([candidate],1,reserveMs);\n          }\n        }\n      }\n      async function boundaryProbe(c,reserveMs) {\n        const window=powerWindow(c);if(!window||!available(reserveMs)||counts.tried>=maxCandidates)return;\n        const candidate={...c,shot:{...c.shot,power:Math.max(0,c.shot.power-window)}},k=key(candidate);\n        let r=cache.get(k);\n        if(r)counts.reused++;\n        else {counts.tried++;counts.generated++;counts.boundaryTrials++;r=await simulate(candidate.shot,c.nominatedColour);if(r?.status==='complete')cache.set(k,r);}\n        const settled=r?.status==='complete'&&r.adjudication&&r.nextBalls;\n        if(settled)counts.completed++;else counts.incomplete++;\n        const goal=settled&&!r.adjudication.foulCode&&(c.kind==='attack'?r.potted?.some(i=>i===c.targetIndex||i===c.potTargetIndex):r.firstHits?.includes(c.targetIndex));\n        c.evidence.robustness={basis:'isolated-power-support-boundary',status:settled?'complete':'incomplete',\n          testedPower:candidate.shot.power,goalVerified:!!goal,score:r?.adjudication?.score,foulCode:r?.adjudication?.foulCode,\n          firstHits:r?.firstHits,potted:r?.potted,interpretation:'boundary diagnostic, excluded from execution mean'};\n        if(settled&&!goal&&c.evidence.nominal.delivery[c.kind==='attack'?'targetPotted':'firstContactMade'])\n          c.executionBoundary={source:'native-power-boundary',failedPower:candidate.shot.power,reachedPower:c.shot.power,\n            repairPower:bufferedPower(c,c.shot.power)};\n      }\n      try {\n        const useFixedReserve=budgetMs>=4000&&(skill&&samples>0||continuation);\n        const finalReserveMs=useFixedReserve?Math.min(9000,budgetMs*.20):0;\n        const coverageReserveMs=useFixedReserve?Math.min(15000,budgetMs*.32):0;\n        const fallbackReserveMs=useFixedReserve?Math.min(24000,budgetMs*.46):0;\n        const reserve=(phase='default')=>{\n          const dynamic=Math.min(12000,Math.max(0,deadline-schedule.now())*.3);\n          if(!useFixedReserve)return dynamic;\n          if(phase==='primary')return Math.max(fallbackReserveMs,dynamic);\n          if(phase==='fallback')return Math.max(coverageReserveMs,dynamic*.8);\n          return finalReserveMs;\n        };\n        const baseSeeds=geometry.generate(state);\n        const intentSeeds=intent=>{\n          const developed=intent.task==='develop'&&development?development.generate(state,geometry):[];\n          const directed=brain.directed(state,developed.length?developed:baseSeeds,intent,geometry,brief);\n          return directed.concat(developed,baseSeeds.filter(c=>c.targetIndex===intent.targetId));\n        };\n        // Cover real opportunities before spending on a visit plan's refinements.\n        await stage('coverage',()=>explore(baseSeeds,Math.min(36,maxCandidates),reserve('primary')));\n        if(plan&&available(reserve('fallback'))){\n          const intents=[plan.primaryIntent,plan.fallbackIntent];\n          for(const c of shortlist(3))if(c.intent&&!intents.some(i=>i.task===c.intent.task&&i.targetId===c.intent.targetId))intents.push(c.intent);\n          const groups=intents.map(intent=>intentSeeds(intent).map(c=>({...c,intent:{...intent,targetId:c.targetIndex}})));\n          const directed=[];\n          for(let i=0;i<Math.max(0,...groups.map(g=>g.length));i++)for(const group of groups)if(group[i])directed.push(group[i]);\n          await stage('position-options',()=>explore(directed,18,reserve('fallback')));\n        }\n        // Validate early proposals before refinement; their evidence stays eligible.\n        await stage('route-evidence',()=>risk(shortlist(4),reserve('coverage')));\n        if(development&&available(reserve()))await stage('development',async()=>{const seeds=development.generate(state,geometry);counts.development=seeds.length;await explore(geometry.diverse?geometry.diverse(seeds):seeds,8,reserve());});\n        if(geometry.softContacts&&available(reserve()))await stage('soft-control',()=>softControls(reserve()));\n        if(!accepted.some(c=>!c.outcome.foulCode)&&geometry.generateRecovery&&available(reserve()))await stage('recovery',async()=>{const seeds=geometry.generateRecovery(state);counts.recovery=seeds.length;await explore(seeds,18,reserve());});\n        if(!accepted.length&&geometry.generateRecovery&&available())await stage('multi-cushion-recovery',async()=>{const seeds=geometry.generateRecovery(state,{multiCushion:true});counts.recovery+=seeds.length;await explore(seeds,maxCandidates-counts.tried,0,true);});\n        if(geometry.refine&&available(reserve('coverage')))await stage('refinement',async()=>{\n          const parents=[],routes=new Set();\n          for(const c of accepted.filter(c=>failuresFor(c).length).concat(shortlist(3))){\n            if(parents.length===3)break;if(routes.has(routeKey(c)))continue;parents.push(c);routes.add(routeKey(c));\n          }\n          for(const c of parents){\n            const failures=failuresFor(c),count=failures.reduce((sum,f)=>sum+Math.max(1,f.count||1),0);\n            if(count)c.evidence.restoredFailures={count,source:'same-layout-delivery',matching:'target, nomination, pocket and stroke'};\n            if(c.evidence.nominal.delivery[c.kind==='attack'?'targetPotted':'firstContactMade']&&\n              (c.kind==='attack'||c.softContact||count||c.executionConcern)&&!c.executionRepair)await boundaryProbe(c,reserve('coverage'));\n            const shortfall=Math.max(0,...failures.map(f=>f.shot.power-(f.actualShot?.power??f.shot.power)));\n            if(count>=2&&shortfall>0&&c.evidence.nominal.delivery[c.kind==='attack'?'targetPotted':'firstContactMade'])\n              c.executionBoundary={...c.executionBoundary,source:c.executionBoundary?.source||'repeated-delivery-failure',\n                reachedPower:c.shot.power,repairPower:bufferedPower(c,c.shot.power,shortfall),failureCount:count};\n          }\n          const groups=parents.map(c=>geometry.refine(state,{...c,contacts:outcomes.get(c.id)?.contacts})),seeds=[];\n          // Spend the existing twelve refinements across routes before second variants.\n          for(let i=0;i<Math.max(0,...groups.map(g=>g.length));i++)for(const group of groups)if(group[i])seeds.push(group[i]);\n          counts.refined=seeds.length;await explore(seeds,12,reserve('coverage'));});\n        const riskReserve=continuation?Math.min(5000,Math.max(0,deadline-schedule.now())*.2):0;\n        let contenders=accepted.filter(c=>(sampled.get(c.id)?.length||0)>=samples&&samples>0).sort((a,b)=>b.score-a.score);\n        // A new independent route or repaired stroke may challenge the tested pool.\n        const fresh=shortlist(2,true).filter(c=>!contenders.length||c.nominalScore>=contenders[0].score||c.executionRepair?.goalVerified);\n        if(fresh.length)await stage('risk',()=>risk(fresh,riskReserve));\n        contenders=accepted.filter(c=>(sampled.get(c.id)?.length||0)>=samples&&samples>0).sort((a,b)=>b.score-a.score);\n        let comparedPair=[];\n        if(contenders.length>1&&available(riskReserve)){\n          const pair=contenders.slice(0,2),gap=pair[0].score-pair[1].score;\n          const spread=Math.max(...pair.map(c=>{const v=sampled.get(c.id).map(r=>r.value);return Math.max(...v)-Math.min(...v);}));\n          if(gap<=Math.max(1,spread)||pair.some(c=>c.executionConcern||c.development)){\n            const extra=2*Math.floor((riskCap-counts.riskTrials)/4),target=Math.min(6,samples+extra);\n            if(target>samples){comparedPair=pair;await stage('decision-evidence',()=>risk(pair,riskReserve,target));}\n          }\n        }\n        // Every earlier verified stroke stays eligible, even if its refined replacement fails.\n        const verified=accepted.filter(c=>(sampled.get(c.id)?.length||0)>0);\n        const comparable=verified.length?verified:shortlist(4);\n        const commonIndices=verified.length?sampled.get(verified[0].id).map(row=>row.evidence.sampleIndex).filter(i=>i<samples&&verified.every(c=>sampled.get(c.id).some(row=>row.evidence.sampleIndex===i))):[];\n        for(const c of comparable) {\n          if(commonIndices.length)updateRisk(c,commonIndices);else {c.score=c.nominalScore;c.evidence.aggregation={source:'common-nominal',finalScore:c.score};}\n          c.evidence.comparison={basis:commonIndices.length?'common-shallow':'common-nominal',sampleIndices:commonIndices,shallowScore:c.score};\n          const n=sampled.get(c.id)?.length||0;\n          c.risk={...c.risk,samples:commonIndices.length,availableSamples:n,comparedSamples:commonIndices.length,coverage:!samples||!skill?'disabled':n>=samples?'complete':n?'partial':'unassessed'};\n        }\n        await stage('continuations',()=>continuations(comparable,commonIndices));\n        for(const c of comparable)if(!c.evidence.aggregation)c.evidence.aggregation={source:'nominal',finalScore:c.score};\n        let status=job.reason||(schedule.now()>=deadline?'budget-exhausted':counts.tried>=maxCandidates?'candidate-limit':'complete');\n        if(!current())status='stale';\n        if(!comparable.length&&!['stale','cancelled'].includes(status))status='no-candidates';\n        const sorted=durations.slice().sort((a,b)=>a-b),quantile=q=>sorted.length?Math.round(sorted[Math.min(sorted.length-1,Math.floor((sorted.length-1)*q))]):null;\n        counts.trialMs={count:sorted.length,median:quantile(.5),p90:quantile(.9)};\n        const ranking=(a,b)=>Number(!!a.features?.mathematicallyDead)-Number(!!b.features?.mathematicallyDead)||b.score-a.score;\n        comparable.sort(ranking);\n        // Incomplete horizons are barriers, not zero-valued rivals. Reorder only adjacent\n        // fully covered peers at the same depth, preserving the common shallow order elsewhere.\n        for(let i=0;i<comparable.length;){\n          if(comparable[i].horizon!=='covered'){i++;continue;}\n          const depth=comparable[i].evidence.continuation.depth;let j=i+1;\n          while(j<comparable.length&&comparable[j].horizon==='covered'&&comparable[j].evidence.continuation.depth===depth&&\n            !!comparable[j].features?.mathematicallyDead===!!comparable[i].features?.mathematicallyDead)j++;\n          if(j-i>1){const peers=comparable.slice(i,j).sort((a,b)=>b.continuationScore-a.continuationScore);\n            for(const c of peers)c.evidence.comparison.basis='common-bounded-horizon';comparable.splice(i,j-i,...peers);}\n          i=j;\n        }\n        if(comparedPair.length===2&&comparedPair.every(c=>comparable.slice(0,2).includes(c))){\n          const indices=sampled.get(comparedPair[0].id).map(r=>r.evidence.sampleIndex).filter(i=>sampled.get(comparedPair[1].id).some(r=>r.evidence.sampleIndex===i));\n          // Do not replace a completed continuation comparison with a shallower one.\n          if(indices.length>commonIndices.length&&!comparedPair.every(c=>c.horizon==='covered')){\n            for(const c of comparedPair){const value=aggregate(sampled.get(c.id).filter(r=>indices.includes(r.evidence.sampleIndex)).map(r=>r.value));\n              c.evidence.pairedExecution={...value,sampleIndices:indices,peerId:comparedPair.find(p=>p!==c).id};}\n            const peers=comparedPair.slice().sort((a,b)=>Number(!!a.features?.mathematicallyDead)-Number(!!b.features?.mathematicallyDead)||b.evidence.pairedExecution.score-a.evidence.pairedExecution.score);\n            comparable.splice(0,2,...peers);for(const c of peers)c.evidence.comparison.basis='common-paired-execution';\n          }\n        }\n        const chosen=comparable[0],categoryBest={};\n        // Next-visit plans do not affect this shot's score, coverage or ranking.\n        // Build them only for the returned candidates, after comparison is complete.\n        const finalists=comparable.slice(0,maxResults);\n        if(brain)for(const c of finalists)if(c.intent)\n          c.expectedNext=brain.assess(state,c,outcomes.get(c.id),c.intent,geometry,brief,{expectedNext:true}).expectedNext;\n        searchIntent.selected=chosen?.intentSource||null;\n        searchIntent.achieved=!!chosen&&intentWorks(chosen);\n        for(const c of accepted.slice().sort((a,b)=>b.score-a.score))if(!categoryBest[c.effect])categoryBest[c.effect]={\n          id:c.id,effect:c.effect,targetIndex:c.targetIndex,score:c.score,selected:comparable.includes(c),\n          cue:c.outcome.cue,points:c.outcome.score,intentMet:c.intentMet,opponentChance:c.features.opponentChance,\n          nextRouteAvailable:c.features.nextRouteAvailable,snookered:c.features.opponentSnookered};\n        const activePlan=plan&&{...plan,actor:rules.playerIndex,round:rules.nRounds,objective:context?.objective,\n          expectedNext:chosen?.expectedNext,lastWasDevelopment:chosen?.effect==='development'||chosen?.intent?.task==='develop',\n          coverageInsufficient:!chosen||(!intentWorks(chosen)&&!(chosen.outcome?.score>0&&chosen.outcome?.continueBreak&&chosen.expectedNext?.intent)),\n          selectedIntent:chosen?.intent};\n        const elapsedMs=performance.now()-started,metrics=schedule.stats(),waitMs=metrics.waitMs-initialScheduling.waitMs;\n        lastResult={status,budgetMs,elapsedMs,scheduling:{enabled:metrics.enabled,yields:metrics.yields-initialScheduling.yields,waitMs,budgetElapsedMs:elapsedMs-waitMs,wallLimitMs},counts,stages,tactical:policy?.analyze(state),selected:chosen,\n          activePlan,searchIntent,categoryBest,planCompliance:chosen?.evidence.nominal.planCompliance,\n          position:{evolution:before.serial?.evolution,round:rules.nRounds,playerIndex:rules.playerIndex},\n          riskCoverage:comparable.map(c=>({id:c.id,samples:c.risk.samples,coverage:c.risk.coverage})),\n          candidates:['stale','cancelled'].includes(status)?[]:finalists};\n        lastResult.shortlist=lastResult.candidates.map(c=>({id:c.id,kind:c.kind,targetIndex:c.targetIndex,pocketIndex:c.pocketIndex,score:c.score,samples:c.risk?.samples||0,plan:c.plan?.status}));\n        // Opt-in complete local evidence. Never expose hidden ranking to the model player.\n        if(typeof options.onAudit==='function')options.onAudit(structuredClone({\n          selected:chosen||null,ranking:comparable,accepted,\n          outcomes:[...outcomes].map(([id,result])=>({id,result})),status,counts,stages\n        }));\n        return lastResult;\n      }finally{clearDeadline();clearTimeout(wallTimer);if(!options.schedulerSession)schedule.close();active=null;}\n    }\n    return {run,preparePlan,cancel:()=>stop('cancelled'),getStatus:()=>({busy:!!active,phase:active?.phase,lastResult:lastResult&&{status:lastResult.status,elapsedMs:lastResult.elapsedMs,count:lastResult.candidates.length,counts:lastResult.counts}})};\n  }\n  return {create};\n})();\n\nconst PCOLLocalAI = (() => {\n  const failure=(code,message)=>Object.assign(new Error(message),{code});\n  const ballNames=['白球','红球','黄球','绿球','棕球','蓝球','粉球','黑球'];\n  const describeBall=b=>b&&({id:b.i,name:ballNames[b.n],points:b.n});\n  const round=value=>{\n    if(typeof value==='number')return Number.isFinite(value)?Math.round(value*1000)/1000:null;\n    if(Array.isArray(value))return value.map(round);\n    if(value&&typeof value==='object')return Object.fromEntries(Object.entries(value).map(([k,v])=>[k,round(v)]));\n    return value;\n  };\n  function create({getSearch,getTrial,getContext,onEvent=()=>{},onChange=()=>{},scheduler}) {\n    const scheduling=scheduler||(typeof PCOLComputeScheduler!=='undefined'?PCOLComputeScheduler:require('./compute-scheduler')).create();\n    let activePlan=null,active=null,state={busy:false,phase:'idle',lastDecision:null};\n    let delivery=null,failurePosition=null,failures=[];\n    // A restored table changes the round and scores, but retains its geometry and legal targets.\n    const positionKey=snapshot=>JSON.stringify([snapshot.sceneId||null,\n      ...['ballOn','playerIndex','inHand','nominatedColour','freeBallNominee','freeBallAvailable','freeBallDeclined','respottedBlack'].map(k=>snapshot.rules?.[k]??null),\n      (snapshot.balls||[]).filter(b=>b.active!==false).slice().sort((a,b)=>a.i-b.i).map(b=>[b.i,b.n,b.x,b.y,b.z,b.r])]);\n    const failureEvidence=snapshot=>failurePosition===positionKey(snapshot)?structuredClone(failures):[];\n    function rememberDelivery(snapshot,candidate,actualShot) {\n      const position=positionKey(snapshot);\n      if(position!==failurePosition){failures=[];failurePosition=position;}\n      delivery=structuredClone({shot:candidate.shot,kind:candidate.kind,targetIndex:candidate.targetIndex,\n        pocketIndex:candidate.pocketIndex,nominatedColour:candidate.nominatedColour,actualShot});\n    }\n    function recordOutcome(result) {\n      const played=delivery;delivery=null;if(!played)return;\n      if(!result.foulCode&&(result.score>0||played.kind!=='attack')){failures=[];return;}\n      const evidence={...played,result:{score:result.score,foulCode:result.foulCode,firstHits:result.firstHits||[]},count:1};\n      failures.push(evidence);if(failures.length>8)failures.shift();\n      emit('execution.feedback',{...evidence,retained:failures.length});\n    }\n    const emit=(kind,data)=>{try{onEvent(kind,round(data));}catch(_){}};\n    const update=patch=>{state={...state,...patch};try{onChange({...state});}catch(_){}};\n    const fingerprint=()=>JSON.stringify(getTrial().snapshot());\n    const compact=list=>[...list].sort((a,b)=>String(a.id).localeCompare(String(b.id))).slice(0,12).map(c=>round({id:c.id,kind:c.kind,label:c.label,targetIndex:c.targetIndex,\n      target:describeBall(getContext().balls?.find(b=>b.i===c.targetIndex)),score:c.score,features:c.features,risk:c.risk,plan:c.plan,evidence:c.evidence,outcome:c.outcome,action:c.action}));\n    const score=c=>Number.isFinite(c.score)?c.score:0;\n    function guard(job,before) {\n      if(job.cancelled)throw failure('cancelled','AI decision cancelled');\n      const activeWait=(job.schedule?.stats().waitMs||0)-(job.waitStarted||0);\n      if(job.timedOut||Date.now()-activeWait>=job.deadline||Date.now()>=job.wallDeadline)throw failure('timeout','AI decision deadline exceeded');\n      if(fingerprint()!==before)throw failure('stale','Position changed; AI decision is stale');\n    }\n    function cancellable(promise,signal) {\n      return new Promise((resolve,reject)=>{\n        const abort=()=>reject(failure('cancelled','AI decision cancelled'));\n        if(signal.aborted)return abort();signal.addEventListener('abort',abort,{once:true});\n        Promise.resolve(promise).then(resolve,reject).finally(()=>signal.removeEventListener('abort',abort));\n      });\n    }\n    async function decide(options={}) {\n      if(active)throw failure('busy','An AI decision is already running');\n      const started=Date.now(),schedule=scheduling.start({cooperativeYield:options.cooperativeYield});\n      const job={controller:new AbortController(),search:getSearch(),schedule,deadline:started+90000,wallDeadline:started+180000,cancelled:false};\n      active=job;update({busy:true,phase:'search',lastDecision:null,error:null,errorClassification:null});\n      const timeout=()=>{job.timedOut=true;job.controller.abort();job.search.cancel();schedule.cancel();};\n      const clearDeadline=schedule.setDeadline(schedule.now()+90000,timeout),wallTimer=setTimeout(timeout,180000);\n      let search;\n      try {\n        const before=fingerprint(),context=round(getContext());\n        const {plan:unusedPlan,...localOptions}=options;\n        const preparation=job.search.preparePlan\n          ?await cancellable(job.search.preparePlan(activePlan,{lastOutcome:context.lastOutcome}),job.controller.signal)\n          :{brief:{},needsReplan:true,reason:'missing-preparation'};\n        guard(job,before);\n        emit('plan.check',{needsReplan:preparation.needsReplan,reason:preparation.reason,planCompliance:preparation.planCompliance,previousPlan:activePlan});\n        const defaultPlan=preparation.brief?.defaultPlan||(preparation.brief?.defaultPrimary&&preparation.brief?.defaultFallback?{primaryIntent:preparation.brief.defaultPrimary,fallbackIntent:preparation.brief.defaultFallback}:null);\n        const continued=preparation.needsReplan===false;\n        const plan=continued?(preparation.continuedPlan||activePlan||defaultPlan):defaultPlan;\n        const source=continued?'continued-plan':'local-plan',reason=preparation.reason||'';\n        const planningElapsedMs=Date.now()-started;\n        const feedback=failureEvidence(getTrial().snapshot());\n        search=await cancellable(job.search.run({...localOptions,schedulerSession:schedule,fastPlan:continued,preparedRoot:preparation.preparedRoot,failureEvidence:feedback,\n          budgetMs:Math.max(1,Math.min(Number(options.budgetMs)||65000,65000,job.deadline-Date.now()+schedule.stats().waitMs-500)),plan}),job.controller.signal);\n        emit('search.complete',{status:search.status,elapsedMs:search.elapsedMs,totalElapsedMs:Date.now()-started,budgetMs:search.budgetMs,scheduling:search.scheduling,counts:search.counts,stages:search.stages||search.counts,position:search.position,activePlan:search.activePlan,searchIntent:search.searchIntent,planCompliance:search.planCompliance,categoryBest:search.categoryBest,candidates:compact(search.candidates||[])});\n        guard(job,before);\n        if(['stale','cancelled','needs-ruling'].includes(search.status))throw failure(search.status,'AI search '+search.status);\n        if(!search.candidates?.length)throw failure('no-candidates','No legal AI candidates available');\n        const candidate=search.selected||search.candidates[0];\n        activePlan=search.activePlan||(plan?{...plan,actor:context.playerIndex,round:search.position?.round??context.nRounds,\n          objective:search.tactical?.objective,expectedNext:candidate.expectedNext||null,lastWasDevelopment:candidate.intent?.task==='develop',\n          coverageInsufficient:search.planCompliance?.coverageInsufficient===true}:null);\n        const result={candidate,reason,source,shortlist:compact(search.candidates),activePlan,\n          search:{status:search.status,elapsedMs:search.elapsedMs,scheduling:search.scheduling,counts:search.counts,stages:search.stages,searchIntent:search.searchIntent,planCompliance:search.planCompliance,categoryBest:search.categoryBest}};\n        emit('selection.complete',{kind:'shot',id:candidate.id,source,reason,score:candidate.score,\n          elapsedMs:planningElapsedMs,totalElapsedMs:Date.now()-started});\n        update({phase:'ready',lastDecision:{candidateId:result.candidate.id,source:result.source,reason:result.reason}});return result;\n      }catch(error){\n        if(job.timedOut&&!job.cancelled)error=failure('timeout','AI decision deadline exceeded');\n        if(!search)emit('search.complete',{status:error.code||'error',elapsedMs:Date.now()-started,candidates:[],error:error.message});\n        update({phase:error.code==='cancelled'?'idle':'error',error:error.message,errorClassification:error.code||'search-failure'});\n        emit('decision.failure',{classification:error.code||'search-failure',error:error.message});throw error;\n      }finally{clearDeadline();clearTimeout(wallTimer);schedule.close();active=null;update({busy:false});}\n    }\n    async function chooseTurn({kind,choices,timeoutMs=90000,wallTimeoutMs=180000,schedulerSession}) {\n      if(active)throw failure('busy','An AI decision is already running');\n      if(!Array.isArray(choices)||!choices.length)throw failure('no-candidates','No legal turn choices available');\n      const started=Date.now(),job={controller:new AbortController(),schedule:schedulerSession,waitStarted:schedulerSession?.stats().waitMs||0,\n        deadline:started+Math.max(1,Math.min(90000,Number(timeoutMs)||90000)),wallDeadline:started+Math.max(1,Math.min(180000,Number(wallTimeoutMs)||180000)),cancelled:false};\n      activePlan=null;active=job;update({busy:true,phase:'selection',error:null,errorClassification:null,lastDecision:null});\n      try {\n        const before=fingerprint();\n        const choice=[...choices].sort((a,b)=>score(b)-score(a))[0];\n        await Promise.resolve();\n        guard(job,before);\n        const source='local',reason='Local search selected the highest-scoring legal option.';\n        emit('selection.complete',{kind,id:choice.id,source,reason,score:choice.score,localBestId:choice.id,\n          changedLocalChoice:false,elapsedMs:Date.now()-started,candidateIds:choices.map(c=>c.id)});\n        update({phase:'ready',lastDecision:{choiceId:choice.id,source,reason}});\n        return {choice,reason,source};\n      }catch(error){\n        update({phase:error.code==='cancelled'?'idle':'error',error:error.message,errorClassification:error.code||'turn-failure'});\n        emit('decision.failure',{kind,classification:error.code||'turn-failure',error:error.message});throw error;\n      }finally{active=null;update({busy:false});}\n    }\n    return {decide,chooseTurn,rememberDelivery,recordOutcome,failureEvidence,\n      resetExperience:()=>{delivery=null;failurePosition=null;failures=[];},\n      clearPlan:()=>{activePlan=null;},getPlan:()=>activePlan&&JSON.parse(JSON.stringify(activePlan)),setPlan:plan=>{activePlan=plan&&JSON.parse(JSON.stringify(plan));},cancel:()=>{\n      if(!active)return;active.cancelled=true;active.controller.abort();active.search?.cancel();active.schedule?.cancel();\n    },getStatus:()=>({...state,lastDecision:state.lastDecision&&{...state.lastDecision}})};\n  }\n  return {create};\n})();\n\n/* One persistent owner for local search, native compilation and detached physics.\n * Live controllers and rule commits never enter this worker. */\nfunction PCOLDecisionWorker() {\n  const engine=PCOLTrialWorker({listen:false}),scheduler=PCOLComputeScheduler.create();\n  let compiler,session,payload,activeId=null,turnManager=null;\n  const send=(type,data)=>self.postMessage({type,id:activeId,...data});\n  class TrialSession {\n    constructor(snapshot){this.root=snapshot;this.key=JSON.stringify(snapshot);this.results=new WeakSet();this.cancelled=false;}\n    snapshot(){return structuredClone(this.root);}\n    fingerprint(){return this.key;}\n    getStatus(){return {busy:false};}\n    cancel(){this.cancelled=true;}\n    compile(shot,balls=this.root.balls){return compiler.compile(shot,balls);}\n    run(before,shot,options={},balls=before.balls){\n      if(this.cancelled)throw Object.assign(new Error('AI decision cancelled'),{code:'cancelled'});\n      const compiled=Array.isArray(shot)||ArrayBuffer.isView(shot)\n        ?{stroke:Array.from(new Float32Array(shot))}:this.compile(shot,balls);\n      const result={...engine.simulate({snapshot:before,stroke:compiled.stroke,options}),compiled,snapshot:this.root,stale:false};\n      this.results.add(result);return result;\n    }\n    async simulate(shot,options){return this.run(this.root,shot,options);}\n    async simulateFrom(parent,shot,options){\n      if(!this.results.has(parent)||!parent.nextSnapshot||!parent.nextBalls||parent.stale)\n        throw new Error('A settled legal trial continuation is required');\n      return this.run(parent.nextSnapshot,shot,options,parent.nextBalls);\n    }\n    async simulateScenario(scenario,shot,options={}){\n      const before=structuredClone(this.root),opts={...options};\n      if(scenario.serial!=null){before.serial=structuredClone(scenario.serial);for(const ball of before.balls)delete ball.transient;}\n      if(scenario.rules!=null)before.rules=structuredClone(scenario.rules);\n      const balls=structuredClone(scenario.balls||before.balls);\n      if(scenario.balls!=null)opts.scenarioBalls=balls;\n      if(scenario.cuePosition!=null){opts.cuePosition={...scenario.cuePosition};Object.assign(balls.find(b=>b.n===0),opts.cuePosition,{active:true});}\n      else delete opts.cuePosition;\n      return this.run(before,shot,opts,balls);\n    }\n  }\n  const getState=before=>{\n    const balls=before.balls.map(b=>({i:b.i,n:b.n,r:b.r,active:b.active,x:b.x,y:b.y,z:b.z}));\n    return {...payload.state,balls,rules:before.rules,scores:before.rules.scores,\n      touching:PCOLCore.touchingStatus({balls,...before.rules}),\n      remainingPoints:PCOLCore.remainingPoints(balls,before.rules.ballOn)};\n  };\n  const search=PCOLSearch.create({getTrial:()=>session,getState,geometry:PCOLSearchGeometry,\n    policy:PCOLTacticalPolicy,brain:PCOLTacticalBrain,skill:PCOLShotSkill,development:PCOLDevelopment,scheduler,\n    continuation:PCOLContinuation.create({geometry:PCOLSearchGeometry,policy:PCOLTacticalPolicy,core:PCOLCore,development:PCOLDevelopment,skill:PCOLShotSkill})});\n  const client=PCOLLocalAI.create({getSearch:()=>search,getTrial:()=>session,getContext:()=>payload.context,scheduler,\n    onEvent:(kind,data)=>send('event',{kind,data}),onChange:state=>send('state',{state})});\n  async function runTurn(){\n    let result,error;\n    turnManager=PCOLTurnManager.create({getState:()=>getState(session.root),getPending:()=>payload.pending,getTrial:()=>session,\n      options:PCOLTurnOptions.create({geometry:PCOLSearchGeometry,core:PCOLCore}),geometry:PCOLSearchGeometry,\n      policy:PCOLTacticalPolicy,skill:PCOLShotSkill,scheduler,choose:request=>client.chooseTurn(request),\n      onEvent:(kind,data)=>send('event',{kind,data}),onChange:state=>send('turn-state',{state}),\n      commit:(choice,kind,reason,source)=>{result={choice,kind,reason,source};},onError:e=>{error=e;}});\n    await turnManager.run();\n    if(error)throw error;\n    if(!result)throw Object.assign(new Error('AI turn cancelled'),{code:'cancelled'});\n    return result;\n  }\n  self.onmessage=async({data:message})=>{\n    const {type,id}=message;\n    if(type==='control'){\n      // These commands arrive in order after real execution or a frame reset.\n      if(['clearPlan','resetExperience','recordOutcome','rememberDelivery'].includes(message.method))\n        client[message.method](...message.args);\n      return;\n    }\n    if(activeId!==null){self.postMessage({type:'error',id,error:{code:'busy',message:'An AI decision is already running'}});return;}\n    activeId=id;\n    try{\n      if(type==='init'){engine.init(message.runtime);compiler=engine.createCompiler();send('result',{result:{ready:true}});return;}\n      if(!compiler)throw new Error('Decision worker is not initialized');\n      payload=message.payload;session=new TrialSession(payload.snapshot);\n      let result;\n      if(type==='decide')result=await client.decide(payload.options||{});\n      else if(type==='turn')result=await runTurn();\n      else if(type==='search')result=await search.run({...payload.options,snapshot:session.root,state:payload.state});\n      else if(type==='trial')result=await session.simulate(payload.shot,payload.options);\n      else throw new Error('Unknown decision operation');\n      send('result',{result});\n    }catch(error){send('error',{error:{code:error.code||'worker-failure',message:error.message||String(error)}});}\n    finally{activeId=null;turnManager=null;}\n  };\n}\n\nPCOLDecisionWorker();";

/* The main-thread boundary: one immutable input per decision, stale checks at
 * completion, ordered log forwarding, and no decision-time physics on the UI thread. */
const PCOLDecisionClient=(()=>{
  const failure=(code,message)=>Object.assign(new Error(message),{code});
  function create({getTrial,getState,getContext,onEvent=()=>{},onChange=()=>{},
    workerFactory=()=>{const url=URL.createObjectURL(new Blob([PCOLDecisionWorkerSource],{type:'text/javascript'}));
      try{return new Worker(url);}finally{URL.revokeObjectURL(url);}}}) {
    let worker=null,runtime=null,ready=null,pending=null,active=null,sequence=0;
    let state={busy:false,phase:'idle',lastDecision:null},turnState={busy:false,failed:false,phase:'idle',lastResult:null};
    let turnChanged=()=>{};
    const changed=()=>onChange({...state});
    function dispose(error=failure('cancelled','AI decision cancelled')){
      worker?.terminate();worker=null;runtime=null;ready=null;
      if(pending){clearTimeout(pending.timer);const old=pending;pending=null;old.reject(error);}
    }
    function request(type,data){
      if(pending)return Promise.reject(failure('busy','An AI decision is already running'));
      return new Promise((resolve,reject)=>{
        const id=++sequence;
        pending={id,resolve,reject,timer:setTimeout(()=>dispose(failure('timeout','AI decision deadline exceeded')),190000)};
        worker.postMessage({type,id,...data});
      });
    }
    async function initialize(){
      const next=getTrial().exportRuntime();
      if(worker&&runtime===next)return ready;
      dispose();runtime=next;worker=workerFactory();
      worker.onmessage=({data})=>{
        if(data.id!==null&&data.id!==pending?.id)return;
        if(data.type==='event'){onEvent(data.kind,data.data);return;}
        if(data.type==='state'){state={...state,...data.state};changed();return;}
        if(data.type==='turn-state'){turnState={...data.state,busy:active?.type==='turn'||data.state.busy};turnChanged();return;}
        if(!pending||data.id!==pending.id)return;
        const done=pending;pending=null;clearTimeout(done.timer);
        if(data.type==='error')done.reject(failure(data.error.code,data.error.message));else done.resolve(data.result);
      };
      worker.onerror=event=>dispose(failure('worker-failure',event.message||'Local decision worker failed'));
      ready=request('init',{runtime});return ready;
    }
    const control=(method,...args)=>worker?.postMessage({type:'control',method,args});
    async function run(type,options={},extra={}){
      if(active)throw failure('busy','An AI decision is already running');
      const trial=getTrial(),snapshot=extra.snapshot||trial.snapshot();
      const fingerprint=trial.fingerprint?.()||JSON.stringify(trial.snapshot());
      const job={type,cancelled:false};active=job;
      if(type!=='turn'){state={...state,busy:true,phase:'search',error:null,errorClassification:null};changed();}
      try{
        await initialize();
        if(job.cancelled)throw failure('cancelled','AI decision cancelled');
        const result=await request(type,{payload:{snapshot,state:extra.state||getState(snapshot),context:getContext(),options,...extra}});
        if(job.cancelled)throw failure('cancelled','AI decision cancelled');
        let current;try{current=trial.fingerprint?.()||JSON.stringify(trial.snapshot());}catch(_){}
        if(current!==fingerprint)throw failure('stale','Position changed; AI decision is stale');
        return result;
      }catch(error){
        if(!job.cancelled){state={...state,phase:error.code==='cancelled'?'idle':'error',error:error.message,errorClassification:error.code};
          onEvent('decision.transport',{operation:type,classification:error.code||'worker-failure',error:error.message});}
        throw error;
      }finally{if(active===job){active=null;state={...state,busy:false};changed();}}
    }
    function cancel(){
      if(!active)return;
      active.cancelled=true;dispose();active=null;state={...state,busy:false,phase:'idle'};changed();
    }
    function createTurnManager({getPending,commit,onError,onChange=()=>{}}){
      let epoch=0;turnChanged=()=>onChange({...turnState});
      return {async run(){
        if(turnState.busy||turnState.failed)return;
        const mark=epoch;turnState={...turnState,busy:true,phase:'turn-search'};turnChanged();
        try{const result=await run('turn',{}, {pending:getPending()});
          if(mark!==epoch)return;
          turnState.lastResult={kind:result.kind,choiceId:result.choice.id,reason:result.reason};
          commit(result.choice,result.kind,result.reason,result.source);
        }catch(error){if(mark===epoch){turnState.failed=true;onError(error);}}
        finally{if(mark===epoch){turnState.busy=false;turnState.phase='idle';turnChanged();}}
      },cancel(){epoch++;if(active?.type==='turn')cancel();turnState={busy:false,failed:false,phase:'idle',lastResult:null};turnChanged();},isBusy:()=>turnState.busy,getStatus:()=>({...turnState})};
    }
    return {decide:options=>run('decide',options),createTurnManager,
      runSearch:(snapshot,state,options={})=>run('search',options,{snapshot,state}),
      simulate:(snapshot,state,shot,options={})=>run('trial',options,{snapshot,state,shot}),
      rememberDelivery:(...args)=>control('rememberDelivery',...args),recordOutcome:result=>control('recordOutcome',result),
      clearPlan:()=>control('clearPlan'),resetExperience:()=>control('resetExperience'),cancel,
      dispose(){cancel();dispose();},isBusy:()=>!!active,getStatus:()=>({...state,worker:!!worker,execution:'worker'})};
  }
  return {create};
})();

/* Bounded, passive frame-gap diagnostics. The host supplies its existing tick;
 * no additional animation loop, performance marks, screenshots or disk writes. */
const PCOLFrameMonitor = (() => {
  const THRESHOLD_MS=50,PAUSE_MS=2000,SAMPLE_LIMIT=32,PHASE_LIMIT=12,LOAF_LIMIT=8;
  const PHASES=['idle','ai','turn','realshot'];
  const phaseName=value=>PHASES.includes(value?.phase||value)?value?.phase||value:'idle';
  const finite=value=>Number.isFinite(value)?value:null;
  const text=(value,length=120)=>typeof value==='string'?value.slice(0,length):'';
  function create({window:win=globalThis.window,getPhase,onReport=()=>{}}={}) {
    const doc=win?.document,now=()=>win?.performance?.now?.()??Date.now();
    let disposed=false,last=null,phase='idle',lastPhase='idle',observer=null,supported=false,visibleSince=now();
    let frames,slowFrames,totalGapMs,maxGapMs,dropped,pauses,maxPauseMs,phaseCounts,samples,loafCount,loafDropped,loafs;
    let phases=[];
    function clear() {
      frames=slowFrames=totalGapMs=maxGapMs=dropped=pauses=maxPauseMs=loafCount=loafDropped=0;
      phaseCounts={idle:0,ai:0,turn:0,realshot:0};samples=[];loafs=[];
    }
    function setPhase(value,time=now()) {
      if(disposed)return;
      const next=phaseName(value);
      if(next===phase&&phases.length)return;
      phase=next;phases.push({at:time,phase});
      if(phases.length>PHASE_LIMIT)phases.shift();
    }
    function updatePhase(time) {
      if(typeof getPhase==='function')try{setPhase(getPhase(),time);}catch(_){}
    }
    function resetBaseline() {
      last=null;visibleSince=now();phases=[];setPhase(phase,visibleSince);
    }
    function visibilityChanged() {
      if(doc?.hidden)pauses++;
      resetBaseline();
    }
    function tick(time=now()) {
      if(disposed||!Number.isFinite(time))return;
      updatePhase(time);
      if(doc?.hidden){last=null;return;}
      if(last===null){last=time;lastPhase=phase;return;}
      const start=last,gap=time-start,previousPhase=lastPhase;
      last=time;lastPhase=phase;
      if(gap<=0)return;
      if(gap>PAUSE_MS){pauses++;maxPauseMs=Math.max(maxPauseMs,gap);visibleSince=time;phases=[];setPhase(phase,time);return;}
      frames++;totalGapMs+=gap;maxGapMs=Math.max(maxGapMs,gap);
      if(gap<THRESHOLD_MS)return;
      slowFrames++;phaseCounts[previousPhase]++;
      const sample={at:start,gapMs:gap,phase:previousPhase,phaseAtResume:phase,
        recentPhases:phases.filter(item=>item.at>=start&&item.at<=time).slice(-4)};
      if(samples.length===SAMPLE_LIMIT){samples.shift();dropped++;}
      samples.push(sample);
    }
    function collect(entries) {
      if(disposed||doc?.hidden)return;
      for(const entry of entries) {
        if(!Number.isFinite(entry.startTime)||!Number.isFinite(entry.duration)||entry.duration<THRESHOLD_MS||entry.startTime<visibleSince)continue;
        loafCount++;
        const recent=phases.filter(item=>item.at<=entry.startTime+entry.duration).slice(-4);
        const row={at:entry.startTime,durationMs:entry.duration,blockingDurationMs:finite(entry.blockingDuration),recentPhases:recent,
          scripts:(entry.scripts||[]).slice(0,3).map(script=>({
            durationMs:finite(script.duration),forcedStyleAndLayoutDurationMs:finite(script.forcedStyleAndLayoutDuration),
            sourceURL:text(script.sourceURL,200).split(/[?#]/)[0],sourceFunctionName:text(script.sourceFunctionName),invoker:text(script.invoker)
          }))};
        if(loafs.length===LOAF_LIMIT){loafs.shift();loafDropped++;}
        loafs.push(row);
      }
    }
    function drain(reason='stroke') {
      if(disposed)return null;
      if(observer)try{collect(observer.takeRecords());}catch(_){}
      if(!frames&&!pauses&&!loafCount)return null;
      const report={reason:text(reason,40),thresholdMs:THRESHOLD_MS,pauseThresholdMs:PAUSE_MS,
        frames,slowFrames,meanGapMs:frames?totalGapMs/frames:0,maxGapMs,phaseCounts,samples,dropped,pauses,maxPauseMs,
        longAnimationFrames:{supported,scope:'document-main-thread-only',count:loafCount,samples:loafs,dropped:loafDropped}};
      clear();resetBaseline();
      try{onReport(report);}catch(_){}
      return report;
    }
    function dispose() {
      if(disposed)return;
      disposed=true;observer?.disconnect();doc?.removeEventListener?.('visibilitychange',visibilityChanged);
      last=null;phases=[];clear();
    }
    clear();updatePhase(visibleSince);setPhase(phase,visibleSince);
    doc?.addEventListener?.('visibilitychange',visibilityChanged);
    // LoAF describes observable document main-thread work only. Absence of a
    // script entry cannot rule out workers or an isolated userscript world.
    const Observer=win?.PerformanceObserver;
    if(Observer?.supportedEntryTypes?.includes('long-animation-frame'))try{
      observer=new Observer(list=>collect(list.getEntries()));
      observer.observe({type:'long-animation-frame',buffered:false});supported=true;
    }catch(_){observer?.disconnect();observer=null;}
    return {tick,setPhase,drain,dispose};
  }
  return {create};
})();

const PCOLLocalOpponent = (() => {
  function create({game,decide,getSnapshot,canThink,canDeliver = canThink,cancelDecision = () => {},onError = () => {},onChange = () => {},
    prepareCandidate = candidate => candidate,nominate = () => {}}) {
    let enabled = false, epoch = 0, pending = null, choice = null, expected = null, delivery = null;
    let phase = 'idle', error = null, reason = '';
    const fingerprint = () => JSON.stringify(getSnapshot());
    const getStatus = () => ({enabled,busy:!!pending,phase,error,reason});
    const changed = () => { try { onChange(getStatus()); } catch (_) {} };
    // Keep unexpected exception details out of the opponent status.
    function messageOf(error,fallback) {
      const message=error?.message;
      const known={stale:'Position changed; AI decision is stale',cancelled:'AI decision cancelled',
        'no-candidates':'No legal AI candidates available','needs-ruling':'Resolve the pending ruling before using AI',timeout:'AI decision deadline exceeded'};
      if(known[error?.code])return known[error.code];
      return typeof message==='string' && /^(AI opponent (position changed|stroke verification failed)|Unsupported AI shot|An AI decision is already running)$/.test(message) ? message : fallback;
    }
    function fail(message) {
      choice = null; expected = null; delivery = null; phase = 'error'; error = message; changed();
      try { onError(new Error(message)); } catch (_) {}
    }
    function reset() {
      epoch++; pending = null; choice = null; expected = null; delivery = null;
      phase = 'idle'; error = null; reason = '';
      cancelDecision(); changed();
    }
    function route(candidate) {
      const shot = candidate?.shot, vertical = shot?.vertical || 0;
      const elevation = vertical < 0 ? .025 * Math.PI : 0;
      if (!shot || !Number.isFinite(shot.direction?.x) || !Number.isFinite(shot.direction?.z) ||
          !Number.isFinite(shot.power) || !Number.isFinite(vertical) ||
          !Number.isFinite(shot.side||0) || Math.abs(shot.side||0)>1 || Math.abs((shot.elevation || 0) - elevation) > 1e-9 ||
          !Array.isArray(candidate.stroke) || candidate.stroke.length !== 8 || !candidate.stroke.every(Number.isFinite)) {
        throw new Error('Unsupported AI shot');
      }
      return {dx:shot.direction.x,dz:shot.direction.z,powerFactor:shot.power - .3,
        fbSpin:vertical,ballBIndex:candidate.targetIndex};
    }
    function step(ai,original,args) {
      if (!enabled) return original.apply(ai,args);
      if (phase === 'error' || phase === 'delivered') return null;
      if (choice) {
        if (!canDeliver()) return null;
        try {
          if (fingerprint() !== choice.fingerprint) throw new Error('AI opponent position changed');
          // Exactly one execution sample, drawn only after the stale check.
          // Never simulate/retry this draw to select a more favourable error.
          const prepared = prepareCandidate(choice.candidate);
          const routeResult = route(prepared);
          delivery={shot:prepared.shot,stroke:prepared.stroke.slice()};
          expected = prepared.stroke.slice();
          nominate(prepared);
          choice = null; phase = 'delivered'; ai._currentTaskIndex = -1; changed();
          return routeResult;
        } catch (error) { fail(messageOf(error,'AI opponent shot preparation failed')); return null; }
      }
      if (pending || !canThink()) return null;
      const job = {epoch,fingerprint:fingerprint()};
      pending = job; phase = 'thinking'; changed();
      Promise.resolve().then(() => {
        if (job.epoch !== epoch) return null;
        return decide();
      }).then(result => {
        if (job.epoch !== epoch) return;
        if (fingerprint() !== job.fingerprint) throw new Error('AI opponent position changed');
        route(result?.candidate);
        choice = {candidate:result.candidate,fingerprint:job.fingerprint};
        reason = typeof result.reason === 'string' ? result.reason : '';
        phase = 'ready';
      }).catch(error => {
        if (job.epoch === epoch) fail(messageOf(error,'AI opponent decision failed'));
      }).finally(() => {
        if (pending === job) { pending = null; changed(); }
      });
      return null;
    }
    function verifyStroke(controller) {
      if (!enabled) return true;
      let actual;
      try { actual = controller.getStrokeVars(); } catch (_) {}
      if (!expected || !actual || actual.length !== 8 ||
          expected.some((value,index) => !Number.isFinite(actual[index]) || Math.abs(value - actual[index]) > 1e-6)) {
        fail('AI opponent stroke verification failed'); return false;
      }
      expected = null; return true;
    }
    return {setEnabled(value) { enabled = !!value; reset(); },reset,step,verifyStroke,getStatus,
      getDelivery:()=>enabled&&phase==='delivered'?delivery:null};
  }
  return {create};
})();

const PCOLMatchRecorder = (() => {
  const ERROR_CODES=new Set(['log_limit','invalid_event','record_failed','recording_disabled','body_too_large','forbidden']);
  function localFetch(url,options) {
    if (typeof GM_xmlhttpRequest !== 'function') return fetch(url,options);
    return new Promise((resolve,reject)=>GM_xmlhttpRequest({url,method:'POST',headers:options.headers,data:options.body,anonymous:true,timeout:5000,
      onload:r=>resolve({ok:r.status>=200&&r.status<300,json:async()=>JSON.parse(r.responseText)}),onerror:()=>reject(new Error('unavailable')),ontimeout:()=>reject(new Error('timeout'))}));
  }
  function createStore({name='pcol-match-recordings',indexedDBImpl=globalThis.indexedDB}={}) {
    let opening=null;
    function database() {
      if(opening)return opening;
      opening=new Promise((resolve,reject)=>{
        if(!indexedDBImpl)return reject(new Error('storage_unavailable'));
        const request=indexedDBImpl.open(name,1);
        request.onupgradeneeded=()=>{
          const events=request.result.createObjectStore('events',{keyPath:'key',autoIncrement:true});
          events.createIndex('id','id',{unique:true});events.createIndex('synced','synced');
        };
        request.onsuccess=()=>resolve(request.result);
        request.onerror=()=>reject(request.error||new Error('storage_unavailable'));
      }).catch(error=>{opening=null;throw error;});
      return opening;
    }
    async function transaction(mode,work) {
      const db=await database();
      return new Promise((resolve,reject)=>{
        const tx=db.transaction('events',mode,mode==='readwrite'?{durability:'strict'}:undefined);let result;
        tx.oncomplete=()=>resolve(result);
        tx.onerror=tx.onabort=()=>reject(tx.error||new Error('storage_failed'));
        work(tx.objectStore('events'),value=>{result=value;});
      });
    }
    return {
      append:batch=>transaction('readwrite',events=>{for(const {id,raw} of batch)events.add({id,raw,synced:0});}),
      stats:()=>transaction('readonly',(events,done)=>{let saved,pending;const total=events.count(),waiting=events.index('synced').count(0);
        total.onsuccess=()=>{saved=total.result;if(pending!==undefined)done({saved,pending});};
        waiting.onsuccess=()=>{pending=waiting.result;if(saved!==undefined)done({saved,pending});};}),
      pending:limit=>transaction('readonly',(events,done)=>{const rows=[],request=events.index('synced').openCursor(0);request.onsuccess=()=>{
        const cursor=request.result;if(!cursor||rows.length>=limit)return done(rows);rows.push(cursor.value);cursor.continue();};}),
      acknowledge:keys=>transaction('readwrite',(events)=>{for(const key of Array.isArray(keys)?keys:[keys]){
        const request=events.get(key);request.onsuccess=()=>{if(request.result)events.put({...request.result,synced:1});};}}),
      readPage:({after=0,limit=200}={})=>transaction('readonly',(events,done)=>{
        const rows=[],size=Math.max(1,Math.min(500,Number(limit)||200)),request=events.openCursor(IDBKeyRange.lowerBound(Number(after)||0,true));
        request.onsuccess=()=>{const cursor=request.result;
          if(!cursor||rows.length>size){const page=rows.slice(0,size);return done({events:page.map(row=>JSON.parse(row.raw)),jsonl:page.map(row=>row.raw+'\n').join(''),nextCursor:page.at(-1)?.key||Number(after)||0,done:rows.length<=size});}
          rows.push(cursor.value);cursor.continue();};
      })
    };
  }
  function create({version='',source='browser',onChange=()=>{},isBusy=()=>false,fetchImpl=localFetch,store=createStore()}={}) {
    let enabled=true,frameId=null,sequence=0,lastStroke=null,disposed=false,writing=null,syncing=null,error=null,syncError=null,saved=0,pending=0,failed=0;
    let queuedBytes=0,retryTimer=null,retryAt=0,retryDelay=5000,notifyTimer=null,lastNotice=null,lastNoticeAt=0;
    const SYNC_BATCH=8,SYNC_INTERVAL=1500,NOTICE_INTERVAL=250;
    const writes=[],session=Date.now().toString(36)+'_'+Math.random().toString(36).slice(2,10);
    const getStatus=()=>({enabled,frameId,session,saved,localSaved:saved,pending,saving:writes.length,failed,error,syncError,status:error?'error':writes.length?'saving':'saved'});
    function sendNotice() {
      notifyTimer=null;if(disposed)return;
      const status=getStatus();
      if(lastNotice&&Object.keys(status).every(key=>status[key]===lastNotice[key]))return;
      lastNotice=status;lastNoticeAt=Date.now();try {onChange(status);}catch(_) {}
    }
    function notify(immediate=false) {
      if(disposed)return;
      if(immediate||!lastNotice||error!==lastNotice.error||syncError!==lastNotice.syncError||enabled!==lastNotice.enabled){
        if(notifyTimer)clearTimeout(notifyTimer);sendNotice();return;
      }
      if(!notifyTimer){notifyTimer=setTimeout(sendNotice,Math.max(0,NOTICE_INTERVAL-(Date.now()-lastNoticeAt)));notifyTimer.unref?.();}
    }
    const entryFor=(kind,data,correlation={})=>({schema:1,id:session+'_'+(++sequence),session,seq:sequence,source,frameId,at:new Date().toISOString(),kind,data,
      ...Object.fromEntries(['turnId','decisionId','requestId','strokeId'].filter(key=>correlation[key]!=null).map(key=>[key,String(correlation[key])]))});
    const ready=store.stats().then(stats=>{saved=stats.saved;pending=stats.pending;notify();scheduleSync();return getStatus();},()=>{error='storage_unavailable';notify();return getStatus();});
    function scheduleSync() {
      if(disposed||!enabled||!pending||retryTimer||syncing)return;
      retryTimer=setTimeout(()=>{retryTimer=null;if(isBusy()){scheduleSync();return;}void sync(false);},Math.max(SYNC_INTERVAL,retryAt-Date.now()));
      retryTimer.unref?.();
    }
    function persist() {
      if(writing)return writing;
      writing=(async()=>{
        await ready;
        while(writes.length){
          const batch=writes.slice(0,40);
          try{await store.append(batch);writes.splice(0,batch.length);queuedBytes-=batch.reduce((n,row)=>n+row.raw.length,0);saved+=batch.length;pending+=batch.length;error=failed?'record_failed':null;notify();scheduleSync();}
          catch(_){error='storage_failed';notify();break;}
        }
        return getStatus();
      })().finally(()=>{writing=null;});
      return writing;
    }
    function sync(force=false) {
      if(syncing||disposed||(!force&&(!enabled||isBusy()||Date.now()<retryAt)))return syncing||Promise.resolve(getStatus());
      if(retryTimer){clearTimeout(retryTimer);retryTimer=null;}
      syncing=(async()=>{
        await ready;
        try{
          while(!disposed){
            const batch=await store.pending(SYNC_BATCH);if(!batch.length)break;
            const accepted=[];
            try{
              for(const row of batch){
                if(disposed||(!force&&(!enabled||isBusy())))break;
                const response=await fetchImpl('http://127.0.0.1:18763/record',{method:'POST',headers:{'Content-Type':'application/json','X-PCOL-Client':'pcol-snooker'},body:row.raw});
                if(!response.ok){let code='record_failed';try{const body=await response.json();if(ERROR_CODES.has(body.error))code=body.error;}catch(_){}throw new Error(code);}
                accepted.push(row.key);
              }
            }finally{
              // A failed upload leaves only its unsent suffix pending. A failed acknowledgement
              // safely retries uploaded IDs; the recording server deduplicates those IDs.
              if(accepted.length){await store.acknowledge(accepted);pending=Math.max(0,pending-accepted.length);syncError=null;retryAt=0;retryDelay=5000;}
            }
            if(!force)break;
          }
          const stats=await store.stats();saved=stats.saved;pending=stats.pending;
        }catch(failure){syncError=ERROR_CODES.has(failure.message)?failure.message:failure.message==='timeout'?'timeout':'unavailable';retryAt=Date.now()+retryDelay;retryDelay=Math.min(60000,retryDelay*2);}
        notify();return getStatus();
      })().finally(()=>{syncing=null;scheduleSync();});
      return syncing;
    }
    function event(kind,data={},correlation={}) {
      if(!enabled||!frameId||disposed)return null;
      const entry=entryFor(kind,data,correlation),compact=['decision.start','stroke.end'].includes(kind);
      let raw;try{raw=JSON.stringify(entry,compact?(key,value)=>key==='serial'?undefined:value:undefined);}catch(_){failed++;error='serialization';notify();return null;}
      // Bound only writes not yet committed, never the durable event history.
      if(writes.length>=4096||queuedBytes+raw.length>8*1024*1024){failed++;error='storage_busy';notify();return null;}
      writes.push({id:entry.id,raw});queuedBytes+=raw.length;if(kind==='stroke.end')lastStroke=entry.id;
      notify();if(!['storage_failed','storage_unavailable'].includes(error)||writing)void persist();return entry.id;
    }
    async function readPage(options){await persist();return store.readPage(options);}
    async function exportJSONL() {
      const parts=[];let after=0;
      while(true){const page=await readPage({after,limit:500});parts.push(page.jsonl);if(page.done)break;after=page.nextCursor;}
      return new Blob(parts,{type:'application/x-ndjson;charset=utf-8'});
    }
    async function download() {
      const blob=await exportJSONL(),url=URL.createObjectURL(blob),link=document.createElement('a');
      link.href=url;link.download='pcol-matches-'+new Date().toISOString().slice(0,10)+'.jsonl';link.click();setTimeout(()=>URL.revokeObjectURL(url),1000);
      return {saved,bytes:blob.size};
    }
    return {startFrame(meta={}){frameId=session+'_'+(++sequence);lastStroke=null;event('frame.start',{version,...meta});return frameId;},
      event,endFrame(summary={}){return event('frame.end',summary);},mark(label,extra={}){return event('mark',{label,strokeId:lastStroke,...extra},{strokeId:lastStroke});},
      context:()=>({frameId,session,enabled}),setEnabled(value){enabled=!!value;notify(true);if(!enabled&&retryTimer){clearTimeout(retryTimer);retryTimer=null;}else scheduleSync();},getStatus,ready,readPage,exportJSONL,download,
      async flush(){await persist();if(syncing)await syncing;return sync(true);},
      dispose(){disposed=true;if(retryTimer){clearTimeout(retryTimer);retryTimer=null;}if(notifyTimer){clearTimeout(notifyTimer);notifyTimer=null;}return persist();}};
  }
  return {create,createStore};
})();

/* Developer-only, bounded decisions from saved settled positions. Never executes live shots. */
const PCOLBench = (() => {
  function create({capture,getTrial,makeSearch,getState,skill,version}) {
    const randomFor=seed=>{let n=seed>>>0;return()=>{n=(Math.imul(n,1664525)+1013904223)>>>0;return (n+.5)/4294967296;};};
    async function decide(position,options={}) {
      const trial=getTrial().createSession(position.snapshot),search=makeSearch(trial);
      try{
        const state=position.state||getState(position.snapshot);
        return await search.run({...options,trial,snapshot:position.snapshot,state});
      }
      finally{trial.dispose();}
    }
    async function visit(position,options={}) {
      const started=performance.now(),deadline=started+Math.min(90000,options.budgetMs||30000);
      const random=randomFor(options.seed??1),actor=position.snapshot.rules.playerIndex,shots=[];
      let current=structuredClone(position),reason='shot-limit',activePlan=options.activePlan||null,lastOutcome=options.lastOutcome;
      for(let i=0;i<Math.min(12,options.maxShots||6);i++) {
        const remaining=deadline-performance.now();if(remaining<250){reason='budget';break;}
        const found=await decide(current,{...options,activePlan,lastOutcome,budgetMs:remaining,maxResults:4});
        const candidate=found.selected||found.candidates[0];if(!candidate){reason=found.status;break;}
        activePlan=found.activePlan;
        const trial=getTrial().createSession(current.snapshot);
        let result;
        try {
          const left=deadline-performance.now();if(left<1){reason='budget';break;}
          const shot=skill.perturb(candidate.shot,candidate.skill,random);
          result=await trial.simulate(shot,{nominatedColour:candidate.nominatedColour,maxWallMs:Math.min(5000,left)});
        } finally {trial.dispose();}
        lastOutcome={actor,score:result.adjudication?.score,foulCode:result.adjudication?.foulCode};
        shots.push({targetIndex:candidate.targetIndex,kind:candidate.kind,searchMs:found.elapsedMs,source:'local',
          activePlan,searchIntent:found.searchIntent,
          score:result.adjudication?.score,foulCode:result.adjudication?.foulCode,status:result.status,
          cue:result.nextBalls?.find(b=>b.n===0)});
        if(result.status!=='complete'||!result.nextSnapshot){reason='ruling-or-incomplete';break;}
        if(!result.adjudication.continueBreak){reason='turn-ended';break;}
        if(!result.nextSnapshot.rules.ballOn){reason='frame-ended';break;}
        current={snapshot:result.nextSnapshot,state:{...getState(result.nextSnapshot),skill:position.state?.skill||'strong',style:position.state?.style||'balanced'}};
      }
      return {version,actor,seed:options.seed??1,shots,reason,elapsedMs:performance.now()-started,
        points:shots.reduce((n,s)=>n+Math.max(0,s.score||0),0)};
    }
    return {capture,decide,visit};
  }
  return {create};
})();

/* Development-only frame runner. All strokes use detached original physics. */
const PCOLArena = (() => {
  const copy=value=>structuredClone(value);
  const autoRefereePolicy='arena-experimental-v1';
  function create({capture,getTrial,makeSearch,getState,skill,core,geometry,policy,turnOptions,
    version,build,createRecorder,createClient,createTurnManager}) {
    let job=null,last={busy:false,phase:'idle'},recorder=null,series=null;
    const status=()=>({...last,recording:recorder?.getStatus?.(),series:series&&copy(series)});
    const randomFor=seed=>{let n=seed>>>0;const random=()=>{n=(Math.imul(n,1664525)+1013904223)>>>0;return (n+.5)/4294967296;};random.state=()=>n;return random;};
    function cancel(){if(series?.busy)series.cancelled=true;if(!job)return;job.cancelled=true;job.manager?.cancel();job.search?.cancel();job.trial?.cancel();for(const client of job.clients)client.cancel();}
    async function run({players=[{engine:'local'},{engine:'local'}],maxShots=160,seed=1,budgetMs=30000,resumeFrom=null,seriesContext=null}={}) {
      if(job)throw new Error('Arena is already running');
      if(series?.busy&&!seriesContext)throw new Error('Arena series is already running');
      if(!Array.isArray(players)||players.length!==2||players.some(p=>p.engine!=='local'))throw new Error('Arena requires two local AI participants');
      // Preserve the same execution settings for both seats.
      if((players[0].skill||'strong')!==(players[1].skill||'strong'))throw new Error('Arena requires matching skill');
      const participants=players.map((p,seat)=>({...p,seat,provider:'local',skill:p.skill||'strong',style:'unified'}));
      const current=job={cancelled:false,clients:[],snapshot:null,pending:copy(resumeFrom?.pending||null),shots:0,lastOutcome:copy(resumeFrom?.lastOutcome||null)};
      const random=randomFor(resumeFrom?.randomState??seed),limit=Math.max(1,Math.min(1000,Math.floor(Number(maxShots)||160)));
      const sharedBudget=Math.max(100,Math.min(65000,Number(budgetMs)||30000));
      let seat=0,decisionId=null,decisionSequence=0,turnId=null,strokeId=null,winner=null,reason=null;
      const emit=(kind,data={})=>recorder.event(kind,{mode:'arena',execution:'isolated-original-physics',seat,provider:participants[seat]?.provider,...data},{decisionId,turnId,strokeId,requestId:data.requestId});
      const state=()=>({...getState(current.snapshot),skill:participants[seat].skill,opponentSkill:participants[1-seat].skill,style:'unified'});
      const checkpoint=basis=>{
        const resume={snapshot:copy(current.snapshot),pending:copy(current.pending),randomState:random.state(),lastOutcome:copy(current.lastOutcome),
          activePlans:current.clients.map(client=>client.getPlan?.()||null),
          shots:(resumeFrom?.shots||0)+current.shots,frameId:recorder.getStatus?.().frameId,reviewFoul:Boolean(current.pending),autoRefereePolicy};
        last={...last,resume};emit('arena.checkpoint',{basis,...resume});return resume;
      };
      function finishEarly() {
        const r=current.snapshot.rules,previous=current.lastOutcome;
        if(current.pending||r.freeBallReview)return false;
        const continuing=previous?.actor===r.playerIndex&&previous?.score>0&&!previous?.foulCode&&previous?.continueBreak!==false;
        const outcome=core.earlyFrameOutcome({balls:current.snapshot.balls,ballOn:r.ballOn,scores:r.scores,playerIndex:r.playerIndex,
          actor:previous?.actor,continueBreak:continuing,freeBall:!!r.freeBallAvailable&&!r.freeBallDeclined,freeBallReview:!!r.freeBallReview});
        if(!outcome)return false;
        winner=outcome.winner;reason='custom-'+outcome.reason;emit('ruling.early-frame',outcome);return true;
      }
      function bindTrial() {
        current.search?.cancel();current.trial?.dispose();
        const raw=getTrial().createSession(current.snapshot);
        // Foul snapshots have no worker serial export. Scenario hydration resets
        // every ball from settled nextBalls without touching the live simulator.
        current.trial={...raw,simulate:(shot,options={})=>raw.simulateScenario({balls:current.snapshot.balls,rules:current.snapshot.rules},shot,options)};
        const search=makeSearch(current.trial);
        current.search={...search,run:options=>search.run({...options,snapshot:current.snapshot,state:state(),budgetMs:Math.min(options.budgetMs??sharedBudget,sharedBudget)})};
      }
      function installState(next,serial=null) {
        const previous=current.snapshot;
        current.snapshot={...previous,serial:serial||previous.serial,rules:copy(next.rules),balls:previous.balls.map(source=>{
          const ball=next.balls.find(b=>b.i===source.i);if(!ball)throw new Error('Arena ball state missing');
          const merged={...source,...copy(ball)};delete merged.transient;return merged;
        })};
      }
      function freeBallAssessment() {
        const s=state(),r=current.snapshot.rules;
        let test=core.isSnookered(s.balls,r.ballOn,undefined,{inHand:r.inHand>0});
        if(r.inHand>0)for(const position of turnOptions.placements(s)) {
          const witness=core.isSnookered(s.balls,r.ballOn,{...position,r:s.balls.find(b=>b.n===0)?.r});
          if(witness.snookered===false){test=witness;break;}
        }
        const uncertain=test.snookered==null;
        r.freeBallAvailable=test.snookered===true;r.freeBallReview=uncertain;
        emit('ruling.free-ball',{assessment:test,available:r.freeBallAvailable,uncertain,experimental:uncertain,
          basis:uncertain?'unknown-assessment-needs-review':'geometric-assessment'});
      }
      try {
        const captured=resumeFrom?.snapshot||await capture();current.snapshot=copy(captured.snapshot||captured);
        seat=current.snapshot.rules.playerIndex;
        if(!current.snapshot.rules?.ballOn||current.snapshot.rules.ballOn===65535||current.snapshot.rules.scores?.length!==2)throw new Error('Arena requires a settled two-player snooker frame');
        recorder=createRecorder({version,source:'arena',mode:'arena'});
        recorder.startFrame({version,build,source:'arena',mode:'arena',execution:'isolated-original-physics',autoRefereePolicy,
          participants,seed,maxShots:limit,budgetMs:sharedBudget,position:copy(current.snapshot),
          ...(resumeFrom?.frameId?{resumedFrom:resumeFrom.frameId,previousShots:resumeFrom.shots,decisionHistoryReset:true}:{}),series:seriesContext});
        if(resumeFrom?.ruling)emit('ruling.resume',copy(resumeFrom.ruling));
        if(resumeFrom?.reviewFoul||current.snapshot.rules.freeBallReview){freeBallAssessment();checkpoint('resume-foul-review');}
        current.clients=participants.map((settings,actor)=>createClient({getSearch:()=>current.search,getTrial:()=>current.trial,
          getContext:()=>{const s=state(),r=current.snapshot.rules;return {...r,style:s.style,balls:s.balls,remainingPoints:s.remainingPoints,lastOutcome:current.lastOutcome,freeBall:{available:r.freeBallAvailable,nominee:r.freeBallNominee}};},
          onEvent:(kind,data)=>emit(kind,{...data,seat:actor,provider:settings.provider})}));
        current.clients.forEach((client,i)=>client.setPlan?.(resumeFrom?.activePlans?.[i]||null));
        for(;current.shots<limit&&!current.cancelled;) {
          seat=current.snapshot.rules.playerIndex;
          last={busy:true,phase:'decision',shots:current.shots,seat,scores:[...current.snapshot.rules.scores],participants,resume:last.resume};
          const r=current.snapshot.rules,s=state();
          if(r.freeBallReview){reason='free-ball-needs-ruling';break;}
          if(finishEarly())break;
          turnId='arena-turn-'+r.nRounds+'-'+seat;decisionId=turnId+'-'+(++decisionSequence);strokeId=null;
          emit('decision.start',{engine:'local',position:copy(current.snapshot),
            randomState:random.state(),pending:copy(current.pending),lastOutcome:current.lastOutcome});
          bindTrial();let prepared=null,committed=false,turnError=null;
          const needs=current.pending||r.inHand>0||(r.freeBallAvailable&&r.freeBallNominee==null&&!r.freeBallDeclined)||s.touching?.requiresColourDeclaration;
          if(needs) {
            current.manager=createTurnManager({getState:state,getPending:()=>current.pending,getTrial:()=>current.trial,options:turnOptions,geometry,policy,skill,
              choose:request=>current.clients[seat].chooseTurn(request),onEvent:emit,onError:error=>{turnError=error;},
              commit:(choice,kind,why,source)=>{
                emit('turn.choice',{kind,choiceId:choice.id,action:choice.action,position:choice.position,nominee:choice.nominee,reason:why,source});
                if(kind==='foul') {
                  installState(choice.state,choice.action==='restore'?current.pending.before.serial:null);
                  current.pending=null;committed=true;checkpoint('foul-choice');return;
                }
                installState(choice.state);current.snapshot.rules.inHand=0;
                if(choice.candidate?.nominatedColour)Object.assign(current.snapshot.rules,{nominatedColour:choice.candidate.nominatedColour,nominationSource:'manual'});
                prepared=choice.candidate?{candidate:choice.candidate,reason:why,source}:null;committed=true;
              }});
            await current.manager.run();if(turnError)throw turnError;if(current.cancelled)break;
            if(!committed)throw new Error('Arena turn decision did not commit');
            // Foul choice changes actor; the next loop handles that actor's shot.
            if(!prepared&&needs&&typeof needs==='object')continue;
            bindTrial();
          }
          if(finishEarly())break;
          const decision=prepared||await current.clients[seat].decide({budgetMs:sharedBudget});
          if(current.cancelled)break;
          const concession=policy?.concession?.({...state(),pending:current.pending},decision,geometry);
          if(concession?.action==='concede'){winner=1-seat;reason='concession';emit('concession.check',{...concession,playerIndex:seat,source:'local-policy'});break;}
          const candidate=decision.candidate,before=copy(current.snapshot),actual=skill.perturb(candidate.shot,candidate.skill,random);
          strokeId=decisionId+'-stroke';emit('stroke.start',{actor:seat,candidateId:candidate.id,nominalShot:candidate.shot,actualShot:actual,reason:decision.reason});
          last={...last,phase:'physics'};
          const result=await current.trial.simulate(actual,{nominatedColour:candidate.nominatedColour,maxSteps:100000,maxWallMs:60000});
          const afterState=result.nextBalls&&{...s,balls:result.nextBalls,rules:{...r,...result.nextContext,ballOn:result.adjudication?.nextBallOn}};
          const planCompliance=afterState&&candidate.expectedNext?PCOLTacticalBrain.compliance(afterState,candidate.expectedNext,geometry):null;
          current.shots++;current.lastOutcome={actor:seat,round:before.rules.nRounds,score:result.adjudication?.score,foulCode:result.adjudication?.foulCode,continueBreak:result.adjudication?.continueBreak};
          const verdict=result.adjudication;
          const valid=Boolean(result.status==='complete'&&verdict&&result.nextBalls);
          const scores=valid?before.rules.scores.map((n,i)=>n+(verdict.score>0&&i===seat?verdict.score:verdict.score<0&&i!==seat?-verdict.score:0)):null;
          emit('stroke.end',{actor:seat,status:result.status,validAdjudication:valid,scoresBefore:[...before.rules.scores],scoresAfter:scores,
            ballOnBefore:before.rules.ballOn,ballOnAfter:valid?(result.nextContext?.ballOn??verdict.nextBallOn):null,
            steps:result.steps,simulatedSeconds:result.simulatedSeconds,result:verdict,potted:result.potted,firstHits:result.firstHits,reviewReasons:result.reviewReasons,nextBalls:result.nextBalls,
            activePlan:decision.activePlan,searchIntent:decision.search?.searchIntent,planCompliance});
          if(result.status!=='complete'||!result.adjudication||!result.nextBalls){reason='physics-needs-ruling';break;}
          if(verdict.frameOutcome==='end') {current.snapshot.rules.scores=scores;winner=scores[0]===scores[1]?null:scores[0]>scores[1]?0:1;reason='black-frame-end';break;}
          if(verdict.frameOutcome==='respot') {
            installState({balls:result.nextBalls,rules:{...before.rules,...result.nextContext,requiresDraw:false,scores,nRounds:(before.rules.nRounds||0)+1,playerIndex:random()<.5?0:1,nominatedColour:null,nominationSource:null,freeBallNominee:null,freeBallAvailable:false,freeBallReview:false,freeBallDeclined:false}});
            emit('ruling.black-draw',{playerIndex:current.snapshot.rules.playerIndex,method:'seeded-uniform'});checkpoint('black-draw');continue;
          }
          if(verdict.foulCode) {
            installState({balls:result.nextBalls,rules:{...before.rules,...result.nextContext,scores,nRounds:(before.rules.nRounds||0)+1,playerIndex:1-seat,nominatedColour:null,nominationSource:null,freeBallNominee:null,freeBallAvailable:false,freeBallReview:false,freeBallDeclined:false}});
            const mask=before.rules.ballOn===252&&before.rules.nominatedColour?1<<before.rules.nominatedColour:before.rules.ballOn;
            const direct=core.hasDirectHit(before.balls,mask),needsSnookers=Math.abs(before.rules.scores[0]-before.rules.scores[1])>core.remainingPoints(before.balls,before.rules.ballOn)||Math.abs(scores[0]-scores[1])>core.remainingPoints(result.nextBalls,verdict.nextBallOn);
            const wrongFirst=Boolean(verdict.foulCode&3);
            // Search candidates carry settled nominal evidence and a complete outcome.
            const nominal=candidate.evidence?.nominal,outcome=candidate.outcome;
            const completeNominal=Boolean(candidate.shot&&outcome&&Number.isFinite(outcome.score)&&Number.isFinite(outcome.nextBallOn)&&
              Array.isArray(outcome.firstHits)&&Number.isFinite(outcome.simulatedSeconds)&&outcome.simulatedSeconds>=0);
            const nominalLegal=completeNominal&&(nominal?.legal===true||outcome.foulCode===0);
            const miss=wrongFirst&&!needsSnookers&&(direct.hasDirectHit===true||nominalLegal);
            current.pending={offender:seat,before,result:verdict,miss};
            emit('ruling.miss',{basis:!wrongFirst?'not-wrong-first':needsSnookers?'needs-snookers':direct.hasDirectHit===true?'direct-hit':nominalLegal?'nominal-trial':'no-clear-evidence',
              miss,direct:direct.hasDirectHit??null,nominalLegal,needsSnookers,experimental:true});
            freeBallAssessment();checkpoint('foul-ruling');continue;
          }
          if(!result.nextSnapshot){reason='continuation-needs-ruling';break;}
          current.snapshot=copy(result.nextSnapshot);
          checkpoint('stroke-ruling');
          if(!current.snapshot.rules.ballOn){winner=scores[0]===scores[1]?null:scores[0]>scores[1]?0:1;reason='frame-end';break;}
          if(finishEarly())break;
        }
        reason=reason||(current.cancelled?'cancelled':'shot-limit');
        const complete=winner!=null,summary={mode:'arena',execution:'isolated-original-physics',complete,reason,winner,shots:current.shots,scores:[...current.snapshot.rules.scores],participants,seed};
        const resume=checkpoint(reason);recorder.endFrame(summary);last={...summary,resume,busy:false,phase:complete?'complete':current.cancelled?'cancelled':'paused'};await recorder.flush();return status();
      } catch(error) {
        const summary={mode:'arena',execution:'isolated-original-physics',complete:false,reason:current.cancelled?'cancelled':error.code||'failed',error:error.message,shots:current.shots,scores:current.snapshot?.rules?.scores,participants};
        const resume=recorder&&current.snapshot?checkpoint(summary.reason):null;
        if(recorder){emit('arena.failure',summary);recorder.endFrame(summary);await recorder.flush();}
        last={...summary,resume,busy:false,phase:current.cancelled?'cancelled':'failed'};return status();
      } finally {current.manager?.cancel();current.search?.cancel();current.trial?.dispose();for(const client of current.clients)client.cancel();if(job===current)job=null;}
    }
    async function runSeries({players,winsRequired=5,seed=Date.now()>>>0,budgetMs=30000,maxShots=160,resume=null}={}) {
      if(job||series?.busy)throw new Error('Arena is already running');
      if(!Number.isInteger(winsRequired)||winsRequired<1||winsRequired>5)throw new Error('Series supports one to five wins');
      const captured=resume?.initial||await capture(),initial=copy(captured.snapshot||captured);
      if(initial.rules.nRounds!==0||initial.rules.scores.some(score=>score!==0))throw new Error('Series requires a fresh frame');
      series=resume?{...copy(resume.series),frames:copy(resume.series.frames.filter(f=>f.complete)),busy:true,cancelled:false,phase:'playing'}:
        {id:'series_'+Date.now().toString(36),busy:true,cancelled:false,winsRequired,wins:[0,0],frames:[],seed,phase:'playing'};
      seed=series.seed;winsRequired=series.winsRequired;let continuation=resume?.frame;
      while(!series.cancelled&&Math.max(...series.wins)<winsRequired) {
        const index=series.frames.length,breaker=index%2,snapshot=copy(initial);
        snapshot.rules.playerIndex=breaker;
        const frameSeed=(seed+Math.imul(index+1,0x9e3779b9))>>>0;
        series.currentFrame=index+1;
        const previousShots=continuation?.shots||0,segments=continuation?.segments||[];
        const result=await run({players,maxShots:maxShots-previousShots,seed:frameSeed,budgetMs,resumeFrom:continuation||{snapshot},
          seriesContext:{id:series.id,index:index+1,breaker,winsRequired,scoreBefore:[...series.wins]}});
        series.frames.push({index:index+1,seed:frameSeed,breaker,frameId:result.recording?.frameId,complete:result.complete,
          winner:result.winner,scores:result.scores,shots:previousShots+result.shots,reason:result.reason,
          segments:[...segments,result.recording?.frameId]});
        continuation=null;
        if(!result.complete){series.phase=series.cancelled?'cancelled':'paused';break;}
        series.wins[result.winner]++;
      }
      series.busy=false;
      if(Math.max(...series.wins)>=winsRequired){series.phase='complete';series.winner=series.wins.indexOf(winsRequired);}
      recorder?.event('series.end',copy(series));await recorder?.flush();
      return status();
    }
    return {run,runSeries,status,cancel};
  }
  return {create};
})();

(() => {
  'use strict';
  const VERSION = "0.16.0";
  const DEVELOPMENT = true;
  const BUILD_ID = "557fe0b9833c";
  if (window.PCOLPatch?.version === VERSION) return;
  const COLOURS = ['白球', '红球', '黄球', '绿球', '棕球', '蓝球', '粉球', '黑球'];
  const FOULS = [[1, '未先碰到目标球'], [2, '先碰错球'], [4, '非法进球'], [8, '白球落袋'], [16, '球离开球台'], [32, '非法跳球'], [64, '利用自由球形成违规斯诺克'], [128, '出杆推动了相贴球（推杆）'], [256, '同一杆中杆头重复击中白球（连击）']];
  const patches = [];
  let active = null;
  const clone = x => JSON.parse(JSON.stringify(x));
  const description = code => FOULS.filter(([bit]) => code & bit).map(([, text]) => text).join('；');
  function wrap(object, key, make, scope = patches) {
    const own = Object.prototype.hasOwnProperty.call(object, key);
    const original = object[key];
    const replacement = make(original);
    object[key] = replacement;
    scope.push(() => { if (object[key] === replacement) { if (own) object[key] = original; else delete object[key]; } });
  }
  function clearSceneHooks(s) {
    for (const undo of s.scenePatches.splice(0).reverse()) undo();
    s.aiHooks=new WeakSet();s.refHooks=new WeakSet();s.deliveryHooks=new WeakSet();
    s.aimGuide=null;
  }
  function syncAimGuide(s) {
    const sight=s.g._gView?.gunsight;
    if(!sight)return;
    if(s.aimGuide!==sight){
      s.aimGuide=sight;
      wrap(sight,'update',original=>function(...args){
        const result=original.apply(this,args);
        // Native segment 4 is the yellow object-ball fan. Keep the native
        // prediction, cue-ball segments and distance limits unchanged.
        if(s.aiSettings.skill==='club'&&s.opponent?.getStatus().enabled)this.segments[4].alpha=0;
        return result;
      },s.scenePatches);
      s.scenePatches.push(()=>{sight.needsUpdate=true;});
    }
    sight.needsUpdate=true;s.g._gView.requireRender();
  }
  function releaseStrokeHistory(s) {
    s.shot=null;s.lastTrace=[];s.lastContacts=[];s.lastBefore=null;s.lastResult=null;
    s.practiceBefore=null;s.activeVisitPlan=null;s.preparedShot=null;
  }
  function balls(g) {
    return g._simulator.getBalls().map(b => ({ i: b.index, n: b.number, active: b.active, x: b.position.x, y: b.position.y, z: b.position.z, r: b.radius }));
  }
  function recordState(s) {
    const m=s.g._model;
    return {balls:balls(s.g),rules:{...m._gContext,nominatedColour:s.nominatedColour,
      freeBallNominee:s.freeBallNominee,freeBallAvailable:s.freeBallAvailable,freeBallReview:s.freeBallReview},
      scores:scores(m),settings:{...s.aiSettings}};
  }
  function beginRecordFrame(s) {
    if(!s.recorder || s.recordingFrame || !s.g._model._gContext.ballOn)return;
    s.recordingFrame=true;s.recordTurn=0;s.recordDecision=0;s.currentTurnId=null;s.currentDecisionId=null;s.lastStrokeRecord=null;
    s.frameStats={startedAt:Date.now(),players:[0,1].map(()=>({shots:0,points:0,fouls:0,penaltyGiven:0,opponentSnookers:0,maxBreak:0})),
      decisions:0,searchMs:0,selectionMs:0};
    s.recorder.startFrame({mode:s.hotseat?'hotseat':s.practice||'single',build:BUILD_ID,initial:recordState(s)});
  }
  function endRecordFrame(s,reason) {
    if(!s.recordingFrame)return;
    s.frameMonitor?.drain('frame-'+reason);
    s.recorder?.endFrame({reason:s.frameEnd?.reason||(s.conceded?'conceded':reason),complete:reason==='finished'||!!s.conceded||!!s.frameEnd,scores:scores(s.g._model),
      concession:s.conceded||null,frameEnd:s.frameEnd||null,summary:{...s.frameStats,elapsedMs:Date.now()-s.frameStats.startedAt}});
    s.recordingFrame=false;s.currentTurnId=null;
  }
  function recordTurn(s) {
    beginRecordFrame(s);
    if(!s.currentTurnId)s.currentTurnId=String(++s.recordTurn);
    return {turnId:s.currentTurnId,decisionId:s.currentDecisionId};
  }
  function recordEvent(s,kind,data,correlation={}) {
    if(kind==='search.complete')s.activeVisitPlan=data.activePlan;
    const stats=s.frameStats;
    if(stats){
      if(kind==='search.complete')stats.searchMs+=data.elapsedMs||0;
      if(kind==='selection.complete'){stats.decisions++;stats.selectionMs+=data.elapsedMs||0;
      }
    }
    return s.recorder?.event(kind,data,{turnId:s.currentTurnId,decisionId:s.currentDecisionId,requestId:data.requestId,...correlation});
  }
  function markStroke(s,label) {
    return s.recorder?.mark(label,{actor:s.lastStrokeRecord?.actor,turnId:s.lastStrokeRecord?.turnId,
      decisionId:s.lastStrokeRecord?.decisionId,controller:s.lastStrokeRecord?.controller,activeDecisionId:s.currentDecisionId});
  }
  function beginDecision(s,kind='shot') {
    if(!DEVELOPMENT)return;
    recordTurn(s);s.currentDecisionId=String(++s.recordDecision);
    recordEvent(s,'decision.start',{kind,state:recordState(s)});
  }
  function hookColourRespots(s) {
    const ref=s.g._model._locRef;
    if(!ref||s.refHooks.has(ref))return;
    s.refHooks.add(ref);
    wrap(ref,'_liveRespotColorBalls',original=>function(list,sim){
      if(!list.some(b=>b.number===6))return original.call(this,list,sim);
      const clearance=1.05*sim.ballRadius,reserved=new Set();
      // Preserve the author's own-spot and highest-available-spot stages.
      for(let i=list.length-1;i>=0;i--){
        const b=list[i];reserved.add(b.number);
        if(!sim.touchBalls(b.index,b.spot,clearance)){list.splice(i,1);sim.respotIndexDefault(b.index);}
      }
      list.sort((a,b)=>a.number-b.number);
      const colours=sim.getBalls().filter(b=>b.number>=2).sort((a,b)=>b.number-a.number);
      for(const spotBall of colours){
        if(!list.length)break;
        const b=list[list.length-1];
        if(!reserved.has(spotBall.number)&&!sim.touchBalls(b.index,spotBall.spot,clearance))sim.resetBallPosition(list.pop(),spotBall.spot);
      }
      // At this point all spots are unavailable. Higher colours go first.
      while(list.length){
        const b=list.pop();
        if(b.number!==6){original.call(this,[b],sim);continue;}
        const ground=sim.ground,margin=sim.ballRadius+2*PCOLCore.CONTACT_EPS;
        const minX=ground.centerPosition.x-ground.size.x/2+margin,maxX=ground.centerPosition.x+ground.size.x/2-margin;
        const bs=sim.getBalls().map(b=>({i:b.index,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,r:b.radius}));
        const x=PCOLCore.pinkRespotX(bs,{i:b.index,...b.spot,r:b.radius},minX,maxX);
        if(x===null)throw new Error('No legal pink-ball respot position');
        sim.resetBallXYZ(b,x,b.spot.y,b.spot.z);
      }
    },s.scenePatches);
  }
  function scores(m) { return m._players.map((p, i, ps) => p.pts - (ps.length > 1 ? ps[(i + 1) % ps.length].penalty : 0)); }
  function actor(s) { return s.hotseat ? `玩家 ${s.g._model._gContext.playerIndex + 1}` : '你'; }
  function startHotseat(s) {
    const home = s.app._controllers.home;
    if (!home || s.app._currentController !== home || home.state !== 3 || s.app._uiLayer?.isBlocked || s.requestedHotseat) return false;
    home._model.setSelectedAIIndex(-1);
    s.requestedHotseat = true;
    s.app.changeController('game');
    return true;
  }
  function startEnhancedGame(s) {
    const home=s.app._controllers.home;
    if(s.app._currentController!==home||home.state!==3||s.app._uiLayer?.isBlocked)return false;
    home._model.setSelectedAIIndex(2);
    s.requestedEnhanced=true;
    s.app.changeController('game');
    return true;
  }
  function syncHotseat(s) {
    if (!s.hotseat) return;
    const g = s.g, fpc = g._fpc, index = g._model._gContext.playerIndex;
    if (!g._playerCtls.includes(fpc)) return;
    // The stock setup resets and appends the same human controller for each USER.
    // Collapse those entries before enter/bind and before any response is dispatched.
    for (const c of new Set(g._playerCtls)) if (c !== fpc) { c.deactivate(); c.release(); }
    g._playerCtls.splice(0, g._playerCtls.length, fpc);
    if (fpc.gPlayerIndex !== index) {
      fpc._gPlayerIndex = index;
      fpc.gotoState0(true);
      fpc.markForceUpdate();
    }
  }
  function ballOnLabel(mask) {
    if (mask === 252) return '任选彩球';
    const targets = PCOLCore.ballOnNumbers(mask);
    return targets.length === 1 ? COLOURS[targets[0]] : '目标球';
  }
  function currentTouching(s) {
    const ctx=s.g._model._gContext;
    return PCOLCore.touchingStatus({balls:balls(s.g),ballOn:ctx.ballOn,nominatedColour:s.nominatedColour,freeBallNominee:s.freeBallNominee});
  }
  function touchingNotice(s) {
    if (s.pending || s.conceded || s.g._model._gState !== 4 || !s.g._model._gContext.ballOn || s.g._model._gContext.ballOn === 65535) return '';
    const info=currentTouching(s);
    if (!info.indices.length) return '';
    const names=[...new Set(info.indices.map(i=>COLOURS[s.g._simulator.getBallAtIndex(i).number]))].join('、');
    if (info.requiresColourDeclaration && s.nominationSource !== 'manual') return `贴球：${names} · 须明确指定彩球`;
    return `贴球：${names} · ${info.deemedHit ? '合法打离即视为已碰目标' : '打离后仍须先碰目标'}`;
  }
  function statusLine(s) {
    const on = s.g._model._gContext.ballOn;
    if (s.frameEnd) return s.frameEnd.reason==='black-lead'?'仅剩黑球，领先至少 8 分 · 本局结束':'超分至少 17 分，按约定结束本局';
    if (s.conceded) return `${s.hotseat?'玩家 '+(s.conceded.playerIndex+1):s.conceded.playerIndex===s.g._fpc.gPlayerIndex?'你':'对手'}已认输`;
    if (s.pending) return `犯规 ${-s.pending.result.score} 分 · 等待选择`;
    if (s.blackDecider) return `平局争黑 · ${s.hotseat ? `玩家 ${s.g._model._gContext.playerIndex + 1}` : s.g._model._gContext.playerIndex === s.g._fpc.gPlayerIndex ? '你' : '对手'}击球`;
    if (s.freeBallNominee != null) return `自由球：${COLOURS[s.g._simulator.getBallAtIndex(s.freeBallNominee).number]}（按${ballOnLabel(on)}计）`;
    if (s.freeBallAvailable) return `目标：${ballOnLabel(on)} · 可选自由球`;
    if (s.freeBallReview) return '手中球：自由球需裁判确认';
    if (s.nominatedColour) return `本杆目标：${COLOURS[s.nominatedColour]}（${s.nominationSource === 'auto' ? '自动' : '手动'}）`;
    if (on === 252) return '彩球：自动识别 · 可手动选球';
    const target = PCOLCore.ballOnNumbers(on);
    return target.length === 1 ? `目标：${COLOURS[target[0]]}` : '规则补丁已启用';
  }
  const PANEL_POSITION_KEY = 'pcol-rules-patch:panel-position';
  function positionPanel(s, x, y) {
    const rect = s.shadow.querySelector('.bar').getBoundingClientRect();
    s.panelPosition = {
      x:Math.max(8,Math.min(x,window.innerWidth-rect.width-8)),
      y:Math.max(8,Math.min(y,window.innerHeight-rect.height-8))
    };
    s.host.style.left = `${s.panelPosition.x}px`;
    s.host.style.top = `${s.panelPosition.y}px`;
    s.host.style.bottom = 'auto';
  }
  function enablePanelDrag(s) {
    let drag = null;
    try {
      const stored = JSON.parse(window.localStorage.getItem(PANEL_POSITION_KEY));
      if (Number.isFinite(stored?.x) && Number.isFinite(stored?.y)) s.panelPosition = stored;
    } catch (_) { /* Storage can be disabled; dragging still works this session. */ }
    for(const handle of [s.shadow.querySelector('.drag'),s.shadow.querySelector('.status')]){
    handle.onpointerdown = e => {
      if (e.button !== 0 || s.modal) return;
      e.preventDefault();
      const rect = s.host.getBoundingClientRect();
      drag = {id:e.pointerId,x:e.clientX,y:e.clientY,left:rect.left,top:rect.top};
      handle.setPointerCapture(e.pointerId);
    };
    handle.onpointermove = e => {
      if (!drag || drag.id !== e.pointerId) return;
      positionPanel(s,drag.left+e.clientX-drag.x,drag.top+e.clientY-drag.y);
    };
    const finish = e => {
      if (!drag || drag.id !== e.pointerId) return;
      drag = null;
      if (handle.hasPointerCapture(e.pointerId)) handle.releasePointerCapture(e.pointerId);
      try { if (s.panelPosition) window.localStorage.setItem(PANEL_POSITION_KEY,JSON.stringify(s.panelPosition)); } catch (_) {}
      if (!s.modal) s.g._gView?.canvas?.focus();
    };
    handle.onpointerup = finish;
    handle.onpointercancel = finish;
    handle.ondblclick = () => {
      s.panelPosition = null;
      Object.assign(s.host.style,{left:'16px',top:'auto',bottom:'14px'});
      try { window.localStorage.removeItem(PANEL_POSITION_KEY); } catch (_) {}
    };
    }
    const resize = () => { if (s.panelPosition) positionPanel(s,s.panelPosition.x,s.panelPosition.y); };
    const observer = new window.ResizeObserver(resize);
    observer.observe(s.shadow.querySelector('.bar'));
    window.addEventListener('resize',resize);
    patches.push(() => {observer.disconnect();window.removeEventListener('resize',resize);window.cancelAnimationFrame(s.renderFrame);});
  }
  function mount(s) {
    if (s.host) return;
    const host = document.createElement('div');
    host.id = 'pcol-rules-patch';
    host.style.cssText = 'position:fixed;left:16px;bottom:14px;z-index:2147483000;font:13px/1.5 "Microsoft YaHei",sans-serif;color:#fff;';
    const shadow = host.attachShadow({ mode: 'open' });
    shadow.innerHTML = `<style>
      *{box-sizing:border-box}button{font:inherit;cursor:pointer;border:1px solid #3b5149;border-radius:9px;background:#21332d;color:#edf3ef;padding:10px 15px;transition:background .15s,border-color .15s}button:hover{background:#304b40;border-color:#739a83}button:focus-visible{outline:2px solid #dfc591;outline-offset:3px}button.primary{background:#d7bf8c;border-color:#d7bf8c;color:#18271f;font-weight:700}button.primary:hover{background:#ebd5a8}button:disabled{opacity:.45;cursor:default}[hidden]{display:none!important}
      .bar{display:flex;gap:7px;align-items:center;flex-wrap:wrap;max-width:calc(100vw - 32px);padding:9px 12px;background:#101f19f2;border:1px solid #446352;border-radius:13px;box-shadow:0 5px 24px #0005}.bar button{padding:6px 11px;font-size:12px;order:2}.bar .ai{order:1;background:#d7bf8c;border-color:#d7bf8c;color:#18271f;font-weight:700}.bar .recording{order:3;background:transparent;color:#adc2b6;border-color:transparent}.bar .mark{order:3;background:transparent}.bar .concede{color:#dfb6a9}.status{max-width:min(400px,calc(100vw - 100px));color:#d9e6dd;line-height:1.6;padding-right:8px}.drag{cursor:grab;touch-action:none;user-select:none;padding:0 3px;color:#8aa893;font-size:20px}.drag:active{cursor:grabbing}.bar[data-practice="true"] .status{cursor:grab;touch-action:none;user-select:none;font-weight:500}
      .veil{position:fixed;inset:0;display:grid;place-items:center;background:#07100cd9;padding:16px}.panel{position:relative;width:min(540px,100%);max-height:calc(100dvh - 32px);overflow:auto;overscroll-behavior:contain;background:#13251d;border:1px solid #4a6553;border-radius:18px;padding:28px;box-shadow:0 24px 90px #0009;line-height:1.6}.panel h2{font-size:24px;font-weight:600;letter-spacing:.02em;margin:0 42px 5px 0;color:#f3f1e6}.panel p{margin:6px 0 18px;color:#aebfb3;font-size:13px}.choices{display:flex;gap:9px;flex-wrap:wrap}.note{font-size:12px;color:#a4b7a8;margin-top:16px;line-height:1.7}.dismiss-dialog{position:absolute;right:18px;top:18px;width:34px;height:34px;padding:0;font-size:23px;background:transparent;border-color:transparent;color:#b7c8ba}.dismiss-dialog:hover{background:#2a3e31}
      .opponent-panel{width:min(660px,100%)}.ai-summary{display:flex;align-items:center;justify-content:space-between;gap:12px;padding:16px 18px;border:1px solid #48614e;background:#1d3528;border-radius:12px;margin-top:20px}.ai-summary strong{font-size:15px;color:#e9efe5}.ai-summary small{display:block;color:#a5bca9;font-size:12px;margin-top:3px}.local-badge{color:#d9c18e;font-size:11px;white-space:nowrap;border:1px solid #6d7051;border-radius:20px;padding:3px 9px}.setting-section{margin-top:23px}.section-heading{display:flex;justify-content:space-between;align-items:baseline;gap:10px;margin-bottom:10px}.section-heading h3{font-size:14px;font-weight:600;color:#e2e9df;margin:0}.section-heading span{font-size:11px;color:#97af9d}.setting-options{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:9px}.setting-option{text-align:left;padding:13px 14px;background:#192d22;border-color:#3b5141;position:relative}.setting-option strong{display:block;font-weight:600;font-size:14px}.setting-option small{display:block;color:#a0b49f;font-size:11px;margin-top:5px;line-height:1.6}.setting-option[aria-pressed="true"]{background:#304333;border-color:#d8c28c;box-shadow:inset 0 0 0 1px #d8c28c}.setting-option[aria-pressed="true"] strong{color:#f2dba7}.setting-option[aria-pressed="true"] strong::after{content:' ✓';font-size:11px}.current-setting{font-size:12px;color:#d7c395;padding-top:17px;margin-top:22px;border-top:1px solid #334b3b}.settings-footer{display:flex;justify-content:flex-end;gap:9px;margin-top:22px}.settings-footer .primary{min-width:146px}.record-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:9px;margin:18px 0}.record-stat{padding:14px 10px;background:#1c3225;border:1px solid #354e3c;border-radius:10px;text-align:center}.record-stat strong{display:block;font-size:25px;color:#e8d4a6;font-variant-numeric:tabular-nums}.record-stat span{font-size:12px;color:#a7bca9}
      @media(max-width:520px){.panel{padding:23px 18px;border-radius:14px}.panel h2{font-size:21px}.setting-options{gap:6px}.setting-option{padding:11px 8px}.setting-option strong{font-size:12px}.section-heading span{font-size:10px}.bar{padding:8px;gap:5px}.bar button{padding:6px 8px}.ai-summary{padding:13px}.settings-footer{flex-wrap:wrap}}
    </style><div class="bar"><span class="drag" title="拖动浮窗；双击恢复位置">⠿</span><span class="status" title="拖动浮窗；双击恢复位置"></span><button type="button" class="hotseat" hidden>双人对局</button><button type="button" class="practice" hidden>练球</button><button type="button" class="retry" hidden>复位重打</button><button type="button" class="choose">选球</button><button type="button" class="concede" hidden>认输本局</button></div><div class="practice-controls"></div><div class="modal"></div>`;
    document.documentElement.appendChild(host);
    s.host = host; s.shadow = shadow;
    const aiButton=document.createElement('button');aiButton.type='button';aiButton.className='ai';
    aiButton.textContent='与 AI 对局';aiButton.onclick=()=>showOpponent(s);shadow.querySelector('.bar').append(aiButton);
    if(DEVELOPMENT){
      const recordButton=document.createElement('button');recordButton.type='button';recordButton.className='recording';
      recordButton.onclick=()=>showRecording(s);shadow.querySelector('.bar').append(recordButton);
      const markButton=document.createElement('button');markButton.type='button';markButton.className='mark';markButton.textContent='标记上一杆';
      markButton.onclick=()=>showAnnotation(s);
      shadow.querySelector('.bar').append(markButton);
    }
    enablePanelDrag(s);
    shadow.querySelector('.hotseat').onclick = () => startHotseat(s);
    shadow.querySelector('.practice').onclick = () => choosePractice(s);
    shadow.querySelector('.retry').onclick = () => retryPractice(s);
    shadow.querySelector('.choose').onclick = () => chooseBall(s);
    shadow.querySelector('.concede').onclick = () => showConcession(s);
    shadow.addEventListener('keydown', e => e.stopPropagation());
    shadow.addEventListener('pointerdown', e => e.stopPropagation());
    render(s);
  }
  function requestRender(s) {
    if(s.renderFrame!=null)return;
    s.renderFrame=window.requestAnimationFrame(()=>{s.renderFrame=null;if(s.host?.isConnected)render(s);});
  }
  function renderRecording(s) {
    if(!s.host?.isConnected)return;
    const r=s.recorder?.getStatus(),button=s.shadow.querySelector('.recording');
    const label='记录 · '+(!r?.enabled?'已暂停':r.error?'保存失败':r.saving?'保存中':'本机已保存');
    const title=r?`本机累计已保存 ${r.localSaved}，待同步 ${r.pending}，正在保存 ${r.saving}`:'';
    if(button.textContent!==label)button.textContent=label;
    if(button.title!==title)button.title=title;
  }
  function render(s) {
    if (!s.host) mount(s);
    const live = s.app._currentController === s.g && s.g._model._gState !== 1;
    const home = s.app._currentController === s.app._controllers.home && s.app._controllers.home?.state === 3;
    const custom=s.practice==='custom',replay=live && s.g._activeSubControl?.name==='replay';
    const controlsVisible=live && custom && !replay && s.g._model._gState===4 && !s.shot && !s.practiceControlsHidden && !s.modal;
    s.host.style.display = live || home ? 'block' : 'none';
    s.shadow.querySelector('.bar').hidden = replay || (live && custom && !controlsVisible);
    s.shadow.querySelector('.bar').setAttribute('data-practice',String(live && custom));
    s.shadow.querySelector('.drag').hidden=live && custom;
    s.shadow.querySelector('.hotseat').hidden = !home;
    s.shadow.querySelector('.practice').hidden = !home;
    const retry = s.shadow.querySelector('.retry');
    retry.hidden = !(live && s.practice);
    retry.disabled = !canRetryPractice(s) || s.modal;
    retry.title = '恢复上一杆前的球位、分数和单杆分';
    const touching=live?touchingNotice(s):'';
    s.shadow.querySelector('.status').textContent = home ? 'PCOL · 对局与练习' : custom ? '自由练习' : `${s.hotseat ? `人格分裂 · ${actor(s)}${s.pending ? '决定' : '击球'} · ` : s.practice === 'standard' ? '单人练习 · ' : ''}${touching?`${touching} · `:''}${statusLine(s)}`;
    const eligible = live && !s.pending && s.g._model._gState === 4 && s.g._model._gContext.playerIndex === s.g._fpc.gPlayerIndex && (s.freeBallAvailable || s.freeBallReview || s.g._model._gContext.ballOn === 252);
    s.shadow.querySelector('.choose').hidden = !eligible;
    s.shadow.querySelector('.concede').hidden = !(live && concessionInfo(s).available && s.g._model._gContext.playerIndex === s.g._fpc.gPlayerIndex && !s.modal);
    const aiStatus=API.ai?.getStatus(),opponent=aiStatus?.opponent;
    const aiButton=s.shadow.querySelector('.ai');
    aiButton.hidden=live&&(!opponent?.enabled||s.hotseat||s.practice);
    const phase=opponent?.error||aiStatus?.turn.failed?'已暂停':aiStatus?.turn.busy?'选择回合方案':opponent?.busy?'正在试打':'设置';
    aiButton.textContent=home?'与 AI 对局':'本地 AI · '+phase;
    aiButton.title=opponent?.error || '调整本地 AI 的击球准度与战术倾向';
    if(DEVELOPMENT){renderRecording(s);
      s.shadow.querySelector('.mark').disabled=!s.lastBefore;
      s.shadow.querySelector('.mark').hidden=home;
    }
    if(s.editor){s.editor.setVisible(controlsVisible);if(controlsVisible)s.editor.update(editableBalls(s),s.placement?.selectedIndex ?? null,Boolean(s.placement));}
  }
  function thinkingAllowed(s) {
    return s.modal ? s.modalKind==='annotation'&&!s.pausedBeforeModal : !s.g._paused;
  }
  function afterAnnotation(s,apply) {
    if(s.modalKind!=='annotation'){apply();return;}
    s.afterAnnotation={fingerprint:JSON.stringify(recordState(s)),apply};
  }
  function showAnnotation(s) {
    if(s.modal)return;
    dialog(s,'标记上一杆','AI 可以继续计算，选好后会等你关闭标记再出杆。',
      ['不合理','精彩','等待异常'].map(label=>[label,()=>{markStroke(s,label);closeModal(s);}])
        .concat([['取消',()=>closeModal(s)]]),'','annotation');
    const g=s.g,ctl=g._playerCtls.find(c=>c.gPlayerIndex===g._model._gContext.playerIndex);
    ctl?._ai?.checkRestart?.(g._simulator,g._model);
    if(!s.ensureAITurn())s.opponent?.step(null,()=>null,[]);
  }
  function closeModal(s) {
    s.shadow?.querySelector('.modal').replaceChildren();
    if (s.modal) s.g._paused = s.pausedBeforeModal;
    s.modal = false;s.modalKind=null;
    const deferred=s.afterAnnotation;s.afterAnnotation=null;
    if(deferred&&deferred.fingerprint===JSON.stringify(recordState(s)))deferred.apply();
    s.g._gView?.canvas?.focus();
    if (s.app._currentController === s.app._controllers.home) s.app._controllers.home._homeMainMenu?.activate();
    render(s);
  }
  function dialog(s, title, message, choices, note = '', kind = 'ruling') {
    mount(s);
    if (!s.modal) s.pausedBeforeModal = s.g._paused;
    s.modal = true;s.modalKind=kind; s.g._paused = true;
    const veil = document.createElement('div'); veil.className = 'veil';
    const panel = document.createElement('section'); panel.className = 'panel'; panel.setAttribute('role', 'dialog'); panel.setAttribute('aria-modal', 'true'); panel.setAttribute('aria-label', title);
    const h = document.createElement('h2'); h.textContent = title;
    const p = document.createElement('p'); p.textContent = message;
    const group = document.createElement('div'); group.className = 'choices';
    for (const [label, action, primary] of choices) {
      const b = document.createElement('button'); b.type = 'button'; b.textContent = label; if (primary) b.className = 'primary';
      b.onclick = () => action(); group.append(b);
    }
    panel.append(h, p, group);
    if (note) { const n = document.createElement('div'); n.className = 'note'; n.textContent = note; panel.append(n); }
    veil.append(panel); s.shadow.querySelector('.modal').replaceChildren(veil);
    group.querySelector('button')?.focus();
    return panel;
  }
  function concessionInfo(s) {
    const m = s.g._model, ctx = m._gContext;
    const info = PCOLCore.concessionStatus({ balls: balls(s.g), ballOn: ctx.ballOn, scores: scores(m), playerIndex: ctx.playerIndex, freeBall: (s.freeBallAvailable || s.freeBallReview) && !s.freeBallDeclined });
    const turn = s.concessionTurn;
    return { ...info, available: info.eligible && m._gState === 4 && !s.shot && !s.pending && !s.freeBallReview && !s.conceded && !s.frameEnd && turn?.round === ctx.nRounds && turn.playerIndex === ctx.playerIndex };
  }
  function concedeFrame(s,reason='player-choice') {
    const info = concessionInfo(s);
    if (!info.available) return false;
    const m = s.g._model, playerIndex = m._gContext.playerIndex;
    s.conceded = { playerIndex, winnerIndex: 1-playerIndex, round: m._gContext.nRounds, score: scores(m), remaining: info.remaining, excess: info.excess,reason };
    s.log.push({ kind: 'concession', ...clone(s.conceded) });
    recordEvent(s,'frame.concession',s.conceded);
    s.concessionTurn = null;
    closeModal(s);
    resetTurn(s);
    s.opponent?.reset();
    m._gContext.ballOn = 0;
    m._gContext.inHand = 0;
    syncResponse(s);
    return true;
  }
  function considerAIConcession(s,state,decision) {
    if(s.pending||s.freeBallReview)return false;
    const ctx=s.g._model._gContext,info=concessionInfo(s),mark=ctx.nRounds+':'+ctx.playerIndex;
    if(!info.eligible||s.aiConcessionMark===mark)return false;
    s.aiConcessionMark=mark;
    const assessment=PCOLTacticalPolicy.concession(state,decision,PCOLSearchGeometry);
    recordEvent(s,'concession.check',{actor:ctx.playerIndex,deficit:info.deficit,remaining:info.remaining,excess:info.excess,
      ...assessment,source:'local-policy'});
    if(assessment.action!=='concede')return false;
    s.concessionTurn={round:ctx.nRounds,playerIndex:ctx.playerIndex};
    afterAnnotation(s,()=>concedeFrame(s,assessment.reason));
    return true;
  }
  function awardEarlyFrame(s,actor,continueBreak=false) {
    const m=s.g._model,ctx=m._gContext;
    const result=PCOLCore.earlyFrameOutcome({balls:balls(s.g),ballOn:ctx.ballOn,scores:scores(m),playerIndex:ctx.playerIndex,actor,continueBreak,
      freeBall:s.freeBallAvailable&&!s.freeBallDeclined,freeBallReview:s.freeBallReview});
    if(!result)return false;
    s.frameEnd={...result,round:ctx.nRounds,scores:scores(m)};
    recordEvent(s,'frame.awarded',s.frameEnd);s.log.push({kind:'frame.awarded',...clone(s.frameEnd)});
    s.pending=null;s.concessionTurn=null;resetTurn(s);s.opponent?.reset();
    if(s.modal)closeModal(s);
    ctx.ballOn=0;ctx.inHand=0;syncResponse(s);return true;
  }
  function confirmFreeBall(s,available) {
    s.freeBallReview=false;s.freeBallAvailable=available;closeModal(s);
    if(awardEarlyFrame(s,s.lastBefore?.context.playerIndex,false))return true;
    offerConcession(s,s.lastBefore?.context.playerIndex);
    return false;
  }
  function showConcession(s) {
    const info = concessionInfo(s);
    if (!info.available || s.modal || s.g._model._gContext.playerIndex !== s.g._fpc.gPlayerIndex) return;
    dialog(s, '本局是否继续？', `${actor(s)}落后 ${info.deficit} 分，剩余最高可得 ${info.remaining} 分，已超分 ${info.excess} 分。可以继续争取罚分，或认输本局。`, [
      ['继续本局', () => closeModal(s), true],
      ['认输本局', () => concedeFrame(s)]
    ], '继续后，出杆前仍可用左下角的“认输本局”按钮重新选择。');
  }
  function offerConcession(s, previousPlayer) {
    const ctx = s.g._model._gContext;
    if (!ctx.ballOn || ctx.ballOn === 65535 || ctx.playerIndex === previousPlayer) return;
    s.concessionTurn = { round: ctx.nRounds, playerIndex: ctx.playerIndex };
    if (concessionInfo(s).available && ctx.playerIndex === s.g._fpc.gPlayerIndex) showConcession(s);
    render(s);
  }
  function chooseBall(s, needsDeclaration = false) {
    const m = s.g._model;
    if (s.pending || m._gState !== 4 || m._gContext.playerIndex !== s.g._fpc.gPlayerIndex) return;
    if (s.freeBallReview) {
      dialog(s, '手中球的自由球判定', '只有白球在 D 区内所有合法位置都无法看见目标球两侧，才可判自由球。这个特殊局面需要裁判确认。', [
        ['不判自由球', () => confirmFreeBall(s,false), true],
        ['裁判确认自由球', () => { s.log.push({ kind: 'referee-free-ball-confirmation' }); if(!confirmFreeBall(s,true)&&!s.modal)chooseBall(s); }]
      ], '程序未把有限采样当成全 D 区证明。');
    } else if (s.freeBallAvailable) {
      const on = PCOLCore.ballOnNumbers(m._gContext.ballOn);
      const candidates = balls(s.g).filter(b => b.active && b.n > 0 && !on.includes(b.n));
      dialog(s, '自由球', '请选择作为目标球的自由球，或按原目标球继续。自由球按本杆目标球的分值计算。', [
        ...candidates.map(b => [COLOURS[b.n], () => { s.freeBallNominee = b.i; s.freeBallDeclined = false; closeModal(s); }]),
        ['按原目标球继续', () => { s.freeBallNominee = null; s.freeBallDeclined = true; closeModal(s); }, true]
      ]);
    } else if (m._gContext.ballOn === 252) {
      const choices = balls(s.g).filter(b => b.active && b.n > 1).map(b => [COLOURS[b.n], () => { s.nominatedColour = b.n; s.nominationSource = 'manual'; closeModal(s); }]);
      choices.push(['使用自动识别', () => { s.nominatedColour = null; s.nominationSource = null; closeModal(s); }]);
      dialog(s, '指定彩球', needsDeclaration === 'touching' ? '白球贴着彩球，规则要求明确声明目标。指定相贴彩球后，合法打离即视为已碰目标；指定其他彩球则仍须先碰到它。选好后再按空格出杆。' : needsDeclaration ? '当前方向无法明确判断目标彩球，请先指定。选好后可继续调整瞄准，再按空格出杆。' : '通常会在出杆时自动识别目标；也可以在这里手动指定。白球可先碰库，但首先碰到的目标球必须符合指定。', choices);
    }
  }
  function takeSnapshot(s) {
    const g = s.g, m = g._model, w = g._simulator._world;
    return { serial: clone(w.serialize({ balls: [] })), context: { ...m._gContext }, balls: balls(g), scores: scores(m), players: m._players.map(p => ({pts:p.pts,penalty:p.penalty,brk:p.brk,maxbrk:p.maxbrk,shootingCount:p.shootingCount,scoreCount:p.scoreCount})), refResult: {...m._refResult}, nominatedColour: s.nominatedColour, nominationSource: s.nominationSource, freeBallNominee: s.freeBallNominee, touching:currentTouching(s) };
  }
  function choosePractice(s) {
    if (s.modal) return;
    dialog(s, '选择练习方式', '两种练习都由你独自控制，每杆结束后均可复位重打。', [
      ['自定义摆球 · 自由练习', () => { closeModal(s); startPractice(s, 'custom'); }, true],
      ['正常球形 · 斯诺克规则', () => { closeModal(s); startPractice(s, 'standard'); }],
      ['返回', () => closeModal(s)]
    ], '自定义模式可自由摆放一套标准球组，不限制先碰球；正常模式按红球、彩球顺序计分与判罚。');
  }
  function startPractice(s, mode) {
    const home = s.app._controllers.home;
    if (!['custom','standard'].includes(mode) || s.app._currentController !== home || home.state !== 3 || s.app._uiLayer?.isBlocked) return false;
    home._model.setSelectedAIIndex(-1);
    s.requestedPractice = mode;
    s.app.changeController('game');
    return true;
  }
  function practiceReady(s) {
    return Boolean(s.practice && s.app._currentController === s.g && s.g._model._gState === 4 && !s.shot && !s.g._uiLayer.isBlocked && s.g._activeSubControl?.name !== 'replay');
  }
  function canRetryPractice(s) { return practiceReady(s) && !s.placement && Boolean(s.practiceBefore); }
  function practiceBounds(s) {
    // The stock model projects the ball centre onto the actual cloth polygon,
    // including the cut corners. Do not enlarge pocket openings with guessed circles.
    return {contains:(x,z)=>s.g._model.pointProjectionOnTable(x,s.g._simulator.spotY,z)};
  }
  function editableBalls(s) {
    return balls(s.g).map(b=>({...b,spot:{...s.g._simulator.getBallAtIndex(b.i).spot}}));
  }
  function placePracticeLayout(s, layout) {
    const sim = s.g._simulator;
    for (const b of layout) sim.resetBallPosition(sim.getBallAtIndex(b.i), b.active ? {x:b.x,y:sim.spotY,z:b.z} : null);
    sim.reset(false, true);
    sim._world.accumulator = 0;
  }
  function ensurePracticePanel(s) {
    if(s.editor)return;
    const changeLayout=layout=>{
      if(!practiceReady(s))return;
      if(!s.placement)openPracticeEditor(s);
      placePracticeLayout(s,layout);s.placement.changed=true;syncResponse(s);refreshPlacement(s);
    };
    s.editor=PCOLPractice.createEditor({document,window,container:s.shadow.querySelector('.practice-controls'),balls:editableBalls(s),
      onSelect:n=>{if(!s.placement&&!openPracticeEditor(s))return;selectPlacementBall(s,n);},
      onClear:()=>changeLayout(editableBalls(s).map(b=>({...b,active:b.n===0}))),
      onStandard:()=>changeLayout(editableBalls(s).map(b=>({...b,...b.spot,active:true}))),
      onCancel:()=>finishPracticeEditor(s,false)
    });
    const shortcut=e=>{
      if((e.key==='w'||e.key==='W'||e.key==='ArrowUp')&&practiceReady(s)&&!s.modal){
        e.preventDefault();e.stopImmediatePropagation();s.g._fpc.gotoState1();s.g._gView.canvas.focus();
      }else if(e.key==='Escape'&&s.placement){e.preventDefault();e.stopImmediatePropagation();finishPracticeEditor(s,false);}
    };
    const canvas=s.g._gView.canvas;
    canvas.addEventListener('keydown',shortcut,true);s.shadow.addEventListener('keydown',shortcut,true);
    s.removePracticeKeys=()=>{canvas.removeEventListener('keydown',shortcut,true);s.shadow.removeEventListener('keydown',shortcut,true);};
  }
  function destroyPracticePanel(s) {
    if(!s.editor)return;
    s.removePracticeKeys();s.editor.destroy();s.editor=null;
  }
  function openPracticeEditor(s) {
    if (s.practice !== 'custom' || !practiceReady(s) || s.modal || s.placement) return false;
    ensurePracticePanel(s);
    s.celebration.clear();s.practiceControlsHidden=false;
    s.placement={before:takeSnapshot(s),bounds:practiceBounds(s),selectedIndex:0,changed:false};
    const hand=s.g._subControl.inHand;
    hand._closeTip();hand._tipPopped=true;hand._firstLookToSet=true;
    s.g._activateSubControl('inHand');
    selectPlacementBall(s,1);
    render(s);
    return true;
  }
  function selectPlacementBall(s,number,index=null) {
    const bs=balls(s.g);
    const b=number===1?(index==null?bs.find(b=>b.n===1&&!b.active)||bs.find(b=>b.n===1):bs.find(b=>b.i===index)):bs.find(b=>b.n===number);
    s.placement.selectedIndex=b.i;
    refreshPlacement(s);
    s.g._gView.canvas.focus();
  }
  function refreshPlacement(s) {
    const b=s.g._simulator.getBallAtIndex(s.placement.selectedIndex),hand=s.g._subControl.inHand,view=s.g._gView;
    if(b.active)view.showRespotIcons(b.position);else view._respotIcon0.alpha=0;
    hand._needsUpdate=true;hand._isValidSpot=false;
    s.editor.update(editableBalls(s),b.index,true);
    view.requireRender();
  }
  function placeSelectedBall(s,position) {
    if(!practiceReady(s))return false;
    const bs=balls(s.g),b=bs.find(b=>b.i===s.placement.selectedIndex),candidate={...b,x:position.x,z:position.z};
    if(PCOLPractice.placementError(bs,candidate,s.placement.bounds))return false;
    const sim=s.g._simulator;
    sim.respotIndexXYZ(b.i,position.x,sim.spotY,position.z);
    sim.reset(false,true);
    s.placement.changed=true;
    syncResponse(s);
    // Continue taking reds from the tray until all fifteen are on the table.
    if(b.n===1&&!b.active&&sim.getBalls().some(b=>b.number===1&&!b.active))selectPlacementBall(s,1);else refreshPlacement(s);
    return true;
  }
  function finishPracticeEditor(s,keep) {
    const edit=s.placement;
    if(!edit)return false;
    s.placement=null;s.practiceControlsHidden=keep;
    if(!keep){restoreSnapshot(s,edit.before);return true;}
    if(edit.changed){
      s.practiceLayout=editableBalls(s);s.practiceBefore=null;s.lastResult=null;s.lastBefore=null;
      resetTurn(s);
      for(const p of s.g._model._players)p.clearScores();
      Object.assign(s.g._model._gContext,{playerIndex:0,nRounds:0,ballOn:65535,inHand:1});
      Object.assign(s.g._model._refResult,{score:0,foulCode:0});
      s.g._movieClip.erase();
    }
    s.g._gView.canvas.focus();
    syncResponse(s);
    return true;
  }
  function retryPractice(s) {
    if (!canRetryPractice(s)) return false;
    const before = s.practiceBefore;
    closeModal(s);
    s.celebration.clear(); s.practiceBefore = null; s.lastResult = null;
    s.g._movieClip.erase();
    s.log.push({kind:'practice-retry',round:before.context.nRounds});
    restoreSnapshot(s,before);
    return true;
  }
  function restoreSnapshot(s,before) {
    const g=s.g,m=g._model,sim=g._simulator;
    resetTurn(s);
    sim._world.restore(before.serial);
    sim._world.accumulator = 0;
    sim._nPhxAwakened = sim._world.nAwakened;
    for (const b of sim.getBalls()) b.syncStates(0);
    sim.clearResult();
    Object.assign(m._gContext,before.context);
    Object.assign(m._refResult,before.refResult);
    before.players.forEach((p,i)=>{
      const target=m._players[i];
      target.pts=p.pts;target.penalty=p.penalty;target.brk=p.brk;target._maxBrk=p.maxbrk;target.shootingCount=p.shootingCount;target.scoreCount=p.scoreCount;
    });
    s.nominatedColour=before.nominatedColour;s.nominationSource=before.nominationSource;s.freeBallNominee=before.freeBallNominee;
    g._fpc.gotoState0(true);g._fpc.markForceUpdate();
    g._gView.syncBalls(sim.getBalls(),sim.evolution);
    syncResponse(s);
  }
  function recordCompletedStroke(s, shot, result) {
    s.frameMonitor?.drain('stroke');
    if(shot.localAI)s.recordAIOutcome?.(result);
    s.lastTrace=shot.trace;s.lastContacts=shot.contacts;s.lastBefore=shot.before;s.lastResult=result;
    if (s.practice) s.practiceBefore=shot.before;
    if (s.practice==='custom') s.practiceControlsHidden=false;
    s.log.push({kind:'stroke',round:s.g._model._gContext.nRounds,offender:shot.before.context.playerIndex,result:clone(result),score:scores(s.g._model),traceSamples:shot.trace.length});
    if(s.log.length>100)s.log.shift();
    if(DEVELOPMENT){
      const actor=shot.before.context.playerIndex,after=recordState(s),handedOver=after.rules.playerIndex!==actor;
      const snooker=after.rules.ballOn?PCOLCore.isSnookered(after.balls,after.rules.ballOn,null,{inHand:after.rules.inHand>0}):{snookered:null};
      const facts={nextActor:after.rules.playerIndex,nextTarget:ballOnLabel(after.rules.ballOn),handedOver,pendingFoulRuling:!!result.foulCode,
        opponentSnookered:handedOver&&!result.foulCode?snooker.snookered:false,selfSnookered:handedOver?false:snooker.snookered,
        firstHitBalls:(result.firstHits||[]).map(i=>({id:i,name:COLOURS[shot.before.balls.find(b=>b.i===i)?.n]}))};
      const id=recordEvent(s,'stroke.end',{actor,result:clone(result),facts,after,
        planCompliance:s.activeVisitPlan?.actor===actor?s.assessPlan?.(s.activeVisitPlan.expectedNext,after):null,
        elapsedMs:shot.recordStarted?performance.now()-shot.recordStarted:null},{strokeId:shot.recordId});
      s.lastStrokeRecord={id,actor,turnId:s.currentTurnId,decisionId:s.currentDecisionId,controller:shot.recordController};
      const stats=s.frameStats.players[actor];stats.shots++;stats.points+=Math.max(0,result.score);
      stats.fouls+=result.foulCode?1:0;stats.penaltyGiven+=Math.max(0,-result.score);stats.opponentSnookers+=facts.opponentSnookered===true?1:0;
      stats.maxBreak=Math.max(stats.maxBreak,s.g._model._players[actor].brk);
      s.currentTurnId=null;s.currentDecisionId=null;
    }
    s.shot=null;resetTurn(s);
  }
  function finishFreePractice(s) {
    const m=s.g._model,sim=s.g._simulator,shot=s.shot;
    shot.physical=false;
    const pottedCount=sim.result.pottedIndices.filter(i=>sim.getBallAtIndex(i).number>0).length;
    if(!sim.getBallAtIndex(0).active)m._locRef._liveRespotCueBall(sim);
    sim.reset(false,false);
    m._gContext.nRounds++;m._gContext.ballOn=65535;m._gContext.inHand=1;
    Object.assign(m._refResult,{score:0,foulCode:0});
    recordCompletedStroke(s,shot,{score:0,foulCode:0,pottedCount});
    syncResponse(s,m._refResult);
    return m;
  }
  function sample(s) {
    const shot = s.shot;
    if (!shot?.physical || s.predicting) return null;
    const sim=s.g._simulator,bs=sim.getBalls(),q=bs[0],p=q.position;
    const row=shot.trace.sample(bs);
    if (!row) { shot.overflow = true; return null; }
    for (const [index,watch] of shot.touchWatches) {
      if (!watch.initial) continue;
      const b=sim.getBallAtIndex(index);
      if (!b?.active || Math.hypot(p.x-b.position.x,p.y-b.position.y,p.z-b.position.z)>q.radius+b.radius+PCOLCore.TOUCH_EPS*2) watch.initial=false;
    }
    return row;
  }
  function recordSolvedContact(s, contact, ix, iy, iz, jx, jy, jz, closeSpeed) {
    const shot=s.shot;
    if (!shot?.physical || s.predicting || !(closeSpeed < -1e-6)) return;
    const q=contact.bi.number===0?contact.bi:contact.isSS && contact.bj.number===0?contact.bj:null;
    if (!contact.isSS) {
      const normal=contact.normal || contact.bj.normal;
      if (!q || contact.bj.end || contact.bj.tunnel || !normal || Math.abs(normal.y)>=.7) return;
      const gained=(q.v.x-ix)*normal.x+(q.v.y-iy)*normal.y+(q.v.z-iz)*normal.z;
      if (!(gained>1e-7)) return;
      const row=sample(s); if (!row) return;
      shot.contacts.push({t:row.t,kind:'cushion',evolution:s.g._simulator._world.evolution,x:row.x,y:row.y,z:row.z});
      for (const item of shot.touchWatches.values()) item.initial=false;
      return;
    }
    if (!q) {
      // A later ball can move the originally touching object without making
      // the initial play-away a push stroke. Track the source of the motion.
      const i=contact.bi,j=contact.bj;
      if(Math.hypot(i.v.x-ix,i.v.y-iy,i.v.z-iz)>1e-7){const watch=shot.touchWatches.get(i.index);if(watch)watch.initial=false;}
      if(Math.hypot(j.v.x-jx,j.v.y-jy,j.v.z-jz)>1e-7){const watch=shot.touchWatches.get(j.index);if(watch)watch.initial=false;}
      return;
    }
    const cueIsI=q===contact.bi,obj=cueIsI?contact.bj:contact.bi;
    const dx=obj.position.x-q.position.x,dy=obj.position.y-q.position.y,dz=obj.position.z-q.position.z;
    const length=Math.hypot(dx,dy,dz);
    const gained=length?((obj.v.x-(cueIsI?jx:ix))*dx+(obj.v.y-(cueIsI?jy:iy))*dy+(obj.v.z-(cueIsI?jz:iz))*dz)/length:0;
    if (!(gained>1e-7)) return;
    const row=sample(s); if (!row) return;
    const watch=shot.touchWatches.get(obj.index);
    const initialPush=watch?.initial;
    if (initialPush && !shot.pushedTouching.includes(obj.index)) shot.pushedTouching.push(obj.index);
    const before=shot.before;
    const target=before.context.ballOn===252 && before.nominatedColour?2**before.nominatedColour:before.context.ballOn;
    const allowed=before.touching.deemedHit || obj.index===before.freeBallNominee || PCOLCore.ballOnNumbers(target).includes(obj.number);
    const firstLegal=!shot.contacts.some(c=>c.ballIndex!=null && c.legal===false);
    shot.contacts.push({t:row.t,ballIndex:obj.index,evolution:s.g._simulator._world.evolution,x:row.x,y:row.y,z:row.z,legal:allowed && firstLegal});
    // Any subsequent rebound/cannon is no longer the initial striking action.
    if (!initialPush) for (const item of shot.touchWatches.values()) item.initial=false;
  }
  function aiColour(s, controller) {
    const m = s.g._model;
    if (m._gContext.ballOn !== 252) return;
    if(s.opponent?.getStatus().enabled && s.nominatedColour)return;
    const chosen = s.aiTarget;
    if (chosen != null && s.g._simulator.getBallAtIndex(chosen)?.number > 1) {
      s.nominatedColour = s.g._simulator.getBallAtIndex(chosen).number; return;
    }
    const dir = controller.getKissDir(), cue = s.g._simulator.getCueBallPosition();
    const choices = balls(s.g).filter(b => b.active && b.n > 1);
    choices.sort((a, b) => {
      const cost = p => { const dx = p.x - cue.x, dz = p.z - cue.z, l = Math.hypot(dx, dz); return 1 - (dx * dir.x + dz * dir.z) / (l || 1); };
      return cost(a) - cost(b);
    });
    s.nominatedColour = choices[0]?.n || 7;
  }
  function hookAI(s, ai) {
    if (!ai || s.aiHooks.has(ai)) return ai;
    s.aiHooks.add(ai);
    if (ai.checkRestart) wrap(ai,'checkRestart',original=>function(...args){
      const changed=original.apply(this,args);
      if(changed)s.opponent?.reset();
      return changed;
    },s.scenePatches);
    wrap(ai, 'step', original => function (...args) {
      if(s.opponent?.getStatus().enabled && s.ensureAITurn?.())return null;
      const result = s.getOpponent().step(this,original,args);
      if(result&&s.opponent.getStatus().enabled){
        const ctl=s.g._playerCtls.find(c=>c._ai===this);
        if(ctl&&!s.deliveryHooks.has(ctl)){
          s.deliveryHooks.add(ctl);
          // The native AI hardcodes setTipPercent(0,fbSpin). Render the prepared
          // side spin and launch the exact compiled vector used by the trial.
          wrap(ctl._stickCtl,'setTipPercent',original=>function(side,vertical){
            return original.call(this,s.opponent.getDelivery()?.shot.side??side,vertical);
          },s.scenePatches);
          wrap(ctl,'getStrokeVars',original=>function(...args){
            return s.opponent.getDelivery()?.stroke.slice()||original.apply(this,args);
          },s.scenePatches);
        }
      }
      if (result) s.aiTarget = Number.isInteger(result.ballBIndex) ? result.ballBIndex : null;
      return result;
    },s.scenePatches);
    return ai;
  }
  function restartAI(s) {
    const g=s.g;
    if(g._model._gState!==4)return;
    for(const ctl of g._playerCtls)if(ctl._ai && ctl.gPlayerIndex===g._model._gContext.playerIndex){
      ctl._shootingDelay=-1;ctl._aiThinkingRandomDelay=0;
      ctl.gotoState0(true);ctl._ai._simEvolution=-1;ctl._ai.checkRestart(g._simulator,g._model);
    }
  }
  function enableLocalAI(s,enabled) {
    s.afterAnnotation=null;
    s.getOpponent().setEnabled(enabled);
    syncAimGuide(s);
    s.turnManager?.cancel();s.preparedShot=null;s.aiPreparedMark=null;
    if(!enabled && s.pending && s.g._model._gContext.playerIndex!==s.g._fpc.gPlayerIndex)resolveFoul(s,'continue');
    if(!s.shot)restartAI(s);render(s);
    return enabled;
  }
  function localAIError(s,error) {
    recordEvent(s,'decision.error',{message:error.message});
    if(/position changed|decision is stale/i.test(error.message)){
      s.turnManager?.cancel();s.opponent?.reset();restartAI(s);return;
    }
    if(s.modal || s.app._currentController!==s.g)return;
    dialog(s,'对手暂停',error.message,[
      ['重试选杆',()=>{closeModal(s);s.turnManager?.cancel();s.opponent.reset();restartAI(s);s.ensureAITurn?.();},true],
      ['关闭提示',()=>closeModal(s)]
    ],'当前出杆已停止。重试会重新检查球局并搜索候选。');
  }
  function dismissiblePanel(s,panel) {
    const close=document.createElement('button');close.type='button';close.className='dismiss-dialog';close.textContent='×';close.setAttribute('aria-label','关闭');close.title='关闭（Esc）';close.onclick=()=>closeModal(s);panel.append(close);
    panel.addEventListener('keydown',e=>{
      if(e.key==='Escape'){e.preventDefault();closeModal(s);}
      if(e.key==='Tab'){
        const buttons=[...panel.querySelectorAll('button:not(:disabled)')],first=buttons[0],last=buttons[buttons.length-1];
        if(e.shiftKey&&s.shadow.activeElement===first){e.preventDefault();last.focus();}
        else if(!e.shiftKey&&s.shadow.activeElement===last){e.preventDefault();first.focus();}
      }
    });
  }
  function showOpponent(s) {
    const fromHome=s.app._currentController===s.app._controllers.home;
    const panel=dialog(s,'本地 AI 对局',fromHome?'选择击球准度，直接开局。AI 根据球局自主比较进攻与防守。':'调整击球准度，新设置用于后续选杆。',[]);
    panel.classList.add('opponent-panel');panel.querySelector('.choices').remove();dismissiblePanel(s,panel);
    const summary=document.createElement('div');summary.className='ai-summary';
    summary.innerHTML='<div><strong>本地 AI</strong><small>根据球局比较进攻、走位、拆球与防守</small></div><span class="local-badge">本机选杆</span>';panel.append(summary);
    const skillLabels={club:'俱乐部',strong:'高手',expert:'专家'};
    const descriptions={club:'更宽的击球误差；隐藏目标球黄色扇面',strong:'适中的击球误差',expert:'更小的击球误差'};
    const current=document.createElement('div');current.className='current-setting';current.setAttribute('aria-live','polite');
    const refresh=()=>{
      syncAimGuide(s);
      current.textContent='当前准度：'+skillLabels[s.aiSettings.skill]+' · 自主战术判断';
      for(const b of panel.querySelectorAll('[data-setting]'))b.setAttribute('aria-pressed',String(s.aiSettings[b.dataset.setting]===b.dataset.value));
      render(s);
    };
    for(const [key,label,caption,values] of [['skill','击球准度','影响瞄准、力度和杆法稳定性',skillLabels]]){
      const section=document.createElement('section');section.className='setting-section';
      const heading=document.createElement('div');heading.className='section-heading';heading.innerHTML='<h3>'+label+'</h3><span>'+caption+'</span>';
      const group=document.createElement('div');group.className='setting-options';group.setAttribute('role','group');group.setAttribute('aria-label',label);
      for(const [value,text] of Object.entries(values)){
        const b=document.createElement('button');b.type='button';b.className='setting-option';b.dataset.setting=key;b.dataset.value=value;
        b.innerHTML='<strong>'+text+'</strong><small>'+descriptions[value]+'</small>';
        b.onclick=()=>{if(s.aiSettings[key]===value)return;s.aiSettings[key]=value;s.turnManager?.cancel();s.opponent?.reset();s.preparedShot=null;s.aiPreparedMark=null;if(!s.shot)restartAI(s);recordEvent(s,'settings',{...s.aiSettings});refresh();};group.append(b);
      }section.append(heading,group);panel.append(section);
    }
    panel.append(current);
    const note=document.createElement('div');note.className='note';note.textContent=fromHome?'默认高手准度。三档共用同一套战术判断，对局中也可以调整。':'设置用于后续选杆，已经击出的球不受影响。';panel.append(note);
    const footer=document.createElement('div');footer.className='settings-footer';
    const back=document.createElement('button');back.type='button';back.textContent=fromHome?'返回':'关闭设置';back.onclick=()=>closeModal(s);footer.append(back);
    const done=document.createElement('button');done.type='button';done.className='primary';done.textContent=fromHome?'开始对局 →':'继续对局';done.onclick=()=>{closeModal(s);if(fromHome)startEnhancedGame(s);};footer.append(done);panel.append(footer);
    refresh();done.focus();
  }
  function showRecording(s) {
    const r=s.recorder.getStatus();
    const message=r.error?(r.failed?`本次有 ${r.failed} 条记录未能保存；已保存记录可导出。`:'本机保存失败，请保留页面并重试。'):!r.enabled?'自动记录已暂停。':r.pending?'已保存在当前浏览器；本地服务恢复后会自动补同步。':'自动记录球局、选杆与结果，保存在当前浏览器。';
    const panel=dialog(s,'比赛记录',message,[]);panel.querySelector('.choices').remove();dismissiblePanel(s,panel);
    const grid=document.createElement('div');grid.className='record-grid';
    for(const [label,value] of [['本机累计已保存',r.localSaved],['待同步',r.pending],['正在保存',r.saving]]){const stat=document.createElement('div');stat.className='record-stat';stat.innerHTML='<strong>'+value+'</strong><span>'+label+'</span>';grid.append(stat);}panel.append(grid);
    const note=document.createElement('div');note.className='note';note.textContent='无需启动服务即可保存和导出。刷新页面后记录仍在；清除网站数据会删除浏览器记录。';panel.append(note);
    const footer=document.createElement('div');footer.className='settings-footer';
    const toggle=document.createElement('button');toggle.type='button';toggle.textContent=r.enabled?'暂停记录':'开启记录';toggle.setAttribute('aria-pressed',String(r.enabled));toggle.onclick=()=>{s.recorder.setEnabled(!r.enabled);showRecording(s);};footer.append(toggle);
    const exportButton=document.createElement('button');exportButton.type='button';exportButton.textContent='导出 JSONL';exportButton.onclick=async()=>{exportButton.disabled=true;try{await s.recorder.download();}catch(_){note.textContent='导出失败，请重试。';}finally{exportButton.disabled=false;}};footer.append(exportButton);
    const retry=document.createElement('button');retry.type='button';retry.textContent='重试保存与同步';retry.disabled=!r.pending&&!r.error;retry.onclick=async()=>{retry.disabled=true;await s.recorder.flush();if(panel.isConnected)showRecording(s);};footer.append(retry);
    const done=document.createElement('button');done.type='button';done.className='primary';done.textContent='完成';done.onclick=()=>closeModal(s);footer.append(done);panel.append(footer);done.focus();
  }
  function resetTurn(s) { s.afterAnnotation=null;s.turnManager?.cancel();s.aiPreparedMark=null;s.preparedShot=null;s.nominatedColour = null; s.nominationSource = null; s.freeBallNominee = null; s.freeBallAvailable = false; s.freeBallReview = false; s.freeBallDeclined = false; s.aiTarget = null; }
  function updateFreeBall(s, result) {
    if (!(result.score < 0) || !s.g._model._gContext.ballOn) return;
    const m = s.g._model, sim = s.g._simulator;
    const options = m._gContext.inHand > 0 ? { inHand: true } : {};
    const bs = balls(s.g);
    let test = PCOLCore.isSnookered(bs, m._gContext.ballOn, undefined, options);
    if (options.inHand) {
      const d = m._locRef._dArea, radius = sim.ballRadius;
      // A single legal clear position disproves a snooker in hand. Failure to
      // find one is NOT proof; that case remains an explicit referee decision.
      search: for (let ring = 0; ring <= 8; ring++) for (let j = 0; j <= 32; j++) {
        const angle = -Math.PI / 2 + j * Math.PI / 32, distance = d._radius * ring / 8;
        const cue = { x: d._center.x + distance * (d._arcDir.x * Math.cos(angle) + d._diameterDir.x * Math.sin(angle)), y: d._center.y + radius, z: d._center.z + distance * (d._arcDir.z * Math.cos(angle) + d._diameterDir.z * Math.sin(angle)), r: radius };
        if (bs.some(b => b.active && b.n > 0 && Math.hypot(b.x-cue.x,b.z-cue.z) <= 2 * radius + 1e-6)) continue;
        const candidate = PCOLCore.isSnookered(bs, m._gContext.ballOn, cue);
        if (candidate.snookered === false) { test = { ...candidate, inHandWitness: cue }; break search; }
      }
    }
    s.freeBallAvailable = test.snookered === true;
    s.freeBallReview = test.snookered == null;
    s.freeBallAssessment = test;
  }
  function syncResponse(s, result) {
    const m = s.g._model, sim = s.g._simulator;
    m._response(sim, result);
  }
  function startBlackDecider(s) {
    const g=s.g,m=g._model,sim=g._simulator;
    const black=sim.getBalls().find(b=>b.number===7);
    // Move White first so it cannot occupy the Black spot during re-spotting.
    m._locRef._liveRespotCueBall(sim);
    sim.respotIndexDefault(black.index);
    for(const player of m._players)player.brk=0;
    Object.assign(m._gContext,{ballOn:128,inHand:2});
    s.concessionTurn=null;
    const drawWinnerIndex=Math.random()<.5?0:1;
    s.blackDecider={drawWinnerIndex,firstPlayerIndex:null};
    const label=index=>s.hotseat?`玩家 ${index+1}`:index===g._fpc.gPlayerIndex?'你':'对手';
    const start=firstPlayerIndex=>{
      s.blackDecider.firstPlayerIndex=firstPlayerIndex;
      m._gContext.playerIndex=firstPlayerIndex;
      s.opponent?.reset();
      for(const ctl of g._playerCtls)if(ctl._ai)ctl._ai._simEvolution=-1;
      s.log.push({kind:'respotted-black',...s.blackDecider,score:scores(m)});
      closeModal(s);
      syncResponse(s);
    };
    const humanChooses=s.hotseat || drawWinnerIndex===g._fpc.gPlayerIndex;
    const choices=humanChooses?[
      [s.hotseat?`${label(drawWinnerIndex)}先击球`:'我先击球',()=>start(drawWinnerIndex),true],
      [s.hotseat?`${label(1-drawWinnerIndex)}先击球`:'让对手先击球',()=>start(1-drawWinnerIndex)]
    ]:[['开始争黑',()=>start(drawWinnerIndex),true]];
    dialog(s,'平局争黑',`比分 ${scores(m).join(' : ')}。${label(drawWinnerIndex)}赢得抽签${humanChooses?'，请选择谁先击球':'并选择先击球'}。黑球重放点位，先手从 D 区手中球开始；首次进球或犯规结束本局。`,choices);
  }
  function resolveFoul(s, action) {
    const pending = s.pending;
    if (!pending) return false;
    if (action === 'restore' && !pending.miss) return false;
    const m = s.g._model, sim = s.g._simulator, gctx = m._gContext;
    s.pending = null;
    closeModal(s);
    resetTurn(s);
    if (action === 'restore') {
      sim._world.restore(pending.before.serial);
      sim._world.accumulator = 0;
      sim._nPhxAwakened = sim._world.nAwakened;
      for (const b of sim.getBalls()) b.syncStates(0);
      s.g._gView.syncBalls(sim.getBalls(), sim.evolution);
      sim.clearResult();
      gctx.playerIndex = pending.offender;
      gctx.ballOn = pending.before.context.ballOn;
      gctx.inHand = pending.before.context.inHand;
    } else if (action === 'again') {
      gctx.playerIndex = pending.offender;
      gctx.ballOn = pending.before.context.ballOn;
      if (gctx.ballOn === 2 && !balls(s.g).some(b => b.active && b.n === 1)) gctx.ballOn = 4;
    } else if (action === 'continue') {
      // Commit the incoming turn's canonical target at the decision boundary,
      // before any free-ball nomination or controller/UI response can use it.
      gctx.ballOn = pending.result.nextBallOn;
      updateFreeBall(s, pending.result);
    } else throw new Error('Unknown foul decision');
    for (const c of s.g._playerCtls) if (c._ai) c._ai._simEvolution = -1;
    s.log.push({ kind: 'decision', action, offender: pending.offender, playerIndex:gctx.playerIndex, ballOn:gctx.ballOn, freeBallAvailable:s.freeBallAvailable, restoredWholeTable: action === 'restore', score: scores(m) });
    recordEvent(s,'foul.choice',{action,offender:pending.offender,after:recordState(s),triggerTurnId:s.lastStrokeRecord?.turnId},
      {strokeId:s.lastStrokeRecord?.id,turnId:s.currentTurnId||s.lastStrokeRecord?.turnId});
    s.currentTurnId=null;s.currentDecisionId=null;
    if(awardEarlyFrame(s,pending.offender,false))return true;
    syncResponse(s);
    offerConcession(s, pending.offender);
    return true;
  }
  function offerFoul(s) {
    const p = s.pending, m = s.g._model;
    if (m._gContext.playerIndex !== s.g._fpc.gPlayerIndex) {
      if(s.opponent?.getStatus().enabled){s.ensureAITurn();return;}
      // AI elects to play the current position; the choice is explicit and recorded.
      resolveFoul(s, 'continue'); return;
    }
    const choices = [
      [`${s.hotseat ? actor(s) : '我'}接手（打${ballOnLabel(p.result.nextBallOn)}）`, () => resolveFoul(s, 'continue'), true],
      [s.hotseat ? `玩家 ${p.offender + 1} 从现位置继续` : '对手从现位置继续', () => resolveFoul(s, 'again')]
    ];
    if (p.miss) choices.push(['复位后让对手重打', () => resolveFoul(s, 'restore')]);
    if (p.reviewMiss) choices.push(['裁判确认空杆并复位', () => { p.miss = true; s.log.push({ kind: 'referee-miss-confirmation' }); resolveFoul(s, 'restore'); }]);
    dialog(s, p.miss ? '犯规与空杆' : '犯规', `${description(p.result.foulCode)}。${actor(s)}获得 ${-p.result.score} 分。请选择下一杆的处理方式。`, choices,
      p.reviewMiss ? '本杆处于遮挡局面，是否已尽力解球需要裁判判断；“裁判确认”是人工判罚，不是自动检测结果。' : p.miss ? '复位恢复本杆前整桌球形；已经判给你的罚分保留。' : '现位置重打保留当前球形。');
  }
  function finishStroke(s, jumpDecision) {
    const g = s.g, m = g._model, sim = g._simulator, shot = s.shot;
    if (!shot) throw new Error('No pre-stroke snapshot');
    sample(s);
    shot.physical = false;
    const firstContact = shot.contacts.find(c => c.ballIndex != null);
    const firstHits = firstContact ? [...new Set(shot.contacts.filter(c => c.ballIndex != null && c.evolution === firstContact.evolution && Math.hypot(c.x-firstContact.x,c.y-firstContact.y,c.z-firstContact.z)<1e-5).map(c => c.ballIndex))] : [];
    const oldMask = shot.before.context.ballOn;
    const jump = PCOLCore.evaluateJump(shot.trace, shot.before.balls, shot.contacts, sim.ballRadius);
    if ((jump.indeterminate || shot.overflow) && !jump.foul && jumpDecision === undefined) {
      dialog(s, '腾空轨迹需要裁判确认', '本杆的落地或接触情况处在自动判定边界，请确认是否属于非法跳球。判定期间比赛暂停。', [
        ['未发生非法跳球', () => { closeModal(s); finishStroke(s, false); }, true],
        ['裁判确认跳球犯规', () => { closeModal(s); finishStroke(s, true); }]
      ]);
      return m;
    }
    if (jumpDecision !== undefined) { jump.refereeDecision = jumpDecision; s.log.push({ kind: 'referee-jump-confirmation', foul: jumpDecision }); }
    const result = PCOLCore.adjudicate({ ballOn: oldMask, nominatedColour: shot.before.nominatedColour, freeBallNominee: shot.before.freeBallNominee, balls: balls(g), firstHits, potted: [...sim.result.pottedIndices], outOfBounds: [...sim.result.outOfBoundsIndices], jumpFoul: jump.foul || jumpDecision === true, touchingAtStart:shot.before.touching.indices, pushedTouching:shot.pushedTouching,cueStrikes:shot.cueStrikes });
    const ctx = m._gContext, offender = ctx.playerIndex, breakBefore = m._players[offender].brk;
    ctx.ballOn = result.nextBallOn;
    ctx.inHand = result.requiresInHand ? 2 : 0;
    sim._world.useStrictMode = true;
    if (result.respots.length) m._locRef._liveRespot(result.respots, [], sim);
    if (result.requiresInHand) m._locRef._liveRespotCueBall(sim);
    // Rebuild contact islands after spotting, exactly as the simulator's normal response does.
    const judgement = m._refResult;
    judgement.score = result.score; judgement.foulCode = result.foulCode;
    ctx.nRounds++;
    if (result.score > 0) { m._players[offender].pts += result.score; m._players[offender].brk += result.score; m._players[offender].scoreCount++; }
    else { m._players[offender].penalty += result.score; m._players[offender].brk = 0; ctx.playerIndex = (offender + 1) % m._players.length; }
    const breakScore=m._players[offender].brk;
    if ((breakBefore < 100 && breakScore >= 100) ||
        (breakScore === 147 && breakBefore < 147) || (breakScore === 155 && breakBefore < 155)) {
      s.celebration.show({ playerLabel: s.hotseat ? `玩家 ${offender + 1}` : m._players[offender].displayName, breakScore });
    }
    const blackFrame=PCOLCore.blackFrameOutcome({ballOn:oldMask,balls:shot.before.balls,score:result.score,scores:scores(m),respottedBlack:!!s.blackDecider});
    if(blackFrame){
      result.frameOutcome=blackFrame;
      result.continueBreak=false;
      if(blackFrame==='respot'){
        result.nextBallOn=ctx.ballOn=128;
        result.requiresInHand=true;ctx.inHand=2;
      }else{ctx.ballOn=0;ctx.inHand=0;s.blackDecider=null;}
    }
    recordCompletedStroke(s,shot,{...result,jump,firstHits});
    if(blackFrame==='respot'){startBlackDecider(s);requestRender(s);return m;}
    if(result.score>=0&&awardEarlyFrame(s,offender,result.continueBreak)){requestRender(s);return m;}
    if (result.score < 0 && ctx.ballOn && m._players.length > 1) {
      const mask = oldMask === 252 && shot.before.nominatedColour ? 2 ** shot.before.nominatedColour : oldMask;
      const direct = PCOLCore.hasDirectHit(shot.before.balls, mask);
      const maximum = PCOLCore.remainingPoints(shot.before.balls, oldMask);
      const beforeDiff = Math.abs(shot.before.scores[0] - shot.before.scores[1]);
      const afterScores = scores(m), afterDiff = Math.abs(afterScores[0] - afterScores[1]);
      const afterMaximum = PCOLCore.remainingPoints(balls(g), ctx.ballOn);
      const needsSnookers = beforeDiff > maximum || afterDiff > afterMaximum;
      const wrongFirst = Boolean(result.foulCode & 3);
      s.pending = { offender, before: shot.before, result, miss: wrongFirst && !needsSnookers && direct.hasDirectHit === true, reviewMiss: wrongFirst && !needsSnookers && direct.hasDirectHit !== true };
      // Freeze before _response activates the next controller; AI cannot shoot behind the dialog.
      const previousPaused = g._paused;
      g._paused = true;
      syncResponse(s, judgement);
      g._paused = previousPaused;
      offerFoul(s);
      g._uiLayer?.closeMessage();
    } else { syncResponse(s, judgement); offerConcession(s, offender); }
    requestRender(s);
    return m;
  }
  function attach(app, require) {
    if (active?.app === app) return active;
    if (active) throw new Error('A different PCOL instance is already attached');
    if (app.constructor.VERSION !== '0.1.0.03152018') throw new Error('Unsupported PCOL build');
    const g = app._controllers.game, m = g._model, sim = g._simulator, world = sim._world;
    if (!m.reportPlayerStroke || !world.serialize || !world.restore || !world.internalStep) throw new Error('PCOL structure changed');
    const s = active = { app, g, hotseat: false, requestedHotseat: false, shot: null, predicting: 0, nominatedColour: null, freeBallNominee: null, freeBallAvailable: false, freeBallDeclined: false, pending: null, modal: false, conceded: null, concessionTurn: null, blackDecider: null, aiHooks: new WeakSet(), log: [], lastTrace: [], lastContacts: [] };
    s.celebration = PCOLCelebration.create({ document, window, host: document.documentElement });
    s.practice=null;s.requestedPractice=null;s.practiceBefore=null;s.practiceLayout=null;s.openEditorOnReady=false;s.placement=null;s.practiceControlsHidden=false;s.refHooks=new WeakSet();s.deliveryHooks=new WeakSet();
    s.scenePatches=[];s.interactingUntil=0;
    hookColourRespots(s);
    API.app = app;
    let trial = null, search = null, localAI = null;
    s.aiSettings={skill:'strong',engine:'local'};s.requestedEnhanced=false;
    // Local durable writes remain immediate; only optional background upload waits.
    const interacting=()=>{s.interactingUntil=performance.now()+750;};
    const inputEvents=['pointermove','pointerdown','wheel','keydown'];
    for(const name of inputEvents)window.addEventListener(name,interacting,{passive:true});
    s.recorder=DEVELOPMENT?PCOLMatchRecorder.create({version:VERSION,
      isBusy:()=>!!s.shot?.physical||performance.now()<s.interactingUntil,
      onChange:()=>renderRecording(s)}):null;
    const getTrial = () => trial || (trial = PCOLTrial.create({game:g,factories:require.m,
      isReady:() => app._currentController===g && m._gState===4 && !s.shot && (!s.modal||s.modalKind==='annotation') && !s.placement && (!s.pending||s.turnManager?.getStatus().busy) && !s.conceded && !s.frameEnd,
      getRules:() => ({...m._gContext,nominatedColour:s.nominatedColour,nominationSource:s.nominationSource,freeBallNominee:s.freeBallNominee,
        freeBallAvailable:s.freeBallAvailable,freeBallReview:s.freeBallReview,freeBallDeclined:s.freeBallDeclined,scores:scores(m),respottedBlack:!!s.blackDecider})}));
    API.trial = {snapshot:() => getTrial().snapshot(),compile:shot => getTrial().compile(shot),
      simulate:(shot,options) => getTrial().simulate(shot,options),simulateAim:options => getTrial().simulateAim(options),
      simulateFrom:(parent,shot,options) => getTrial().simulateFrom(parent,shot,options),
      cancel:() => trial?.cancel(),getStatus:() => trial?.getStatus() || {busy:false,initialized:false,lastResult:null}};
    const getSearchState=before => {
        const ground=sim.ground;
        const d=m._locRef._dArea;
        const current=before.balls.map(b=>({i:b.i,n:b.n,r:b.r,active:b.active,x:b.x,y:b.y,z:b.z}));
        return {balls:current,rules:before.rules,touching:PCOLCore.touchingStatus({balls:current,...before.rules}),
          ...s.aiSettings,scores:before.rules.scores,remainingPoints:PCOLCore.remainingPoints(current,before.rules.ballOn),
          dArea:d&&{center:{x:d._center.x,y:sim.spotY,z:d._center.z},arcDir:{x:d._arcDir.x,z:d._arcDir.z},diameterDir:{x:d._diameterDir.x,z:d._diameterDir.z},radius:d._radius},
          pockets:g._gView.playArea.pockets.map(p=>({x:p.position.x,z:p.position.z,r:p.radius,
            normal:{x:p.normal.x,z:p.normal.z},maxHalfOpen:p.maxHalfOpen})),
          bounds:{minX:ground.centerPosition.x-ground.size.x/2,maxX:ground.centerPosition.x+ground.size.x/2,
            minZ:ground.centerPosition.z-ground.size.z/2,maxZ:ground.centerPosition.z+ground.size.z/2}};
      };
    const makeSearch = adapter => PCOLSearch.create({getTrial:()=>adapter||getTrial(),geometry:PCOLSearchGeometry,
      policy:PCOLTacticalPolicy,brain:PCOLTacticalBrain,skill:PCOLShotSkill,getState:getSearchState,development:PCOLDevelopment,
      continuation:PCOLContinuation.create({geometry:PCOLSearchGeometry,policy:PCOLTacticalPolicy,core:PCOLCore,development:PCOLDevelopment,skill:PCOLShotSkill})});
    // The standalone localhost arena owns its controller; no new player logic runs on the original site.
    if(DEVELOPMENT && ['127.0.0.1','localhost'].includes(window.location.hostname) && new URLSearchParams(window.location.search).has('codexArena'))
      API.codexHost={version:VERSION,build:BUILD_ID,getTrial,makeSearch,getState:getSearchState,
        captureInitial:()=>{if(m._players.length!==2||m._gContext.ballOn!==2||!sim.ground)throw new Error('Initial table not ready');
          return PCOLTrial.create({game:g,factories:require.m,isReady:()=>true,
            getRules:()=>({...m._gContext,scores:scores(m),nominatedColour:null,nominationSource:null,freeBallNominee:null,freeBallAvailable:false,freeBallReview:false,freeBallDeclined:false,respottedBlack:false})}).snapshot();},
        skill:PCOLShotSkill,core:PCOLCore,geometry:PCOLSearchGeometry,policy:PCOLTacticalPolicy,brain:PCOLTacticalBrain,
        development:PCOLDevelopment,turnOptions:PCOLTurnOptions.create({geometry:PCOLSearchGeometry,core:PCOLCore}),
        createClient:PCOLLocalAI.create,createTurnManager:PCOLTurnManager.create,
        freeze:()=>{g._paused=true;s.frameMonitor?.dispose();s.recorder?.dispose();s.recorder=null;s.recordingFrame=false;s.host?.remove();},game:g};
    s.assessPlan=(expected,after)=>PCOLTacticalBrain.compliance(getSearchState(after||{balls:balls(g),rules:{...m._gContext,scores:scores(m)}}),expected,PCOLSearchGeometry);
    const getSearch = () => search || (search = makeSearch());
    API.search = {run:options=>getSearch().run(options),cancel:()=>search?.cancel(),
      getStatus:()=>search?.getStatus() || {busy:false,lastResult:null}};
    const localTools=DEVELOPMENT && ['127.0.0.1','localhost'].includes(window.location.hostname);
    if(localTools)API.bench=PCOLBench.create({version:VERSION,getTrial,makeSearch,getState:getSearchState,skill:PCOLShotSkill,
      capture:()=>{const snapshot=getTrial().snapshot();return {snapshot,state:getSearchState(snapshot)};}});
    if(localTools)API.arena=PCOLArena.create({version:VERSION,build:BUILD_ID,getTrial,makeSearch,getState:getSearchState,
      capture:()=>({snapshot:getTrial().snapshot()}),skill:PCOLShotSkill,core:PCOLCore,geometry:PCOLSearchGeometry,policy:PCOLTacticalPolicy,
      turnOptions:PCOLTurnOptions.create({geometry:PCOLSearchGeometry,core:PCOLCore}),
      createRecorder:PCOLMatchRecorder.create,createClient:PCOLLocalAI.create,createTurnManager:PCOLTurnManager.create});
    s.recordAIOutcome=result=>localAI?.recordOutcome(result);
    s.getLocalAI = () => localAI || (localAI = PCOLDecisionClient.create({getTrial,getState:getSearchState,onChange:()=>requestRender(s),
      onEvent:(kind,data)=>recordEvent(s,kind,data),
      getContext:()=>({ballOn:m._gContext.ballOn,playerIndex:m._gContext.playerIndex,nRounds:m._gContext.nRounds,scores:scores(m),
        nominatedColour:s.nominatedColour,freeBall:{available:s.freeBallAvailable,nominee:s.freeBallNominee},
        skill:s.aiSettings.skill,lastOutcome:s.lastResult&&{actor:s.lastBefore?.context.playerIndex,round:m._gContext.nRounds,score:s.lastResult.score,foulCode:s.lastResult.foulCode},
        remainingPoints:PCOLCore.remainingPoints(balls(g),m._gContext.ballOn),breakScore:m._players[m._gContext.playerIndex]?.brk||0,
        balls:balls(g).filter(b=>b.active).map(b=>({i:b.i,n:b.n,x:b.x,z:b.z}))})}));
    s.getOpponent = () => s.opponent || (s.opponent = PCOLLocalOpponent.create({game:g,
      decide:async()=>{
        let result;
        if(s.preparedShot){result=s.preparedShot;s.preparedShot=null;}
        else{beginDecision(s);result=await s.getLocalAI().decide();}
        considerAIConcession(s,getSearchState(getTrial().snapshot()),result);
        return result;
      },getSnapshot:()=>getTrial().snapshot(),cancelDecision:()=>localAI?.cancel(),
      prepareCandidate:candidate=>{
        const shot=PCOLShotSkill.perturb(candidate.shot,candidate.skill);
        const compiled=getTrial().compile(shot);
        s.getLocalAI().rememberDelivery(getTrial().snapshot(),candidate,shot);
        recordEvent(s,'stroke.prepared',{candidateId:candidate.id,targetIndex:candidate.targetIndex,
          nominalShot:candidate.shot,actualShot:shot,stroke:compiled.stroke,expected:candidate.outcome,risk:candidate.risk});
        return {...candidate,shot,stroke:compiled.stroke,actual:compiled.actual};
      },
      nominate:candidate=>{
        if(m._gContext.ballOn===252){s.nominatedColour=candidate.nominatedColour||candidate.outcome.nominatedColour;s.nominationSource='manual';}
      },
      canThink:()=>app._currentController===g && m._gState===4 && thinkingAllowed(s) && !s.pending && !s.conceded && !s.frameEnd && !s.hotseat && !s.turnManager?.getStatus().busy &&
        m._gContext.playerIndex!==g._fpc.gPlayerIndex && !sim.getBalls().some(b=>b.active&&!b.asleep),
      canDeliver:()=>app._currentController===g && m._gState===4 && !g._paused && !s.modal && !s.pending && !s.conceded && !s.frameEnd &&
        !s.hotseat && m._gContext.playerIndex!==g._fpc.gPlayerIndex && !sim.getBalls().some(b=>b.active&&!b.asleep),
      onChange:()=>requestRender(s),onError:error=>localAIError(s,error)}));
    s.turnManager=s.getLocalAI().createTurnManager({getPending:()=>s.pending,
      commit:(choice,kind,reason,source)=>afterAnnotation(s,()=>{
        if(kind==='foul'){recordEvent(s,'turn.choice',{kind,choiceId:choice.id,action:choice.action,reason,source});s.log.push({kind:'ai-foul-choice',action:choice.action,reason});resolveFoul(s,choice.action);return;}
        if(choice.position){
          const p=choice.position;
          if(!m._locRef.projectionInSideValidRegion(p.x,p.y,p.z)||sim.touchBalls(0,p))throw new Error('AI cue placement is no longer legal');
          m.reqRespotCueball({x:p.x,y:sim.spotY,z:p.z},sim);
        }
        s.freeBallNominee=choice.nominee??null;s.freeBallDeclined=choice.nominee==null;
        if(choice.state.rules.nominatedColour){s.nominatedColour=choice.state.rules.nominatedColour;s.nominationSource='manual';}
        if(choice.candidate?.nominatedColour){s.nominatedColour=choice.candidate.nominatedColour;s.nominationSource='manual';}
        s.aiPreparedMark=m._gContext.nRounds+':'+m._gContext.playerIndex;
        if(choice.candidate)s.preparedShot={candidate:choice.candidate,reason,source};
        recordEvent(s,'turn.choice',{kind,choiceId:choice.id,position:choice.position,nominee:choice.nominee,reason,source});
        s.log.push({kind:'ai-turn-choice',decision:kind,position:choice.position,freeBallNominee:s.freeBallNominee,reason});
        restartAI(s);
      }),onError:error=>localAIError(s,error),onChange:()=>requestRender(s)});
    s.frameMonitor=PCOLFrameMonitor.create({window,getPhase:()=>s.shot?.physical?'realshot':
      s.turnManager.isBusy()?'turn':localAI?.isBusy()?'ai':'idle',
      onReport:report=>recordEvent(s,'performance.frame',report)});
    if(API.codexHost)API.codexHost.getDecisionClient=()=>s.getLocalAI();
    s.ensureAITurn=()=>{
      if(!s.opponent?.getStatus().enabled||s.hotseat||app._currentController!==g||m._gState!==4||!thinkingAllowed(s)||s.shot||s.conceded||s.frameEnd||m._gContext.playerIndex===g._fpc.gPlayerIndex)return false;
      if(s.turnManager.getStatus().busy||s.turnManager.getStatus().failed||s.afterAnnotation)return true;
      if(s.freeBallReview){
        if(s.modalKind==='annotation')return true;
        dialog(s,'AI 手中球的自由球判定','D 区自由球判定尚不确定，请裁判确认后由 AI 自行选球。',[
          ['不判自由球',()=>confirmFreeBall(s,false),true],
          ['判自由球',()=>confirmFreeBall(s,true)]
        ]);return true;
      }
      const mark=m._gContext.nRounds+':'+m._gContext.playerIndex;
      const needs=s.pending||(m._gContext.inHand>0&&s.aiPreparedMark!==mark)||
        (s.freeBallAvailable&&s.freeBallNominee==null&&!s.freeBallDeclined)||
        (currentTouching(s).requiresColourDeclaration&&s.nominationSource!=='manual');
      if(needs){beginDecision(s,'turn');s.turnManager.run();return true;}return false;
    };
    API.ai={setEnabled:enabled=>enableLocalAI(s,enabled),decide:options=>s.getLocalAI().decide(options),
      cancel:()=>{s.afterAnnotation=null;s.turnManager.cancel();s.opponent?.reset();localAI?.cancel();},
      getStatus:()=>({...(localAI?.getStatus()||{busy:false,phase:'idle'}),turn:s.turnManager.getStatus(),settings:{...s.aiSettings},opponent:s.opponent?.getStatus()||{enabled:false}})};
    if(DEVELOPMENT)API.recording={getStatus:()=>s.recorder.getStatus(),setEnabled:v=>s.recorder.setEnabled(v),
      flush:()=>s.recorder.flush(),readPage:options=>s.recorder.readPage(options),exportJSONL:()=>s.recorder.exportJSONL(),download:()=>s.recorder.download(),mark:label=>markStroke(s,label)};
    s.getOpponent().setEnabled(false);
    patches.push(() => {API.arena?.cancel();endRecordFrame(s,'uninstalled');s.recorder?.dispose();
      for(const name of inputEvents)window.removeEventListener(name,interacting);
      s.turnManager.cancel();s.opponent?.reset();localAI?.dispose();search?.cancel();trial?.dispose();s.frameMonitor?.dispose();
      clearSceneHooks(s);releaseStrokeHistory(s);});
    if (require?.c?.[30]?.exports) wrap(require.c[30].exports, 'getFoulDescription', () => description);
    wrap(app, 'onCurrentControllerStateChanged', original => function (...args) { const r = original.apply(this, args); if (app._currentController !== g) s.celebration.clear(); render(s); return r; });
    wrap(g, '_activateSubControl', original => function (...args) {
      if(s.placement && args[0]!=='inHand'){
        finishPracticeEditor(s,args[0]==='gaming');
        if(args[0]==='gaming')return;
      }
      syncAimGuide(s);
      const r = original.apply(this,args); if (args[0] === 'replay') s.celebration.clear();
      if(s.practice==='custom')render(s);else requestRender(s);return r;
    });
    wrap(g,'_onModelResponse',original=>function(...args){
      if(s.placement){g._gView.syncBalls(sim.getBalls(),sim.evolution);g._gView.requireRender();return;}
      return original.apply(this,args);
    });
    wrap(g,'exit',original=>function(...args){API.arena?.cancel();endRecordFrame(s,'exited');s.turnManager.cancel();s.opponent?.reset();localAI?.dispose();search?.cancel();trial?.dispose();trial=null;search=null;
      if(s.placement)finishPracticeEditor(s,false);destroyPracticePanel(s);releaseStrokeHistory(s);clearSceneHooks(s);return original.apply(this,args);});
    wrap(g._fpc,'gotoState1',original=>function(...args){
      if(s.practice==='custom'){if(s.placement)finishPracticeEditor(s,true);s.practiceControlsHidden=true;render(s);}
      return original.apply(this,args);
    });
    wrap(g._fpc,'gotoState0',original=>function(...args){
      const r=original.apply(this,args);
      if(s.practice==='custom'&&m._gState===4&&!s.shot&&!s.placement){s.practiceControlsHidden=false;render(s);}
      return r;
    });
    const hand=g._subControl.inHand;
    wrap(hand,'_showTip',original=>function(...args){if(s.placement){this._tipPopped=true;return;}return original.apply(this,args);});
    wrap(hand,'_onActvate',original=>function(...args){const r=original.apply(this,args);if(s.placement)this._firstLookToSet=true;return r;});
    wrap(m,'isValidInHandPositionUnderRay',original=>function(origin,direction,simulator,spot){
      if(!s.placement)return original.call(this,origin,direction,simulator,spot);
      if(!this._locRef.intersectionRayValidRegionPlane(origin,direction,spot))return false;
      spot.y=simulator.spotY;
      const bs=balls(s.g),b=bs.find(b=>b.i===s.placement.selectedIndex);
      return !PCOLPractice.placementError(bs,{...b,x:spot.x,z:spot.z},s.placement.bounds);
    });
    wrap(m,'reqRespotCueball',original=>function(position,simulator){
      return s.placement?placeSelectedBall(s,position):original.call(this,position,simulator);
    });
    wrap(g,'updateActing',original=>function(...args){
      s.frameMonitor?.tick(performance.now());
      s.ensureAITurn();
      const r=original.apply(this,args);
      // Wait until the stock first-play controls dialog has been closed.
      if(s.openEditorOnReady && practiceReady(s)){s.openEditorOnReady=false;ensurePracticePanel(s);render(s);}
      return r;
    });
    const home=app._controllers.home;
    if (home) wrap(home,'_confirmMenuClick',original=>function(...args){
      if(this._homeMainMenu.clickedIndex===1)return choosePractice(s);
      if(this._homeMainMenu.clickedIndex===0){s.requestedEnhanced=false;s.getOpponent().setEnabled(false);}
      return original.apply(this,args);
    });
    wrap(m, 'asyncLaunch', original => function (ready) {
      endRecordFrame(s,'restarted');
      clearSceneHooks(s);releaseStrokeHistory(s);
      localAI?.clearPlan();localAI?.resetExperience();s.aiConcessionMark=null;
      s.hotseat = s.requestedHotseat;
      s.requestedHotseat = false;
      s.getOpponent().setEnabled(s.requestedEnhanced);s.requestedEnhanced=false;
      destroyPracticePanel(s);s.practiceControlsHidden=false;
      s.practiceBefore=null;s.practiceLayout=null;s.openEditorOnReady=false;
      return original.call(this, payload => {
        if (s.hotseat) {
          const first = this._players[0], Player = first.constructor;
          const info = { ...first._userInfo };
          // Copy profile data: changing these frame labels must not rename the saved user.
          first._userInfo = { ...info, displayName: 'Player 1' };
          this._players.push(new Player({ ...info, userId: 'pcol-local-player-2', displayName: 'Player 2' }, Player.PLAYER_TYPE_USER));
        }
        s.practice=this._players.length===1?(s.requestedPractice||'standard'):null;
        s.requestedPractice=null;s.openEditorOnReady=s.practice==='custom';
        hookColourRespots(s);
        for(const c of g._playerCtls)hookAI(s,c._ai);
        ready(payload);
        beginRecordFrame(s);
      });
    });
    wrap(g, '_showResult', original => function (...args) {
      endRecordFrame(s,'finished');
      if(s.practice){
        const choices=[];
        if(canRetryPractice(s))choices.push(['复位重打最后一杆',()=>retryPractice(s),true]);
        choices.push(['重新练习',()=>{closeModal(s);m.reqReset(sim);}]);
        dialog(s,'练习完成',`本次得分 ${m._players[0].pts}，最高单杆 ${m._players[0].maxbrk}。`,choices);
        return;
      }
      const r = original.apply(this, args);
      if (s.hotseat) {
        const pts = scores(m), winner = s.frameEnd?.winner ?? s.conceded?.winnerIndex ?? (pts[0] === pts[1] ? null : pts[0] > pts[1] ? 0 : 1);
        const box = this._uiLayer._registeredBox.duoResultBox;
        box.head(winner == null ? 'DRAW' : `PLAYER ${winner + 1} WINS`);
        box._head.className = `box-head ${winner == null ? 'bright-copy' : 'success-copy'}`;
      }
      return r;
    });
    wrap(m, 'getLocalAIInstance', original => function (...args) { return hookAI(s, original.apply(this, args)); });
    for (const c of g._playerCtls) hookAI(s, c._ai);
    wrap(m, 'getContext', original => function (key) {
      if (key === 'ballOn' && this._gState === 4 && !s.pending) {
        if (s.freeBallNominee != null) return 2 ** sim.getBallAtIndex(s.freeBallNominee).number;
        if (this._gContext.ballOn === 252 && s.nominatedColour) return 2 ** s.nominatedColour;
      }
      return original.call(this, key);
    });
    wrap(m, 'reportPlayerStroke', original => function (player) {
      if (s.modal || s.placement || s.pending || s.conceded || !this._gContext.ballOn || this._gState !== 4 || this._gContext.playerIndex !== player) return false;
      const controller = g._playerCtls.find(c => c.gPlayerIndex === player);
      if (player === g._fpc.gPlayerIndex) {
        if (s.freeBallReview || (s.freeBallAvailable && s.freeBallNominee == null && !s.freeBallDeclined)) { chooseBall(s); return false; }
        if (currentTouching(s).requiresColourDeclaration && s.nominationSource !== 'manual') { s.nominatedColour=null; s.nominationSource=null; chooseBall(s,'touching'); return false; }
        if (this._gContext.ballOn === 252 && !s.nominatedColour) {
          const inferred = PCOLCore.inferColour(balls(g),controller?.getKissDir?.());
          if (inferred.colour == null) { chooseBall(s,true); return false; }
          s.nominatedColour = inferred.colour; s.nominationSource = 'auto';
        }
      } else {
        if(s.opponent?.getStatus().enabled && !s.opponent.verifyStroke(controller))return false;
        aiColour(s, controller);
      }
      const before = takeSnapshot(s);
      const accepted = original.call(this, player);
      if (accepted) { s.celebration.clear(); s.concessionTurn = null; s.shot = { before, trace: PCOLShotTrace.create(sim.getBalls(),{cap:15001}), contacts: [], physical: false, localAI:player!==g._fpc.gPlayerIndex&&!s.hotseat&&!!s.opponent?.getStatus().enabled, touchWatches:new Map(before.touching.indices.map(i=>[i,{initial:true}])), pushedTouching:[] };
        if(DEVELOPMENT){recordTurn(s);s.shot.recordStarted=performance.now();
          s.shot.recordController=player===g._fpc.gPlayerIndex||s.hotseat?'human':s.opponent?.getStatus().enabled?s.aiSettings.engine:'original';
          s.shot.recordId=recordEvent(s,'stroke.start',{
          actor:player,controller:s.shot.recordController,
          before:{balls:before.balls,rules:before.context,scores:before.scores},stroke:Array.from(controller.getStrokeVars())});}
        render(s); }
      return accepted;
    });
    wrap(sim, 'stroke', original => function (...args) {
      const r = original.apply(this, args);
      if (!s.predicting && s.shot) {
        s.shot.physical = true;
        const cue=this.getBallAtIndex(0);
        for (const [i,watch] of s.shot.touchWatches) {
          const obj=this.getBallAtIndex(i),dx=obj.position.x-cue.position.x,dy=obj.position.y-cue.position.y,dz=obj.position.z-cue.position.z;
          const distance=Math.hypot(dx,dy,dz);
          if (distance && (cue.v.x*dx+cue.v.y*dy+cue.v.z*dz)/distance < -1e-6) watch.initial=false;
        }
        sample(s);
      }
      return r;
    });
    // Existing resting contacts bypass presolve. Actual solver impulses detect
    // both first physical hits and directly pushing an initially touching ball.
    wrap(world.solver,'solveContact',original=>function (contact) {
      if(!s.shot||s.predicting)return original.call(this,contact);
      // The native engine emits one instantaneous tip impulse. Count actual
      // additional impulses, never infer a second strike from ball proximity.
      if(s.shot&&!s.predicting&&contact===world.tipContact&&contact.getCloseSpeed() < -1e-6)s.shot.cueStrikes=(s.shot.cueStrikes||0)+1;
      const recording=s.shot.physical && (contact.bi.number===0 || contact.isSS&&(contact.bj.number===0||s.shot.touchWatches.size>0));
      if(!recording)return original.call(this,contact);
      const i=contact.bi.v,j=contact.isSS?contact.bj.v:null;
      const ix=i.x,iy=i.y,iz=i.z,jx=j?.x,jy=j?.y,jz=j?.z,closeSpeed=contact.getCloseSpeed();
      const r=original.call(this,contact);
      recordSolvedContact(s,contact,ix,iy,iz,jx,jy,jz,closeSpeed);
      return r;
    });
    wrap(world, 'predict', original => function (...args) { s.predicting++; try { return original.apply(this, args); } finally { s.predicting--; } });
    wrap(world, 'internalStep', original => function (...args) { const r = original.apply(this, args); if(s.shot?.physical&&!s.predicting)sample(s); return r; });
    // Initial scene loading replaces internalStep with __internalStep__.
    // Hook that source too, so document-start installation records real steps.
    wrap(world, '__internalStep__', original => function (...args) { const r = original.apply(this, args); if(s.shot?.physical&&!s.predicting)sample(s); return r; });
    wrap(m, '_locRoundResultResponse', original => function (...args) {
      if (s.practice==='custom' && s.shot) return finishFreePractice(s);
      if (this._gContext.ballOn === 65535 || !s.shot) return original.apply(this, args);
      return finishStroke(s);
    });
    wrap(m, '_onResetResponse', original => function (...args) {
      endRecordFrame(s,'restarted');
      s.opponent?.reset();localAI?.cancel();localAI?.clearPlan();localAI?.resetExperience();
      if(s.placement)finishPracticeEditor(s,false);
      s.practiceControlsHidden=false;
      s.celebration.clear();
      releaseStrokeHistory(s);s.aiConcessionMark=null;
      s.pending = null; s.shot = null; s.conceded = null;s.frameEnd=null; s.concessionTurn = null; s.blackDecider=null; resetTurn(s); if (s.modal) closeModal(s);
      const response=original.apply(this, args);beginRecordFrame(s);return response;
    });
    // Keep the small status chip in sync after cue-ball placement and game lifecycle changes.
    wrap(m, '_response', original => function (...args) {
      if(args[1]==='restart' && s.practice==='custom'){
        const layout=s.practiceLayout||editableBalls(s).map(b=>({...b,active:b.n===0}));
        placePracticeLayout(s,layout);
        this._gContext.ballOn=65535;this._gContext.inHand=1;
      }
      syncHotseat(s); const r = original.apply(this, args);
      if(s.practice==='custom')render(s);else requestRender(s);return r;
    });
    mount(s);
    return s;
  }
  const API = window.PCOLPatch = {
    version: VERSION, core: PCOLCore, attach,
    getStatus: () => active ? { attached: true, version: VERSION, mode: active.hotseat ? 'hotseat' : active.g._model._players.length > 1 ? 'ai' : 'practice', practice:active.practice, canRetryPractice:canRetryPractice(active), context: { ...active.g._model._gContext }, score: scores(active.g._model), pending: active.pending && { offender: active.pending.offender, miss: active.pending.miss, reviewMiss: active.pending.reviewMiss }, freeBallAvailable: active.freeBallAvailable, freeBallReview: active.freeBallReview, freeBallAssessment: active.freeBallAssessment, nominatedColour: active.nominatedColour, nominationSource: active.nominationSource, freeBallNominee: active.freeBallNominee, touching:currentTouching(active), concession: concessionInfo(active), conceded: active.conceded, frameEnd: active.frameEnd || null, lastResult: active.lastResult, traceSamples: active.lastTrace.length, log: clone(active.log) } : { attached: false, version: VERSION },
    startHotseat: () => active && startHotseat(active),
    startPractice: mode => active && startPractice(active,mode),
    editPractice: () => active && openPracticeEditor(active),
    retryPractice: () => active && retryPractice(active),
    chooseBall: () => active && chooseBall(active),
    resolveFoul: action => active && resolveFoul(active, action),
    concede: () => active && concedeFrame(active),
    uninstall: () => { if(active?.placement)finishPracticeEditor(active,false);if(active)destroyPracticePanel(active);if (active?.modal) closeModal(active); active?.celebration.destroy(); active?.host?.remove(); for (const undo of patches.reverse()) undo(); active = null; delete window.PCOLPatch; }
  };
  function instrument(chunk) {
    const modules = chunk?.[1], original = modules?.[10];
    if (typeof original !== 'function' || original.__pcolRuleHook) return;
    const factory = function (module, exports, require) {
      const result = original.apply(this, arguments), App = exports.default;
      if (App?.prototype?.launch && !App.prototype.launch.__pcolRuleHook) {
        const launch = App.prototype.launch;
        const hooked = function (...args) { try { attach(this, require); } catch (e) { console.error('[PCOL rules patch]', e); } return launch.apply(this, args); };
        hooked.__pcolRuleHook = true; App.prototype.launch = hooked;
        patches.push(() => { if (App.prototype.launch === hooked) App.prototype.launch = launch; });
      }
      return result;
    };
    factory.__pcolRuleHook = true;
    factory.__pcolNativeSource = original.toString();
    modules[10] = factory;
    patches.push(() => { if (modules[10] === factory) modules[10] = original; });
  }
  const queue = window.webpackJsonp = window.webpackJsonp || [];
  queue.forEach(instrument);
  let downstream = queue.push;
  const descriptor = Object.getOwnPropertyDescriptor(queue, 'push');
  Object.defineProperty(queue, 'push', {
    configurable: true,
    get() {
      // Capture each downstream value: webpack keeps a reference to the old push.
      const next = downstream;
      return function (...chunks) { chunks.forEach(instrument); return next.apply(this, chunks); };
    },
    set(value) { downstream = value; }
  });
  patches.push(() => { if (descriptor) Object.defineProperty(queue, 'push', { ...descriptor, value: downstream }); else { delete queue.push; queue.push = downstream; } });
})();

})();
