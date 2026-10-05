// ==UserScript==
// @name         PCOL Snooker Rules Patch
// @namespace    local.pcol.rules
// @version      0.2.6
// @description  Snooker rules, century celebrations, custom practice layouts and stroke retry.
// @match        http://www.heyzxz.me/pcol/*
// @match        https://www.heyzxz.me/pcol/*
// @run-at       document-start
// @grant        none
// @noframes
// @updateURL    https://raw.githubusercontent.com/1034701377-web/pcol-snooker-enhancements/main/outputs/pcol-rules-patch.user.js
// @downloadURL  https://raw.githubusercontent.com/1034701377-web/pcol-snooker-enhancements/main/outputs/pcol-rules-patch.user.js
// ==/UserScript==
(() => {
/* PCOL rule helpers. x/z are cloth coordinates; y is height. No game mutation.
 * WPBSA 2024-25: definitions 17/20, play 3/7/8/11/12.
 * https://wpbsa.com/wp-content/uploads/2198_WPBSA-Rulebook-2024-25.pdf
 */
const PCOLCore = (() => {
  'use strict';
  const RADIUS = 0.02625;
  const RED = 2, COLOUR_ALL = 252;
  const FOUL = Object.freeze({MISS:1, FIRST_HIT:2, POTTING:4, CUE_POTTED:8, OFF_TABLE:16, JUMP:32, FREE_BALL_SNOOKER:64, PUSH:128});
  // This engine admits resting sphere contacts within ~0.01 mm of tangency.
  // Do not classify visibly near balls as touching merely to ease a shot.
  const TOUCH_EPS = 1e-5;
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
      const rr=radius(pink)+radius(b)+2*TOUCH_EPS;
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
  function concessionStatus({balls, ballOn, scores, playerIndex, freeBall = false, threshold = 20}) {
    const maximum = remainingPoints(balls,ballOn,{freeBall});
    const valid = scores.length === 2 && (playerIndex === 0 || playerIndex === 1) && ballOn > 0 && ballOn !== 65535;
    const deficit = valid ? scores[1-playerIndex]-scores[playerIndex] : 0;
    const excess = deficit-maximum;
    return {eligible:valid && excess >= threshold,playerIndex,remaining:maximum,deficit,excess,threshold};
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
  function sampleBall(sample, b) { return sample.balls ? sample.balls.find(v => v.i === b.i) || {...b,active:false} : b; }
  function ballAt(trace, b, t) {
    let j = 0;
    while (j + 1 < trace.length && trace[j + 1].t < t) j++;
    if (j + 1 === trace.length) return sampleBall(trace[j], b);
    const a = trace[j], next = trace[j+1];
    const u = Math.max(0, Math.min(1, (t-a.t) / (next.t-a.t || 1)));
    return lerp(sampleBall(a,b),sampleBall(next,b),u);
  }

  // Relative swept-disc overlap, retaining only points with the cue above
  // the object's surface. Merely lifting the cue/using masse is not a foul.
  function sweptOver(a, b, objectA, objectB, rr, eps) {
    const p = {x:a.x-objectA.x,y:a.y-objectA.y,z:a.z-objectA.z};
    const v = {x:b.x-objectB.x-p.x,y:b.y-objectB.y-p.y,z:b.z-objectB.z-p.z};
    const A = v.x*v.x+v.z*v.z, B = 2*(p.x*v.x+p.z*v.z), C = p.x*p.x+p.z*p.z-(rr-eps)*(rr-eps);
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
    const us = [near,(lo+hi)/2,lo+(hi-lo)*1e-4,hi-(hi-lo)*1e-4];
    for (const u of us) {
      const q = {x:p.x+u*v.x,y:p.y+u*v.y,z:p.z+u*v.z};
      const horizontal2 = q.x*q.x+q.z*q.z;
      if (q.y > eps && horizontal2 < (rr-eps)*(rr-eps) && horizontal2+q.y*q.y >= (rr-eps)*(rr-eps)) return {u,position:lerp(a,b,u)};
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
    const cue = ballsAtStart.find(b => b.n === 0) || {r:fallbackRadius,...trace[0]};
    const rc = radius(cue,fallbackRadius), eps = Math.max(1e-6,rc*0.002);
    const groundY = cue.y;
    const events = contactEvents.slice().sort((a,b) => a.t-b.t);
    const objects = ballsAtStart.filter(b => b.n > 0 && active(b));
    const touching = new Set(objects.filter(b => Math.hypot(cue.x-b.x,cue.y-b.y,cue.z-b.z) <= rc+radius(b,fallbackRadius)+eps).map(b => b.i));
    const contacts = events.filter(e => e.ballIndex != null && objects.some(b => b.i === e.ballIndex));
    const first = contacts[0];
    const offendingBalls = [], details = [];
    let indeterminate = false;
    for (const object of objects) {
      const passages=[];
      let wasOver=false;
      for (let k=0;k<trace.length-1;k++) {
        const a=trace[k],b=trace[k+1],oa=sampleBall(a,object),ob=sampleBall(b,object);
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
      while(start>0 && trace[start].y>groundY+eps) start--;
      let land=passage.k+1;
      while(land<trace.length && trace[land].y>groundY+eps) land++;
      const hitDuringFlight = contacts.find(e => e.ballIndex===object.i && e.t>=trace[start].t && (land===trace.length || e.t<=trace[land].t));
      if (hitDuringFlight && !touching.has(object.i)) {
        if (land===trace.length) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball; landing not yet recorded.'});continue;}
        if(!trace[land].balls) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Contacted ball current position at landing is unavailable.'});continue;}
        const objectAtLanding=ballAt(trace,object,trace[land].t);
        const approach=ballAt(trace,object,passage.t);
        const vx=approach.x-trace[start].x,vz=approach.z-trace[start].z;
        const length=Math.hypot(vx,vz);
        const far=length ? ((trace[land].x-objectAtLanding.x)*vx+(trace[land].z-objectAtLanding.z)*vz)/length : 0;
        if (far <= eps) {details.push({...detail,exception:'20(b): hit airborne, landed on near side of the ball current position.'});continue;}
        if (far < rc+radius(object,fallbackRadius)+eps) {indeterminate=true;details.push({...detail,indeterminate:true,reason:'Landing close to dividing plane; manual decision required.'});continue;}
      }
      offendingBalls.push(object.i);
      details.push({...detail,foul:true,reason:'Cue passed above an object ball without a recorded exception.'});
      }
    }
    return {foul:offendingBalls.length>0,offendingBalls:unique(offendingBalls),reason:offendingBalls.length?'Illegal jump over an object ball.':indeterminate?'Some airborne contact needs review.':'No illegal jump found.',indeterminate,details};
  }

  /** Indices identify firstHits (simultaneous), potted, outOfBounds and nominee.
   * nominatedColour is a number 2..7. balls contains final positions and all
   * objects including inactive entries. Removed indices are also excluded when
   * callers supply pre-stroke active flags. Colours to respot are indices.
   * This pure function does not decide discretionary Foul and a Miss, restore
   * positions, choose colour spot geometry, or decide a tied-frame re-spot.
   */
  function adjudicate({ballOn,nominatedColour=null,freeBallNominee=null,balls,firstHits=[],potted=[],outOfBounds=[],jumpFoul=false,touchingAtStart=[],pushedTouching=[]}) {
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
    return {score,foulCode,nextBallOn,respots,requiresInHand,ballOnUsed:on,penalty:foulCode?penalty:0,freeBallNominee:validNominee?nominee.i:null,reasons,freeBallSafety,canonicalPotted,continueBreak:score>0,touching:{indices:touching.map(b=>b.i),deemedHit,pushedIndices:unique(pushedTouching)}};
  }
  return Object.freeze({RADIUS,RED,COLOUR_ALL,FOUL,TOUCH_EPS,ballOnNumbers,pinkRespotX,touchingStatus,remainingPoints,concessionStatus,isSnookered,hasDirectHit,inferColour,evaluateJump,adjudicate});
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

(() => {
  'use strict';
  const VERSION = "0.2.6";
  if (window.PCOLPatch?.version === VERSION) return;
  const COLOURS = ['白球', '红球', '黄球', '绿球', '棕球', '蓝球', '粉球', '黑球'];
  const FOULS = [[1, '未先碰到目标球'], [2, '先碰错球'], [4, '非法进球'], [8, '白球落袋'], [16, '球离开球台'], [32, '非法跳球'], [64, '利用自由球形成违规斯诺克'], [128, '出杆推动了相贴球（推杆）']];
  const patches = [];
  let active = null;
  const clone = x => JSON.parse(JSON.stringify(x));
  const description = code => FOULS.filter(([bit]) => code & bit).map(([, text]) => text).join('；');
  function wrap(object, key, make) {
    const own = Object.prototype.hasOwnProperty.call(object, key);
    const original = object[key];
    const replacement = make(original);
    object[key] = replacement;
    patches.push(() => { if (object[key] === replacement) { if (own) object[key] = original; else delete object[key]; } });
  }
  function balls(g) {
    return g._simulator.getBalls().map(b => ({ i: b.index, n: b.number, active: b.active, x: b.position.x, y: b.position.y, z: b.position.z, r: b.radius }));
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
        const ground=sim.ground,margin=sim.ballRadius+2*PCOLCore.TOUCH_EPS;
        const minX=ground.centerPosition.x-ground.size.x/2+margin,maxX=ground.centerPosition.x+ground.size.x/2-margin;
        const bs=sim.getBalls().map(b=>({i:b.index,active:b.active,x:b.position.x,y:b.position.y,z:b.position.z,r:b.radius}));
        const x=PCOLCore.pinkRespotX(bs,{i:b.index,...b.spot,r:b.radius},minX,maxX);
        if(x===null)throw new Error('No legal pink-ball respot position');
        sim.resetBallXYZ(b,x,b.spot.y,b.spot.z);
      }
    });
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
    if (s.conceded) return '本局已认输';
    if (s.pending) return `犯规 ${-s.pending.result.score} 分 · 等待选择`;
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
    window.addEventListener('resize',resize);
    patches.push(() => window.removeEventListener('resize',resize));
  }
  function mount(s) {
    if (s.host) return;
    const host = document.createElement('div');
    host.id = 'pcol-rules-patch';
    host.style.cssText = 'position:fixed;left:16px;bottom:14px;z-index:2147483000;font:13px/1.5 "Microsoft YaHei",sans-serif;color:#fff;';
    const shadow = host.attachShadow({ mode: 'open' });
    shadow.innerHTML = `<style>
      *{box-sizing:border-box}button{font:inherit;cursor:pointer;border:1px solid #ab8544;border-radius:5px;background:#28241b;color:#fff;padding:8px 12px}button:hover{background:#65512e}button:focus-visible{outline:2px solid #f5c368;outline-offset:2px}button.primary{background:#aa782d;color:#fff}button:disabled{opacity:.45;cursor:default}.bar{display:flex;gap:9px;align-items:center;padding:7px 10px;background:#171610e8;border:1px solid #88734c;border-radius:6px}.bar button{padding:3px 7px}.veil{position:fixed;inset:0;display:grid;place-items:center;background:#0009}.panel{width:min(540px,calc(100vw - 32px));max-height:85vh;overflow:auto;background:#171914;border:1px solid #b69758;border-radius:10px;padding:24px;box-shadow:0 18px 60px #0008}.panel h2{font-size:21px;margin:0 0 12px}.panel p{margin:9px 0 18px;color:#dedbcd}.choices{display:flex;gap:9px;flex-wrap:wrap}.note{font-size:12px;color:#b8baa9;margin-top:14px}
      [hidden]{display:none!important}.bar{max-width:calc(100vw - 16px);flex-wrap:wrap}.drag{cursor:grab;touch-action:none;user-select:none;padding:0 4px;color:#e7c986;font-size:18px}.drag:active{cursor:grabbing}
      .bar[data-practice="true"] .status{cursor:grab;touch-action:none;user-select:none;font-weight:500}
    </style><div class="bar"><span class="drag" title="拖动浮窗；双击恢复位置">⠿</span><span class="status" title="拖动浮窗；双击恢复位置"></span><button type="button" class="hotseat" hidden>开始双人局</button><button type="button" class="practice" hidden>练球</button><button type="button" class="retry" hidden>复位重打</button><button type="button" class="choose">选球</button><button type="button" class="concede" hidden>认输本局</button></div><div class="practice-controls"></div><div class="modal"></div>`;
    document.documentElement.appendChild(host);
    s.host = host; s.shadow = shadow;
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
    s.shadow.querySelector('.status').textContent = home ? 'PCOL · 规则与练习' : custom ? '自由练习' : `${s.hotseat ? `人格分裂 · ${actor(s)}${s.pending ? '决定' : '击球'} · ` : s.practice === 'standard' ? '单人练习 · ' : ''}${touching?`${touching} · `:''}${statusLine(s)}`;
    const eligible = live && !s.pending && s.g._model._gState === 4 && s.g._model._gContext.playerIndex === s.g._fpc.gPlayerIndex && (s.freeBallAvailable || s.freeBallReview || s.g._model._gContext.ballOn === 252);
    s.shadow.querySelector('.choose').hidden = !eligible;
    s.shadow.querySelector('.concede').hidden = !(live && concessionInfo(s).available && s.g._model._gContext.playerIndex === s.g._fpc.gPlayerIndex && !s.modal);
    if(s.editor){s.editor.setVisible(controlsVisible);if(controlsVisible)s.editor.update(editableBalls(s),s.placement?.selectedIndex ?? null,Boolean(s.placement));}
    if ((live || home) && s.panelPosition && !s.shadow.querySelector('.bar').hidden) positionPanel(s,s.panelPosition.x,s.panelPosition.y);
  }
  function closeModal(s) {
    s.shadow?.querySelector('.modal').replaceChildren();
    if (s.modal) s.g._paused = s.pausedBeforeModal;
    s.modal = false;
    s.g._gView?.canvas?.focus();
    if (s.app._currentController === s.app._controllers.home) s.app._controllers.home._homeMainMenu?.activate();
    render(s);
  }
  function dialog(s, title, message, choices, note = '') {
    mount(s);
    if (!s.modal) s.pausedBeforeModal = s.g._paused;
    s.modal = true; s.g._paused = true;
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
  }
  function concessionInfo(s) {
    const m = s.g._model, ctx = m._gContext;
    const info = PCOLCore.concessionStatus({ balls: balls(s.g), ballOn: ctx.ballOn, scores: scores(m), playerIndex: ctx.playerIndex, freeBall: (s.freeBallAvailable || s.freeBallReview) && !s.freeBallDeclined });
    const turn = s.concessionTurn;
    return { ...info, available: info.eligible && m._gState === 4 && !s.shot && !s.pending && !s.conceded && turn?.round === ctx.nRounds && turn.playerIndex === ctx.playerIndex };
  }
  function concedeFrame(s) {
    const info = concessionInfo(s);
    if (!info.available) return false;
    const m = s.g._model, playerIndex = m._gContext.playerIndex;
    s.conceded = { playerIndex, winnerIndex: 1-playerIndex, round: m._gContext.nRounds, score: scores(m), remaining: info.remaining, excess: info.excess };
    s.log.push({ kind: 'concession', ...clone(s.conceded) });
    s.concessionTurn = null;
    closeModal(s);
    resetTurn(s);
    m._gContext.ballOn = 0;
    m._gContext.inHand = 0;
    syncResponse(s);
    return true;
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
        ['不判自由球', () => { s.freeBallReview = false; closeModal(s); }, true],
        ['裁判确认自由球', () => { s.freeBallReview = false; s.freeBallAvailable = true; s.log.push({ kind: 'referee-free-ball-confirmation' }); closeModal(s); chooseBall(s); }]
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
    s.lastTrace=shot.trace;s.lastContacts=shot.contacts;s.lastBefore=shot.before;s.lastResult=result;
    if (s.practice) s.practiceBefore=shot.before;
    if (s.practice==='custom') s.practiceControlsHidden=false;
    s.log.push({kind:'stroke',round:s.g._model._gContext.nRounds,offender:shot.before.context.playerIndex,result:clone(result),score:scores(s.g._model),traceSamples:shot.trace.length});
    if(s.log.length>100)s.log.shift();
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
    const bs = balls(s.g), q = bs[0], t = shot.trace.length;
    if (t > 15000) { shot.overflow = true; return null; }
    const row = { t, x: q.x, y: q.y, z: q.z, balls: bs };
    for (const [index,watch] of shot.touchWatches) {
      if (!watch.initial) continue;
      const b=bs.find(b=>b.i===index);
      if (!b?.active || Math.hypot(q.x-b.x,q.y-b.y,q.z-b.z)>q.r+b.r+PCOLCore.TOUCH_EPS*2) watch.initial=false;
    }
    shot.trace.push(row); return row;
  }
  function recordSolvedContact(s, contact, beforeVelocity, closeSpeed) {
    const shot=s.shot;
    if (!shot?.physical || s.predicting || !(closeSpeed < -1e-6)) return;
    const q=contact.bi.number===0?contact.bi:contact.isSS && contact.bj.number===0?contact.bj:null;
    if (!contact.isSS) {
      const normal=contact.normal || contact.bj.normal;
      if (!q || contact.bj.end || contact.bj.tunnel || !normal || Math.abs(normal.y)>=.7) return;
      const v=beforeVelocity.i;
      const gained=(q.v.x-v.x)*normal.x+(q.v.y-v.y)*normal.y+(q.v.z-v.z)*normal.z;
      if (!(gained>1e-7)) return;
      const row=sample(s); if (!row) return;
      shot.contacts.push({t:row.t,kind:'cushion',evolution:s.g._simulator._world.evolution,x:row.x,y:row.y,z:row.z});
      for (const item of shot.touchWatches.values()) item.initial=false;
      return;
    }
    if (!q) {
      // A later ball can move the originally touching object without making
      // the initial play-away a push stroke. Track the source of the motion.
      for (const [b,v] of [[contact.bi,beforeVelocity.i],[contact.bj,beforeVelocity.j]]) {
        if (Math.hypot(b.v.x-v.x,b.v.y-v.y,b.v.z-v.z)>1e-7) {
          const watch=shot.touchWatches.get(b.index); if (watch) watch.initial=false;
        }
      }
      return;
    }
    const obj=q===contact.bi?contact.bj:contact.bi, v=q===contact.bi?beforeVelocity.j:beforeVelocity.i;
    const direction={x:obj.position.x-q.position.x,y:obj.position.y-q.position.y,z:obj.position.z-q.position.z};
    const length=Math.hypot(direction.x,direction.y,direction.z);
    const gained=length?((obj.v.x-v.x)*direction.x+(obj.v.y-v.y)*direction.y+(obj.v.z-v.z)*direction.z)/length:0;
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
    wrap(ai, 'step', original => function (...args) {
      const result = original.apply(this, args);
      if (result) s.aiTarget = Number.isInteger(result.ballBIndex) ? result.ballBIndex : null;
      return result;
    });
    return ai;
  }
  function resetTurn(s) { s.nominatedColour = null; s.nominationSource = null; s.freeBallNominee = null; s.freeBallAvailable = false; s.freeBallReview = false; s.freeBallDeclined = false; s.aiTarget = null; }
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
    syncResponse(s);
    offerConcession(s, pending.offender);
    return true;
  }
  function offerFoul(s) {
    const p = s.pending, m = s.g._model;
    if (m._gContext.playerIndex !== s.g._fpc.gPlayerIndex) {
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
    const result = PCOLCore.adjudicate({ ballOn: oldMask, nominatedColour: shot.before.nominatedColour, freeBallNominee: shot.before.freeBallNominee, balls: balls(g), firstHits, potted: [...sim.result.pottedIndices], outOfBounds: [...sim.result.outOfBoundsIndices], jumpFoul: jump.foul || jumpDecision === true, touchingAtStart:shot.before.touching.indices, pushedTouching:shot.pushedTouching });
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
    recordCompletedStroke(s,shot,{...result,jump,firstHits});
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
    render(s);
    return m;
  }
  function attach(app, require) {
    if (active?.app === app) return active;
    if (active) throw new Error('A different PCOL instance is already attached');
    if (app.constructor.VERSION !== '0.1.0.03152018') throw new Error('Unsupported PCOL build');
    const g = app._controllers.game, m = g._model, sim = g._simulator, world = sim._world;
    if (!m.reportPlayerStroke || !world.serialize || !world.restore || !world.internalStep) throw new Error('PCOL structure changed');
    const s = active = { app, g, hotseat: false, requestedHotseat: false, shot: null, predicting: 0, nominatedColour: null, freeBallNominee: null, freeBallAvailable: false, freeBallDeclined: false, pending: null, modal: false, conceded: null, concessionTurn: null, aiHooks: new WeakSet(), log: [], lastTrace: [], lastContacts: [] };
    s.celebration = PCOLCelebration.create({ document, window, host: document.documentElement });
    s.practice=null;s.requestedPractice=null;s.practiceBefore=null;s.practiceLayout=null;s.openEditorOnReady=false;s.placement=null;s.practiceControlsHidden=false;s.refHooks=new WeakSet();
    hookColourRespots(s);
    API.app = app;
    if (require?.c?.[30]?.exports) wrap(require.c[30].exports, 'getFoulDescription', () => description);
    wrap(app, 'onCurrentControllerStateChanged', original => function (...args) { const r = original.apply(this, args); if (app._currentController !== g) s.celebration.clear(); render(s); return r; });
    wrap(g, '_activateSubControl', original => function (...args) {
      if(s.placement && args[0]!=='inHand'){
        finishPracticeEditor(s,args[0]==='gaming');
        if(args[0]==='gaming')return;
      }
      const r = original.apply(this,args); if (args[0] === 'replay') s.celebration.clear(); render(s); return r;
    });
    wrap(g,'_onModelResponse',original=>function(...args){
      if(s.placement){g._gView.syncBalls(sim.getBalls(),sim.evolution);g._gView.requireRender();return;}
      return original.apply(this,args);
    });
    wrap(g,'exit',original=>function(...args){if(s.placement)finishPracticeEditor(s,false);destroyPracticePanel(s);return original.apply(this,args);});
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
      const r=original.apply(this,args);
      // Wait until the stock first-play controls dialog has been closed.
      if(s.openEditorOnReady && practiceReady(s)){s.openEditorOnReady=false;ensurePracticePanel(s);render(s);}
      return r;
    });
    const home=app._controllers.home;
    if (home) wrap(home,'_confirmMenuClick',original=>function(...args){
      if(this._homeMainMenu.clickedIndex===1)return choosePractice(s);
      return original.apply(this,args);
    });
    wrap(m, 'asyncLaunch', original => function (ready) {
      s.hotseat = s.requestedHotseat;
      s.requestedHotseat = false;
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
        ready(payload);
      });
    });
    wrap(g, '_showResult', original => function (...args) {
      if(s.practice){
        const choices=[];
        if(canRetryPractice(s))choices.push(['复位重打最后一杆',()=>retryPractice(s),true]);
        choices.push(['重新练习',()=>{closeModal(s);m.reqReset(sim);}]);
        dialog(s,'练习完成',`本次得分 ${m._players[0].pts}，最高单杆 ${m._players[0].maxbrk}。`,choices);
        return;
      }
      const r = original.apply(this, args);
      if (s.hotseat) {
        const pts = scores(m), winner = s.conceded?.winnerIndex ?? (pts[0] === pts[1] ? null : pts[0] > pts[1] ? 0 : 1);
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
      } else aiColour(s, controller);
      const before = takeSnapshot(s);
      const accepted = original.call(this, player);
      if (accepted) { s.celebration.clear(); s.concessionTurn = null; s.shot = { before, trace: [], contacts: [], physical: false, touchWatches:new Map(before.touching.indices.map(i=>[i,{initial:true}])), pushedTouching:[] }; render(s); }
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
      const recording=s.shot?.physical && !s.predicting && (contact.isSS || contact.bi.number===0);
      const velocity=b=>({x:b.v.x,y:b.v.y,z:b.v.z});
      const beforeVelocity=recording?{i:velocity(contact.bi),j:contact.isSS?velocity(contact.bj):null}:null;
      const closeSpeed=recording?contact.getCloseSpeed():0;
      const r=original.call(this,contact);
      if (recording) recordSolvedContact(s,contact,beforeVelocity,closeSpeed);
      return r;
    });
    wrap(world, 'predict', original => function (...args) { s.predicting++; try { return original.apply(this, args); } finally { s.predicting--; } });
    wrap(world, 'internalStep', original => function (...args) { const r = original.apply(this, args); sample(s); return r; });
    // Initial scene loading replaces internalStep with __internalStep__.
    // Hook that source too, so document-start installation records real steps.
    wrap(world, '__internalStep__', original => function (...args) { const r = original.apply(this, args); sample(s); return r; });
    wrap(m, '_locRoundResultResponse', original => function (...args) {
      if (s.practice==='custom' && s.shot) return finishFreePractice(s);
      if (this._gContext.ballOn === 65535 || !s.shot) return original.apply(this, args);
      return finishStroke(s);
    });
    wrap(m, '_onResetResponse', original => function (...args) {
      if(s.placement)finishPracticeEditor(s,false);
      s.practiceControlsHidden=false;
      s.celebration.clear();
      s.practiceBefore=null;s.lastResult=null;s.lastBefore=null;
      s.pending = null; s.shot = null; s.conceded = null; s.concessionTurn = null; resetTurn(s); if (s.modal) closeModal(s);
      return original.apply(this, args);
    });
    // Keep the small status chip in sync after cue-ball placement and game lifecycle changes.
    wrap(m, '_response', original => function (...args) {
      if(args[1]==='restart' && s.practice==='custom'){
        const layout=s.practiceLayout||editableBalls(s).map(b=>({...b,active:b.n===0}));
        placePracticeLayout(s,layout);
        this._gContext.ballOn=65535;this._gContext.inHand=1;
      }
      syncHotseat(s); const r = original.apply(this, args); render(s); return r;
    });
    mount(s);
    return s;
  }
  const API = window.PCOLPatch = {
    version: VERSION, core: PCOLCore, attach,
    getStatus: () => active ? { attached: true, version: VERSION, mode: active.hotseat ? 'hotseat' : active.g._model._players.length > 1 ? 'ai' : 'practice', practice:active.practice, canRetryPractice:canRetryPractice(active), context: { ...active.g._model._gContext }, score: scores(active.g._model), pending: active.pending && { offender: active.pending.offender, miss: active.pending.miss, reviewMiss: active.pending.reviewMiss }, freeBallAvailable: active.freeBallAvailable, freeBallReview: active.freeBallReview, freeBallAssessment: active.freeBallAssessment, nominatedColour: active.nominatedColour, nominationSource: active.nominationSource, freeBallNominee: active.freeBallNominee, touching:currentTouching(active), concession: concessionInfo(active), conceded: active.conceded, lastResult: active.lastResult, traceSamples: active.lastTrace.length, log: clone(active.log) } : { attached: false, version: VERSION },
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
