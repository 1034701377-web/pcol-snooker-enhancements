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
  return Object.freeze({RADIUS,RED,COLOUR_ALL,FOUL,TOUCH_EPS,ballOnNumbers,touchingStatus,remainingPoints,concessionStatus,isSnookered,hasDirectHit,inferColour,evaluateJump,adjudicate});
})();
module.exports = PCOLCore;
