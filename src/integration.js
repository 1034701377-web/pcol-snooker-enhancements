(() => {
  'use strict';
  const VERSION = __PCOL_VERSION__;
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
    if (s.practice === 'custom') return `自由练习 · 台上 ${balls(s.g).filter(b => b.active && b.n > 0).length} 颗目标球${s.lastResult?.pottedCount != null ? ` · 本杆进 ${s.lastResult.pottedCount} 球` : ''}`;
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
    const handle = s.shadow.querySelector('.drag');
    let drag = null;
    try {
      const stored = JSON.parse(window.localStorage.getItem(PANEL_POSITION_KEY));
      if (Number.isFinite(stored?.x) && Number.isFinite(stored?.y)) s.panelPosition = stored;
    } catch (_) { /* Storage can be disabled; dragging still works this session. */ }
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
    </style><div class="bar"><span class="drag" title="拖动浮窗；双击恢复位置">⠿</span><span class="status"></span><button type="button" class="hotseat" hidden>开始双人局</button><button type="button" class="practice" hidden>练球</button><button type="button" class="edit" hidden>摆球</button><button type="button" class="retry" hidden>复位重打</button><button type="button" class="choose">选球</button><button type="button" class="concede" hidden>认输本局</button></div><div class="modal"></div>`;
    document.documentElement.appendChild(host);
    s.host = host; s.shadow = shadow;
    enablePanelDrag(s);
    shadow.querySelector('.hotseat').onclick = () => startHotseat(s);
    shadow.querySelector('.practice').onclick = () => choosePractice(s);
    shadow.querySelector('.edit').onclick = () => openPracticeEditor(s);
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
    s.host.style.display = live || home ? 'block' : 'none';
    s.shadow.querySelector('.bar').hidden = live && s.g._activeSubControl?.name === 'replay';
    s.shadow.querySelector('.hotseat').hidden = !home;
    s.shadow.querySelector('.practice').hidden = !home;
    s.shadow.querySelector('.edit').hidden = !(live && s.practice === 'custom');
    s.shadow.querySelector('.edit').disabled = !practiceReady(s) || s.modal || Boolean(s.placement);
    const retry = s.shadow.querySelector('.retry');
    retry.hidden = !(live && s.practice);
    retry.disabled = !canRetryPractice(s) || s.modal;
    retry.title = '恢复上一杆前的球位、分数和单杆分';
    const touching=live?touchingNotice(s):'';
    s.shadow.querySelector('.status').textContent = home ? 'PCOL · 规则与练习' : `${s.hotseat ? `人格分裂 · ${actor(s)}${s.pending ? '决定' : '击球'} · ` : s.practice === 'standard' ? '单人练习 · ' : ''}${touching?`${touching} · `:''}${statusLine(s)}`;
    const eligible = live && !s.pending && s.g._model._gState === 4 && s.g._model._gContext.playerIndex === s.g._fpc.gPlayerIndex && (s.freeBallAvailable || s.freeBallReview || s.g._model._gContext.ballOn === 252);
    s.shadow.querySelector('.choose').hidden = !eligible;
    s.shadow.querySelector('.concede').hidden = !(live && concessionInfo(s).available && s.g._model._gContext.playerIndex === s.g._fpc.gPlayerIndex && !s.modal);
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
    const sim = s.g._simulator, vertices = sim.ground.edges.map(e => e.va), sides = sim.sidePolyGroups.polys;
    // Use the inward-facing straight cushions, ignoring the back of the pockets.
    const minX = Math.max(Math.min(...vertices.map(p=>p.x)), ...sides.filter(p=>p.normal.x>.9999).map(p=>-p.d/p.normal.x));
    const maxX = Math.min(Math.max(...vertices.map(p=>p.x)), ...sides.filter(p=>p.normal.x<-.9999).map(p=>-p.d/p.normal.x));
    const minZ = Math.max(Math.min(...vertices.map(p=>p.z)), ...sides.filter(p=>p.normal.z>.9999).map(p=>-p.d/p.normal.z));
    const maxZ = Math.min(Math.max(...vertices.map(p=>p.z)), ...sides.filter(p=>p.normal.z<-.9999).map(p=>-p.d/p.normal.z));
    const d = s.g._model._locRef._dArea;
    return {minX,maxX,minZ,maxZ,baulkX:d._center.x,dRadius:d._radius,pockets:[minX,0,maxX].flatMap(x=>[minZ,maxZ].map(z=>({x,z,r:.075})))};
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
  function openPracticeEditor(s) {
    if (s.practice !== 'custom' || !practiceReady(s) || s.modal || s.placement) return false;
    s.celebration.clear();
    s.placement={before:takeSnapshot(s),bounds:practiceBounds(s),selectedIndex:0,changed:false};
    const changeLayout=layout=>{
      if(!practiceReady(s))return;
      placePracticeLayout(s,layout);s.placement.changed=true;syncResponse(s);refreshPlacement(s);
    };
    s.editor=PCOLPractice.createEditor({document,container:s.shadow.querySelector('.modal'),balls:editableBalls(s),
      onSelect:n=>selectPlacementBall(s,n),
      onSelectRed:i=>selectPlacementBall(s,1,i),
      onRemove:()=>{const layout=editableBalls(s),b=layout.find(b=>b.i===s.placement.selectedIndex);if(b.n===0)return;b.active=false;changeLayout(layout);},
      onClear:()=>changeLayout(editableBalls(s).map(b=>({...b,active:b.n===0}))),
      onStandard:()=>changeLayout(editableBalls(s).map(b=>({...b,...b.spot,active:true}))),
      onDone:()=>finishPracticeEditor(s,true),onCancel:()=>finishPracticeEditor(s,false)
    });
    const escape=e=>{if(e.key==='Escape'){e.preventDefault();e.stopImmediatePropagation();finishPracticeEditor(s,false);}};
    s.g._gView.canvas.addEventListener('keydown',escape,true);
    s.shadow.addEventListener('keydown',escape,true);
    s.placement.removeEvents=()=>{s.g._gView.canvas.removeEventListener('keydown',escape,true);s.shadow.removeEventListener('keydown',escape,true);};
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
    s.editor.update(editableBalls(s),b.index);
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
    edit.removeEvents();s.placement=null;s.editor.destroy();s.editor=null;
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
    if (breakBefore < 100 && m._players[offender].brk >= 100) s.celebration.show({ playerLabel: s.hotseat ? `玩家 ${offender + 1}` : m._players[offender].displayName, breakScore: m._players[offender].brk });
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
    s.practice=null;s.requestedPractice=null;s.practiceBefore=null;s.practiceLayout=null;s.openEditorOnReady=false;s.placement=null;
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
    wrap(g,'exit',original=>function(...args){if(s.placement)finishPracticeEditor(s,false);return original.apply(this,args);});
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
      if(s.openEditorOnReady && practiceReady(s)){s.openEditorOnReady=false;openPracticeEditor(s);}
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
    uninstall: () => { if(active?.placement)finishPracticeEditor(active,false);if (active?.modal) closeModal(active); active?.celebration.destroy(); active?.host?.remove(); for (const undo of patches.reverse()) undo(); active = null; delete window.PCOLPatch; }
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
